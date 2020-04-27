/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

use std::cell::BorrowError;
use std::cell::BorrowMutError;
use std::cell::Cell;
use std::cell::Ref;
use std::cell::RefCell;
use std::fmt::Debug;
use std::ops::Deref;
use std::rc::Rc;

/// A trait for a garbage collector
pub trait GarbageCollector: 'static + Sized {
    type Handle: GcHandle<Self>;
    fn gc(&mut self);
    fn root(&mut self, handle: &Self::Handle);
    fn mark(&mut self, handle: &Self::Handle);
}

/// Garbage collected objects store a handle to a traceable object
/// (the handle is called the reflector, and the traceable object is reflected).
pub trait GcHandle<GC: GarbageCollector>: Clone {
    fn new(tracer: Box<dyn Traceable<GC>>) -> Self;
}

/// The life cycle of a traceable object is that it is initialized,
/// then there are some (possibly none) GC runs in which it is traced,
/// then there are some (at least one) GC run in which it isn't traced,
/// then it is finalized.
///
/// A reflector `A` is *directly reachable* from a reflector `B`
/// if calling `trace(gc)` on B's reflected object calls `gc.mark(A)`.
///
/// A reflector `A` is *reachable* from a reflector `B`
/// if it is reflexivly transitively directly reachable.
///
/// An object will only be finalized when it is not reachable from a root.
pub trait Traceable<GC: GarbageCollector>: 'static {
    fn initialize(&self, reflector: &GC::Handle);
    fn trace(&self, gc: &mut GC);
    fn finalize(&self);
}

// TODO: implement traceable for more base types
impl<T: Traceable<GC>, GC: GarbageCollector> Traceable<GC> for Option<T> {
    fn initialize(&self, reflector: &GC::Handle) {
        if let Some(ref me) = self {
            me.initialize(reflector);
        }
    }
    fn trace(&self, gc: &mut GC) {
        if let Some(ref me) = self {
            me.trace(gc);
        }
    }
    fn finalize(&self) {
        if let Some(ref me) = self {
            me.finalize();
        }
    }
}

/// A reference-counted garbage collected object.
/// We maintain the invariant that if a `&GcRc<GC, T>` is live,
/// then its reflector is reachable from a root.
pub struct GcRc<GC: GarbageCollector, T>(Rc<GcRcData<GC, T>>);

struct GcRcData<GC: GarbageCollector, T> {
    reflector: RefCell<Option<GC::Handle>>,
    reflected: Rc<T>,
}

impl<GC: GarbageCollector, T> Deref for GcRc<GC, T> {
    type Target = T;
    fn deref(&self) -> &T {
        self.0.reflected.deref()
    }
}

impl<GC: GarbageCollector, T: Traceable<GC>> GcRc<GC, T> {
    // NOT pub!
    fn dangerous_new(value: T) -> GcRc<GC, T> {
        let reflected = GcRc(Rc::new(GcRcData {
            reflector: RefCell::new(None),
            reflected: Rc::new(value),
        }));
        GC::Handle::new(Box::new(reflected.dangerous_clone()));
        reflected
    }

    /// Create a rooted object
    pub fn rooted(gc: &mut GC, value: T) -> GcRc<GC, T> {
        let result = GcRc::dangerous_new(value);
        {
            let reflector = result.0.reflector.borrow();
            let reflector = reflector.as_ref().expect("GC while rooting?");
            gc.root(reflector);
        }
        result
    }
}

impl<GC: GarbageCollector, T> GcRc<GC, T> {
    // NOT pub!
    fn dangerous_clone(&self) -> GcRc<GC, T> {
        GcRc(self.0.clone())
    }
}

impl<GC: GarbageCollector, T: Traceable<GC>> Traceable<GC> for GcRc<GC, T> {
    fn initialize(&self, reflector: &GC::Handle) {
        debug_assert!(self.0.reflector.borrow().is_none());
        self.0.reflector.replace(Some(reflector.clone()));
        self.0.reflected.initialize(reflector);
    }
    fn trace(&self, gc: &mut GC) {
        debug_assert!(self.0.reflector.borrow().is_some());
        gc.mark(self.0.reflector.borrow().as_ref().unwrap());
        self.0.reflected.trace(gc);
    }
    fn finalize(&self) {
        debug_assert!(self.0.reflector.borrow().is_some());
        self.0.reflector.replace(None);
        self.0.reflected.finalize();
    }
}

/// A `RefCell` for garbage-collected objects.
pub struct GcRcCell<GC: GarbageCollector, T> {
    curr: RefCell<Option<GcRc<GC, T>>>,
    state: Cell<State>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Uninit,
    Reachable,
    Unreachable,
}

/// A `Ref` for garbage collected objects.
pub struct GcRcRef<'a, GC: GarbageCollector, T>(Ref<'a, Option<GcRc<GC, T>>>);

impl<GC: GarbageCollector, T: Traceable<GC>> GcRcCell<GC, T> {
    pub fn new() -> GcRcCell<GC, T> {
        GcRcCell {
            curr: RefCell::new(None),
            state: Cell::new(State::Uninit),
        }
    }

    fn must_be_reachable(&self) -> Result<(), BorrowMutError> {
        if self.state.get() == State::Reachable {
            Ok(())
        } else {
            debug_assert_eq!(self.state.get(), State::Uninit);
            // Deliberately reborrow to return an error
            let _ = self.curr.try_borrow_mut()?;
            let _ = self.curr.try_borrow_mut()?;
            Ok(())
        }
    }

    /// Replicating the `RefCell` API
    pub fn try_borrow<'a>(&'a self) -> Result<GcRcRef<'a, GC, T>, BorrowError> {
        Ok(GcRcRef(self.curr.try_borrow()?))
    }

    /// Replicating the `RefCell` API
    pub fn borrow<'a>(&'a self) -> GcRcRef<'a, GC, T> {
        self.try_borrow().expect("Borrow failed")
    }

    /// Try to set the refcell to be a new object
    pub fn try_set(&self, rc: &GcRc<GC, T>) -> Result<(), BorrowMutError> {
        self.must_be_reachable()?;
        *self.curr.try_borrow_mut()? = Some(rc.dangerous_clone());
        Ok(())
    }

    /// Try to set the refcell to be a clone of an existing object
    pub fn try_set_new(&self, value: T) -> Result<(), BorrowMutError> {
        self.must_be_reachable()?;
        *self.curr.try_borrow_mut()? = Some(GcRc::dangerous_new(value));
        Ok(())
    }

    /// Set the refcell to be a clone of an existing object
    pub fn set<'a>(&'a self, rc: &GcRc<GC, T>) {
        self.try_set(rc).expect("Borrow failed")
    }

    /// Set the refcell to be a new object
    pub fn set_new(&self, value: T) {
        self.try_set_new(value).expect("Borrow failed")
    }
}

impl<GC: GarbageCollector, T: Traceable<GC>> Traceable<GC> for GcRcCell<GC, T> {
    fn initialize(&self, _: &GC::Handle) {
        debug_assert_eq!(self.state.get(), State::Uninit);
        self.curr.replace(None);
        self.state.set(State::Reachable);
    }
    fn trace(&self, gc: &mut GC) {
        debug_assert_eq!(self.state.get(), State::Reachable);
        if let Some(ref value) = *self.curr.borrow() {
            value.trace(gc);
        }
    }
    fn finalize(&self) {
        debug_assert_eq!(self.state.get(), State::Reachable);
        self.curr.replace(None);
        self.state.set(State::Unreachable);
    }
}

impl<'a, GC: GarbageCollector, T> Deref for GcRcRef<'a, GC, T> {
    type Target = Option<GcRc<GC, T>>;
    fn deref(&self) -> &Option<GcRc<GC, T>> {
        self.0.deref()
    }
}

#[cfg(test)]
mod tests {

    use crate::GarbageCollector;
    use crate::GcHandle;
    use crate::GcRc;
    use crate::GcRcCell;
    use crate::Traceable;
    use std::cell::Cell;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::collections::HashSet;
    use std::rc::Rc;

    type Address = usize;

    type TestHandle = Rc<Cell<Option<Address>>>;

    type Object = (TestHandle, Box<dyn Traceable<TestGC>>);

    type Memory = (HashMap<Address, Object>, Address);

    thread_local! { static MEMORY: RefCell<Memory> = RefCell::new((HashMap::new(), 0)); }

    impl GcHandle<TestGC> for TestHandle {
        fn new(reflected: Box<dyn Traceable<TestGC>>) -> TestHandle {
            MEMORY.with(|memory| {
                let (address, handle) = {
                    let mut memory = memory.borrow_mut();
                    let (ref mut map, ref mut next) = *memory;
                    let address = *next;
                    let handle = Rc::new(Cell::new(Some(address)));
                    let object = (handle.clone(), reflected);
                    *next = *next + 1;
                    map.insert(address, object);
                    (address, handle)
                };
                let memory = memory.borrow();
                if let Some((_, ref reflector)) = memory.0.get(&address) {
                    reflector.initialize(&handle);
                }
                handle
            })
        }
    }

    struct TestGC {
        roots: Vec<TestHandle>,
        marked: HashSet<Address>,
    }

    impl TestGC {
        fn new() -> TestGC {
            TestGC {
                roots: Vec::new(),
                marked: HashSet::new(),
            }
        }
    }

    impl GarbageCollector for TestGC {
        type Handle = TestHandle;
        fn gc(&mut self) {
            MEMORY.with(|memory| {
                let roots: Vec<TestHandle> = self.roots.iter().cloned().collect();
                self.marked.clear();
                for root in &roots {
                    self.mark(root);
                }
                memory
                    .borrow_mut()
                    .0
                    .retain(|address, (handle, reflector)| {
                        let keep = self.marked.contains(address);
                        if !keep {
                            handle.set(None);
                            reflector.finalize();
                        }
                        keep
                    })
            });
        }
        fn mark(&mut self, handle: &TestHandle) {
            MEMORY.with(|memory| {
                let address = handle.get().expect("Tried to mark a GC'd object");
                if self.marked.insert(address) {
                    let memory = memory.borrow();
                    let (_, ref reflector) =
                        memory.0.get(&address).expect("Tried to mark a GC'd object");
                    reflector.trace(self);
                }
            })
        }
        fn root(&mut self, handle: &TestHandle) {
            self.roots.push(handle.clone());
        }
    }

    type DOM<T> = GcRc<TestGC, T>;

    type DOMRefCell<T> = GcRcCell<TestGC, T>;

    struct Node {
        data: usize,
        prev: DOMRefCell<Node>,
        next: DOMRefCell<Node>,
    }

    impl Traceable<TestGC> for Node {
        fn initialize(&self, handle: &TestHandle) {
            self.prev.initialize(handle);
            self.next.initialize(handle);
        }
        fn trace(&self, gc: &mut TestGC) {
            self.prev.trace(gc);
            self.next.trace(gc);
        }
        fn finalize(&self) {
            self.prev.finalize();
            self.next.finalize();
        }
    }

    impl Node {
        fn new(data: usize) -> Node {
            Node {
                data: data,
                prev: DOMRefCell::new(),
                next: DOMRefCell::new(),
            }
        }

        fn insert_after(self, other: &DOM<Node>) {
            // TODO: set self.next to be the current other.next
            other.next.set_new(self);
            let this = other.next.borrow();
            let this = this.as_ref().unwrap();
            this.prev.set(other);
        }
    }

    #[test]
    fn test_dom() {
        let mut gc = TestGC::new();
        let n0 = Node::new(0);
        let n1 = Node::new(1);
        let ref root = GcRc::rooted(&mut gc, n0);
        n1.insert_after(root);
        assert_eq!(root.data, 0);
        assert!(root.prev.borrow().is_none());
        assert_eq!(root.next.borrow().as_ref().unwrap().data, 1);
    }
}
