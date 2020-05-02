/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

use std::cell::RefCell;
use std::mem;
use std::rc::Rc;
use std::rc::Weak;

struct RcCellData<T> {
    borrows: Vec<Weak<T>>,
    latest_borrowed: bool,
    latest: Rc<T>,
}

pub struct RcCell<T>(RefCell<RcCellData<T>>);

impl<T> RcCell<T> {
    pub fn new(x: T) -> RcCell<T> {
        RcCell(RefCell::new(RcCellData {
            borrows: Vec::new(),
            latest: Rc::new(x),
            latest_borrowed: false,
        }))
    }

    pub fn set(&self, x: T) -> Option<T> {
        let mut this = self.0.borrow_mut();
        let prev = mem::replace(&mut this.latest, Rc::new(x));
        this.latest_borrowed = false;
        Rc::try_unwrap(prev).ok()
    }

    pub fn get(&self) -> Rc<T> {
        let mut this = self.0.borrow_mut();
        if !this.latest_borrowed {
            let weak = Rc::downgrade(&this.latest);
            this.latest_borrowed = true;
            this.truncate();
            this.borrows.push(weak);
        }
        this.latest.clone()
    }

    pub fn borrowed(&self) -> Borrowed<T> {
        Borrowed {
            position: 0,
            cell: self,
        }
    }
}

impl<T> RcCellData<T> {
    fn truncate(&mut self) {
        let len = self
            .borrows
            .iter()
            .enumerate()
            .rev()
            .find(|(_, weak)| weak.strong_count() > 0)
            .map(|(index, _)| index + 1)
            .unwrap_or(0);
        self.borrows.truncate(len);
    }
}

pub struct Borrowed<'a, T> {
    position: usize,
    cell: &'a RcCell<T>,
}

impl<'a, T> Iterator for Borrowed<'a, T> {
    type Item = Rc<T>;
    fn next(&mut self) -> Option<Rc<T>> {
        self.cell.0.borrow().borrows[self.position..]
            .iter()
            .enumerate()
            .filter_map(|(index, weak)| {
                self.position = index;
                weak.upgrade()
            })
            .next()
    }
}
