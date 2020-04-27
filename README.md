# Garbage collected reference counted objects

The aim of this library is to see if an interface to a garbage collector
can be written just in safe Rust.

The tricky part of this is to avoid having to use a cycle detector.
This library does this by providing an implementation of mutable
references (which are the source of cycles) that are automatically
cleared when they are finalized.
