(** Define witnesses for some type properties:
    - [(a, b) Witness.eq] witnesses that [a = b]
    - [(a, b) Witness.sub] witnesses that [a] is a subtype of [b]
    - [(a, b) Witness.order] is used to reflect a total ordering on some types

    [Witness.order] is used to build heterogeneous maps indexed by type
    witnesses. One can compare keys, and additionally recover a type level
    equality in they case two keys are equal.
*)
module Witness = Witness

(** [World] is used to manipulate strongly typed finite sets (a family of type
    representing each intervals [0..n]).
    They can be extended, and this extension is reflected at the type-level:
    - dynamically, [0..n] is extended to [0..n+1],
    - statically, [0..n] is a subtype of [0..n+1].
*)
module World = World

(** [Flat] encodes binding trees by allocating names in finite sets.
    It is "flat" because the scoping structure is "flattened" to a set of
    monotonically increasing integers.
    Facilities are provided to assist in this process. Type safety ensures that
    names cannot expect and are interpreted in the appropriate scope (enforcing
    manual renaming if a name is ambiguous in a given context).
*)
module Flat = Flat
