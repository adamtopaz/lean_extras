import Lean

open Lean

/--
A structure that pairs a value with an identifier.
-/
structure WithId (α : Type u) : Type u where
  val : α
  id : UInt64
deriving Hashable, BEq, DecidableEq, Inhabited

