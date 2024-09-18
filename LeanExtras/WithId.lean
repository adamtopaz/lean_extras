import Lean

open Lean

structure WithId (α : Type u) : Type u where
  val : α
  id : UInt64
deriving Hashable, BEq

