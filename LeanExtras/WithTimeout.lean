import Lean

open Lean

/--
Return type used internally by `withTimeout`. 
-/
inductive TimeoutResult (α : Type) where
  | success (val : α)
  | timeout

/--
Run a computation with a timeout.
-/
def withTimeout (timeout : UInt32) (x : IO α) : IO α := do
  let timeoutTask ← IO.asTask (prio := .dedicated) <| 
    IO.sleep timeout >>= fun _ => return TimeoutResult.timeout
  let mainTask ← IO.asTask (prio := .dedicated) <| TimeoutResult.success <$> x
  match ← IO.waitAny [mainTask, timeoutTask] with
  | .ok <| .success a => return a
  | .ok <| .timeout => throw <| .userError s!"Operation timed out after {timeout}ms"
  | .error e => throw e
