import Lean

open Lean

/--
Run a computation with a timeout.
-/
def withTimeout (timeout : Nat) (x : IO α) : IO α := do
  let start ← IO.monoMsNow
  let task ← IO.asTask x
  while True do
    let currentTime ← IO.monoMsNow
    if currentTime - start > timeout then
      IO.cancel task
      throw <| IO.userError "timeout"
    if (← IO.hasFinished task) then
      match task.get with
      | .ok res => return res
      | .error e => throw e
  throw <| .userError "timeout"

