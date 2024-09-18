import Lean

open Lean

def Array.runInParallel 
    [Monad M] [MonadLift IO M]
    (as : Array α) 
    (numThread : Nat) 
    (e : α → IO (Except IO.Error Unit)) : 
    M (Except IO.Error Unit) := do
  let mut tasks := #[]
  for thread in [:numThread] do
    let task ← IO.asTask <| mkTask thread numThread as e
    tasks := tasks.push task
  for t in tasks do
    let t ← IO.wait t
    match t with 
    | .error e => show IO _ from throw e
    | .ok _ => continue
  return .ok ()
where mkTask thread numThread as e : IO Unit := do
  for h : i in [thread:as.size:numThread] do
    let a := as[i]'h.right
    let res ← e a
    match res with 
    | .error e => throw e
    | .ok _ => continue

def Array.mapInParallel 
    [Monad M] [MonadLift IO M]
    [Inhabited β]
    (as : Array α) 
    (numThread : Nat) 
    (e : α → IO (Except IO.Error β)) : 
    M (Except IO.Error (Array β)) := do
  let mut tasks := #[]
  for thread in [:numThread] do
    let task ← IO.asTask <| mkTask thread numThread as e
    tasks := tasks.push task
  let mut fromTasks := #[]
  for t in tasks do
    let t ← IO.wait t
    match t with 
    | .error e => show IO _ from throw e
    | .ok bs => fromTasks := fromTasks.push bs
  let mut out : Array β := Array.mkArray as.size default
  for bs in fromTasks do
    for (i,b) in bs do
      out := out.set! i b
  return .ok out
where mkTask thread numThread as e : IO (Array (Nat × β)) := do
  let mut out := #[]
  for h : i in [thread:as.size:numThread] do
    let a := as[i]'h.right
    let res ← e a
    match res with 
    | .error e => throw e
    | .ok b => 
      out := out.push (i,b)
  return out
