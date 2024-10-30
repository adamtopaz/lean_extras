import Lean

open Lean

/--
Run a computation in parallel on an array of elements.
Variables:
- `as` : the array of elements to run the computation on.
- `numThread` : the number of threads to use.
- `e` : the computation to run on each element. It takes the index of the element and the element itself as arguments.
-/
def Array.runInParallel 
    (as : Array α) 
    (numThread : Nat) 
    (e : Nat → α → IO (Except IO.Error Unit)) : 
    IO (Except IO.Error Unit) := do
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
    let res ← e i a
    match res with 
    | .error e => throw e
    | .ok _ => continue

/--
Map an array of elements to an array of elements in parallel.
Variables:
- `as` : the array of elements to map.
- `numThread` : the number of threads to use.
- `e` : the mapping function. It takes an element as an argument and returns the mapped element.
-/
def Array.mapInParallel 
    [Inhabited β]
    (as : Array α) 
    (numThread : Nat) 
    (e : α → IO (Except IO.Error β)) : 
    IO (Except IO.Error (Array β)) := do
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
