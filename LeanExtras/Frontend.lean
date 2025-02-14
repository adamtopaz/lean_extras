import Lean
import Lean.Util.Path

open Lean Elab Frontend

/--
Run a computation in the frontend monad on a specific `input : String`.
-/
def runFrontendOn 
    (input : String) 
    (fileName : String := "<input>") 
    (options : Options := {}) 
    (enableInfoTrees? := true)
    (m : Frontend.FrontendM α) :
    IO (α × Frontend.State) := do
  searchPathRef.set compile_time_search_path%
  unsafe enableInitializersExecution
  let inputCtx : Lean.Parser.InputContext := Lean.Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header options messages inputCtx
  let cmdState := Command.mkState env messages options
  let cmdState := { cmdState with infoState.enabled := enableInfoTrees? }
  let ctx : Frontend.Context := ⟨inputCtx⟩
  let state : Frontend.State := {
    commandState := cmdState
    parserState := parserState
    cmdPos := parserState.pos
  }
  StateRefT'.run (ReaderT.run m ctx) state

/--
Run a computation in the frontend monad on a specific `input : String`.
Similar to `runFrontendOn`, but returns only the result of the computation.
-/
def runFrontendOn' 
    (input : String) 
    (fileName : String := "<input>") 
    (options : Options := {}) 
    (enableInfoTrees? := true)
    (m : Frontend.FrontendM α) :
    IO α := 
  runFrontendOn input fileName options enableInfoTrees? m <&> Prod.fst

/--
A structure that bundles data to be processed by the Lean frontend.
-/
structure LeanFile where
  input : String
  fileName : String := "<input>"
  options : Options := {}
  enableInfoTrees? : Bool := true

/--
Read a Lean file from a path, as a `LeanFile`.
-/
def LeanFile.read (path : System.FilePath) : IO LeanFile := do
  let contents ← IO.FS.readFile path
  return { input := contents }

/--
Find a `lean` file by its module name, as a `LeanFile`.
-/
def LeanFile.findModule (mod : Name) : IO LeanFile := do
  let filePath := (← findOLean mod).toString.replace ".lake/build/lib/" ""
  LeanFile.read <| (System.FilePath.mk filePath).withExtension "lean"

/--
Run a computation in the frontend monad on a specific `LeanFile`.
-/
def LeanFile.runFrontend (f : LeanFile) (m : Frontend.FrontendM α) : IO (α × Frontend.State) := 
    runFrontendOn f.input f.fileName f.options f.enableInfoTrees? m

/--
Run a computation in the frontend monad on a specific `LeanFile`.
Similar to `LeanFile.runFrontend`, but returns only the result of the computation.
-/
def LeanFile.runFrontend' (f : LeanFile) (m : Frontend.FrontendM α) : IO α := 
    runFrontendOn' f.input f.fileName f.options f.enableInfoTrees? m

/--
Get the info trees from a `LeanFile`.
-/
def LeanFile.getInfoTrees (f : LeanFile) : IO (PersistentArray InfoTree) := f.runFrontend' do
  processCommands
  let trees := (← get).commandState.infoState.trees
  return trees

/--
Run a computation in the frontend monad on a specific module.
-/
def Lean.Name.runFrontend (mod : Name) (m : Frontend.FrontendM α) : IO (α × Frontend.State) := 
  LeanFile.findModule mod >>= fun e => e.runFrontend m

/--
Run a computation in the frontend monad on a specific module.
Similar to `Lean.Name.runFrontend`, but returns only the result of the computation.
-/
def Lean.Name.runFrontend' (mod : Name) (m : Frontend.FrontendM α) : IO α := 
  LeanFile.findModule mod >>= fun e => e.runFrontend' m

/--
Get the info trees from a module.
-/
def Lean.Name.getInfoTrees (mod : Name) : IO (PersistentArray InfoTree) := 
  LeanFile.findModule mod >>= fun e => e.getInfoTrees

/--
A convenience function to run a computation on the infotrees in a module.
-/
def LeanFile.withInfoTrees (mod : LeanFile) (m : PersistentArray InfoTree → IO α) : IO α := do
  let trees ← mod.getInfoTrees
  m trees

/--
Visit all nodes in all infotrees in a module.
-/
def LeanFile.withVisitInfoTrees 
    (mod : LeanFile) 
    (pre : ContextInfo → Info → PersistentArray InfoTree → IO Bool) 
    (post : ContextInfo → Info → PersistentArray InfoTree → List (Option α) → IO α) : IO (Array (Option α)) :=
  mod.withInfoTrees fun trees => do
    let mut out := #[]
    for tree in trees do
      out := out.push <| ← tree.visitM pre post
    return out

/--
Visit all nodes in all infotrees in a module.
This is a version of `Lean.Name.withVisitInfoTrees` that does not return any values.
-/
def LeanFile.withVisitInfoTrees' (mod : LeanFile) 
    (pre : ContextInfo → Info → PersistentArray InfoTree → IO Bool) 
    (post : ContextInfo → Info → PersistentArray InfoTree → IO Unit) : IO Unit := do
  mod.withInfoTrees fun trees => do
    for tree in trees do
      tree.visitM' pre post

