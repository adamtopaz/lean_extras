import Lean
import Lean.Util.Path

open Lean Elab Frontend

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

def runFrontendOn' 
    (input : String) 
    (fileName : String := "<input>") 
    (options : Options := {}) 
    (enableInfoTrees? := true)
    (m : Frontend.FrontendM α) :
    IO α := 
  runFrontendOn input fileName options enableInfoTrees? m <&> Prod.fst

structure LeanFile where
  input : String
  fileName : String := "<input>"
  options : Options := {}
  enableInfoTrees? : Bool := true

def LeanFile.read (path : System.FilePath) : IO LeanFile := do
  let contents ← IO.FS.readFile path
  return { input := contents }

def LeanFile.findModule (mod : Name) : IO LeanFile := do
  let filePath := (← findOLean mod).toString.replace ".lake/build/lib/" ""
  LeanFile.read <| (System.FilePath.mk filePath).withExtension "lean"

def LeanFile.runFrontend (f : LeanFile) (m : Frontend.FrontendM α) : IO (α × Frontend.State) := 
    runFrontendOn f.input f.fileName f.options f.enableInfoTrees? m

def LeanFile.runFrontend' (f : LeanFile) (m : Frontend.FrontendM α) : IO α := 
    runFrontendOn' f.input f.fileName f.options f.enableInfoTrees? m

def LeanFile.getInfoTrees (f : LeanFile) : IO (PersistentArray InfoTree) := f.runFrontend' do
  processCommands
  let trees := (← get).commandState.infoState.trees
  return trees

def Lean.Name.runFrontend (mod : Name) (m : Frontend.FrontendM α) : IO (α × Frontend.State) := 
  LeanFile.findModule mod >>= fun e => e.runFrontend m

def Lean.Name.runFrontend' (mod : Name) (m : Frontend.FrontendM α) : IO α := 
  LeanFile.findModule mod >>= fun e => e.runFrontend' m

def Lean.Name.getInfoTrees (mod : Name) : IO (PersistentArray InfoTree) := 
  LeanFile.findModule mod >>= fun e => e.getInfoTrees
