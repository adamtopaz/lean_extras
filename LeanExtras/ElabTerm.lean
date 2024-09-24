import Lean

open Lean Elab Term 

syntax (name := elabTerm) "elab_term" doSeq : term

@[term_elab elabTerm]
def runElabTerm : TermElab := fun stx _expectedType? => 
  match stx with 
  | `(elab_term $seq:doSeq) => do
    let out ← unsafe 
      evalTerm (TermElabM Expr) (mkApp (mkConst ``TermElabM) (mkConst ``Expr)) (← `(do $seq))
    out
  | _ => throwUnsupportedSyntax

