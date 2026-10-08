import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FastEnv
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Literal

/-! Generate a literal certificate and final states. Callers independently
validate the certificate and both executions in the kernel. -/

open Lean Meta Elab Command Term in
elab "forward_state " n:ident " := " t:term : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let v ← elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let v ← instantiateMVars v
    let ty ← instantiateMVars (← inferType v)
    let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) ty)
    let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) ty inst v)
    addDecl <| .defnDecl {
      name := name, levelParams := [], type := ty, value := ShareCommon.shareCommon' l
      hints := .abbrev, safety := .safe }

