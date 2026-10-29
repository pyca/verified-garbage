module

public import VerifiedGarbage.Proof.Framework.KernelRfl
public meta import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FastEnv
public meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FastEnv
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Literal
public meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Literal
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Spec.Weierstrass

/-! Generate a literal certificate and final states. Callers independently
validate the certificate and both executions in the kernel. -/

public meta section

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
    addDecl (forceExpose := true) <| .defnDecl {
      name := name, levelParams := [], type := ty, value := ShareCommon.shareCommon' l
      hints := .abbrev, safety := .safe }

