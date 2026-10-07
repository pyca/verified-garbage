import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Build
import VerifiedGarbage.Proof.Framework.AArch64.Lit

namespace VG.Proof.Weierstrass.AArch64.Forward

deriving instance Lean.ToExpr for Op
deriving instance Lean.ToExpr for Node
deriving instance Lean.ToExpr for Tree
deriving instance Lean.ToExpr for Certificate

open Lean Meta Elab Command Term

/-- Generate an untrusted expression table. Its validity and both instruction
executions must still be proved by the kernel before it can refine code. -/
elab "certificate_value " n:ident " := " t:term : command => do
  let name := (← getCurrNamespace) ++ n.getId
  liftTermElabM do
    let ty := Lean.mkConst ``Certificate
    let v ← elabTermEnsuringType t ty
    let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) ty)
    let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) ty inst v)
    addDecl <| .defnDecl {
      name := name, levelParams := [], type := ty, value := ShareCommon.shareCommon' l
      hints := .abbrev, safety := .safe }

end VG.Proof.Weierstrass.AArch64.Forward
