module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Workspace
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Workspace
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! The four generation workspace widths have public initialization traces. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem workspace_ct {w : Nat} (hw : w = 4 ∨ w = 16 ∨ w = 32 ∨ w = 48)
    {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.x0]) :
    RelCT isa (Two Φ) (Impl.Dsa.AArch64.Generation.workspace w) (fun _ _ => True) := by
  rcases hw with rfl | rfl | rfl | rfl <;> exact two_taint _ hp (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
