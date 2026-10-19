module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Workspace
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Workspace
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! The four generation workspace widths have public initialization traces. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem workspace_ct {w : Nat} (hw : w = 4 ∨ w = 16 ∨ w = 32 ∨ w = 48)
    {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.x0]) :
    RelCT isa (Two Φ) (Impl.Dsa.AArch64.Generation.workspace w) (fun _ _ => True) := by
  rcases hw with rfl | rfl | rfl | rfl <;> exact two_taint _ hp (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
