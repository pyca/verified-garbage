module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ForceWitness
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.ForceWitness
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! Forced witness shaping has no data-dependent control flow. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem forceWitness_ct {len : Nat} (hlen : len = 20 ∨ len = 32 ∨ len = 128 ∨ len = 256 ∨ len = 384)
    {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.x1]) :
    RelCT isa (Two Φ) (.block (Impl.Dsa.AArch64.Generation.forceWitness len)) (fun _ _ => True) := by
  rcases hlen with rfl | rfl | rfl | rfl | rfl <;> exact two_taint _ hp (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
