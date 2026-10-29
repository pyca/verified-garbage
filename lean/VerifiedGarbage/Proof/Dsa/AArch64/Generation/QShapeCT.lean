module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QShape
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.QShape
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Subgroup candidate shaping leaks only pointers and the digest length. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem qShape_ct {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.x12, .x2, .x9]) :
    RelCT isa (Two Φ) Impl.Dsa.AArch64.Generation.qShape (fun _ _ => True) :=
  two_taint _ hp (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
