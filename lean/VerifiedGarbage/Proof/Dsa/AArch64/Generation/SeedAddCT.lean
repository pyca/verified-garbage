module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Wrapped-seed addition leaks only its buffer addresses -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem seedAdd20_ct {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.x1, .x2]) :
    RelCT isa (Two Φ) (Impl.Dsa.AArch64.Generation.seedAdd 20) (fun _ _ => True) :=
  two_taint _ hp (by taint_decide)

theorem seedAdd32_ct {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.x1, .x2]) :
    RelCT isa (Two Φ) (Impl.Dsa.AArch64.Generation.seedAdd 32) (fun _ _ => True) :=
  two_taint _ hp (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
