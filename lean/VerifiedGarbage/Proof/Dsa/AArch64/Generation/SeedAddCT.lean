module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedAdd
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

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
