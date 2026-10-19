module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedAdd
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call

/-! # Wrapped-seed addition leaks only its buffer addresses -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem seedAdd20_ct {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.rdi, .rsi]) :
    RelCT isa (Two Φ) (Impl.Dsa.X86_64.Generation.seedAdd 20) (fun _ _ => True) :=
  two_taint _ hp (by taint_decide)

theorem seedAdd32_ct {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.rdi, .rsi]) :
    RelCT isa (Two Φ) (Impl.Dsa.X86_64.Generation.seedAdd 32) (fun _ _ => True) :=
  two_taint _ hp (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
