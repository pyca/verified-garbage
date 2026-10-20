module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessCut
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessCut
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter candidates on x86-64: fixed-time shaping and halving -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate

/-- Only the pointers, byte count, and requested bit width affect shaping's trace. -/
theorem shape_ct {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.rdi, .rsi, .rcx, .rdx]) :
    RelCT isa (Two Φ) shape fun _ _ => True := two_taint _ hp (by taint_decide)

/-- In-place halving has the same trace for every buffer of the public length. -/
theorem halve_ct {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.rdi, .rcx]) :
    RelCT isa (Two Φ) halve fun _ _ => True := two_taint _ hp (by taint_decide)

/-- Witness masking leaks only its pointers and public dimensions. -/
theorem witnessCut_ct {α : Type} {Φ : α → State → Prop} (hp : Pins Φ [.rdi, .rsi, .rcx, .rdx]) :
    RelCT isa (Two Φ) witnessCut fun _ _ => True := two_taint _ hp (by taint_decide)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
