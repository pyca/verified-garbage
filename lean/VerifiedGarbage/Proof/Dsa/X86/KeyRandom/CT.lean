module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Dsa.X86.KeyRandom
public meta import VerifiedGarbage.Proof.Framework.X86.Taint

public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Impl.Dsa.X86.KeyRandom

/-!
# The sampler's secret-byte loops leak nothing (x86)

Only pointers and counts are shared between runs; neither candidate bytes,
the borrow, nor the nonzero accumulator is assumed equal. The leading byte
of q, on which `mask` branches, is public.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.Impl.Dsa.X86

theorem copyLoop_ct {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.esi, .edx, .ecx]) :
    RelCT isa (Two Φ) (.loop (.block KeyRandom.copyByte) .ne) (fun _ _ => True) :=
  two_taint [.esi, .edx, .ecx] h (by taint_decide)

theorem rangeBody_ct {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.esi, .edx, .ecx]) :
    RelCT isa (Two Φ) (.seq (.loop (.block KeyRandom.rangeByte) .ne) (.block KeyRandom.rangeFinish))
      (fun _ _ => True) :=
  two_taint [.esi, .edx, .ecx] h (by taint_decide)

theorem mask_ct {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.edx]) :
    RelCT isa (Two Φ) KeyRandom.mask (fun _ _ => True) :=
  two_taint [.edx] h (by taint_decide)

end VG.Proof.Dsa.X86.KeyRandom
