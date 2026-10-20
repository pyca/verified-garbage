module

public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Impl.Dsa.X86.Random
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Impl.Dsa.X86.Random
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The sampler's secret-byte loops leak nothing (x86)

Only pointers and counts are shared between runs; neither candidate bytes,
the borrow, nor the nonzero accumulator is assumed equal. The leading byte
of q, on which `mask` branches, is public.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

theorem copyLoop_ct {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.esi, .edx, .ecx]) :
    RelCT isa (Two Φ) (.loop (.block Random.copyByte) .ne) (fun _ _ => True) :=
  two_taint [.esi, .edx, .ecx] h (by taint_decide)

theorem rangeBody_ct {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.esi, .edx, .ecx]) :
    RelCT isa (Two Φ) (.seq (.loop (.block Random.rangeByte) .ne) (.block Random.rangeFinish))
      (fun _ _ => True) :=
  two_taint [.esi, .edx, .ecx] h (by taint_decide)

theorem mask_ct {α : Type} {Φ : α → State → Prop} (h : Pins Φ [.edx]) :
    RelCT isa (Two Φ) Random.mask (fun _ _ => True) :=
  two_taint [.edx] h (by taint_decide)

end VG.Proof.Dsa.X86
