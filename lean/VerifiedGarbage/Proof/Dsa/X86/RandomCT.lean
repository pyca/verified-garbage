module

public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Impl.Dsa.X86.RandomSign
meta import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
meta import VerifiedGarbage.Impl.Dsa.X86.RandomSign

/-!
# The sampler's secret-byte loops leak nothing (x86)

Only pointers and counts are shared between runs; neither candidate bytes,
the borrow, nor the nonzero accumulator is assumed equal. The leading byte
of q, on which `mask` branches, is public.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Dsa.X86

/-- The registers `rs` hold `p`'s values. -/
def PublicRegs (rs : List Reg) (p : Reg → BitVec 32) (s : State) : Prop :=
  ∀ r ∈ rs, s.gpr r = p r

theorem copyLoop_ct :
    RelCT isa (Two (PublicRegs [.esi, .edx, .ecx])) (.loop (.block Random.copyByte) .ne) (fun _ _ => True) :=
  two_taint [.esi, .edx, .ecx] (pins_of (fun p r => p r) (fun _ _ h => h)) (by taint_decide)

theorem rangeBody_ct :
    RelCT isa (Two (PublicRegs [.esi, .edx, .ecx]))
      (.seq (.loop (.block Random.rangeByte) .ne) (.block Random.rangeFinish)) (fun _ _ => True) :=
  two_taint [.esi, .edx, .ecx] (pins_of (fun p r => p r) (fun _ _ h => h)) (by taint_decide)

theorem mask_ct : RelCT isa (Two (PublicRegs [.edx])) Random.mask (fun _ _ => True) :=
  two_taint [.edx] (pins_of (fun p r => p r) (fun _ _ h => h)) (by taint_decide)

end VG.Proof.Dsa.X86
