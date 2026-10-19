module

public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Random
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Leakage proofs for the sampler's secret-byte operations.
Only pointer and loop-count registers are shared between runs; neither
candidate bytes, q bytes, borrow nor the nonzero accumulator is assumed equal.
-/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64

def RandomPublicRegs (rs : List Reg) (p : Reg → BitVec 64) (s : State) : Prop :=
  ∀ r ∈ rs, s.gpr r = p r

theorem random_copyLoop_ct :
    RelCT isa (Two (RandomPublicRegs [.r10, .rdx, .r11]))
      (.loop (.block Random.copyByte) .ne) (fun _ _ => True) := by
  exact two_taint [.r10, .rdx, .r11]
    (pins_of (fun p r => p r) (fun _ _ h => h)) (by taint_decide)

theorem random_rangeBody_ct :
    RelCT isa (Two (RandomPublicRegs [.r10, .rdx, .r11]))
      (.seq (.loop (.block Random.rangeByte) .ne) (.block Random.rangeFinish))
      (fun _ _ => True) := by
  exact two_taint [.r10, .rdx, .r11]
    (pins_of (fun p r => p r) (fun _ _ h => h)) (by taint_decide)

theorem random_mask_ct :
    RelCT isa (Two (RandomPublicRegs [])) Random.mask (fun _ _ => True) := by
  exact two_taint [] (pins_of (fun p r => p r) (fun _ _ h => h)) (by taint_decide)

end VG.Proof.Dsa.X86_64
