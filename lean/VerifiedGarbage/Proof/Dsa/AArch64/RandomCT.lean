module

public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Random
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Leakage proofs for the sampler's secret-byte operations.
Only pointer and loop-count registers are shared between runs; neither
candidate bytes, q bytes, borrow nor the nonzero accumulator is assumed equal.
-/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

def RandomPublicRegs (rs : List Reg) (p : Reg → BitVec 64) (s : State) : Prop :=
  ∀ r ∈ rs, s.gpr r = p r

theorem random_copyLoop_ct :
    RelCT isa (Two (RandomPublicRegs [.x12, .x2, .x9]))
      (.loop (.block Random.copyByte) (.nonzero .x .x9)) (fun _ _ => True) := by
  exact two_taint [.x12, .x2, .x9]
    (pins_of (fun p r => p r) (fun _ _ h => h)) (by taint_decide)

theorem random_rangeBody_ct :
    RelCT isa (Two (RandomPublicRegs [.x12, .x2, .x9]))
      (.seq (.loop (.block Random.rangeByte) (.nonzero .x .x9)) (.block Random.rangeFinish))
      (fun _ _ => True) := by
  exact two_taint [.x12, .x2, .x9]
    (pins_of (fun p r => p r) (fun _ _ h => h)) (by taint_decide)

theorem random_mask_ct :
    RelCT isa (Two (RandomPublicRegs [])) Random.mask (fun _ _ => True) := by
  exact two_taint [] (pins_of (fun p r => p r) (fun _ _ h => h)) (by taint_decide)

end VG.Proof.Dsa.AArch64
