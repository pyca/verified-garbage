module

public import VerifiedGarbage.Proof.Dsa.AArch64.WidthChoice
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.WidthChoice
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of the supported public-width switch -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def WidthChoicePre (p : Nat × Nat) (s : State) : Prop :=
  s.gpr .x2 = BitVec.ofNat 64 p.1 ∧ s.gpr .x8 = BitVec.ofNat 64 p.2 ∧
    (s.gpr .x6 == (0#64)) = decide (p.1 = 128)

theorem widthChoice_ct : RelCT isa (Two WidthChoicePre) widthChoice (fun _ _ => True) := by
  unfold widthChoice
  refine two_ite (fun p s t hs ht => by change some (s.gpr .x6 == (0#64)) = some (t.gpr .x6 == (0#64)); rw [hs.2.2, ht.2.2]) ?_ ?_
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · exact two_taint [.x2] (pins_of (fun p _ => BitVec.ofNat 64 p.1) (by
      intro p s h r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact h.1.1)) (by taint_decide)

end VG.Proof.Dsa.AArch64
