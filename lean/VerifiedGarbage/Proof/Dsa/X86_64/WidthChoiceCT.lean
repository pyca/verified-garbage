module

public import VerifiedGarbage.Proof.Dsa.X86_64.WidthChoice
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.WidthChoice
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant time of the supported public-width switch -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def WidthChoicePre (p : Nat × Nat) (s : State) : Prop :=
  s.gpr .rdx = BitVec.ofNat 64 p.1 ∧ s.gpr .r8 = BitVec.ofNat 64 p.2 ∧
    s.zf = some (decide (p.1 = 128))

theorem widthChoice_ct : RelCT isa (Two WidthChoicePre) widthChoice (fun _ _ => True) := by
  unfold widthChoice
  refine two_ite (fun p s t hs ht => by simp only [eval, hs.2.2, ht.2.2]) ?_ ?_
  · exact two_taint [] (by intro p s t hs ht r hr; cases hr) (by taint_decide)
  · exact two_taint [.rdx] (pins_of (fun p _ => BitVec.ofNat 64 p.1) (by
      intro p s h r hr
      simp only [List.mem_singleton] at hr
      subst r
      exact h.1.1)) (by taint_decide)

end VG.Proof.Dsa.X86_64
