import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCBase

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem maskSeedHalf_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {src dst : Nat} (hs : src%8=0) (hsb : src+32≤32768) (hsrc : inB (rbs++wbs) (sc src) 32 = true)
    (hdst : inB wbs (sc dst) 32 = true)
    (hsep : sepB rbs wbs (sc src) 32 (sc dst) 32 = true) :
    WP isa (.block (maskSeedHalf src dst)) s fun t =>
      PPostB S s t [(sc dst,32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc dst)) 32 = bytesAt s.mem (pa s (sc src)) 32 := by
  unfold maskSeedHalf
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc dst) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 src,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc src),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc dst)+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc dst)) (sb := .x28) (db := .x10) (so := src) (dO := 0) (by decide) (by decide) ⟨hs,hsb⟩ (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc src),32⟩ : Region).Disjoint ⟨pa s (sc dst),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]

end VG.Proof.MlDsa.AArch64.Sign
