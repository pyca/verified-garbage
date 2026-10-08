import VerifiedGarbage.Proof.P256.EcdhInverse.Words
import VerifiedGarbage.Proof.P256.EcdhInverse.RawUpdate
import VerifiedGarbage.Proof.P256.EcdhInverse.Update

namespace VG.Proof.P256.EcdhInverse
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

def batchMemory : List (Nat × Nat) := batchW p256.invP++[(7104,576)]

private theorem word_values {m m' : Mem} {base : Addr} {a n : Nat}
    (h : ∀ i<n,word m base (a+8*i)=word m' base (a+8*i)) :
    wordsVal m base a n=wordsVal m' base a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [wordsVal]
    rw [show word m base a=word m' base a by simpa only [Nat.mul_zero,Nat.add_zero] using h 0 (by omega)]
    rw [ih (a:=a+8) (fun i hi => by rw [show a+8+8*i=a+8*(i+1) by omega]; exact h (i+1) (by omega))]

theorem update_clob : ∀r∈Update.optimized.flatMap Forward.instrClob,r∈allocatedRegs.filter (· != .x20) := by
  rw [Update.rightCode.lit_eq]; decide +kernel

theorem update_writes : ∀w∈Update.optimized.flatMap Forward.instrWrites,
    ∃w'∈batchMemory,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2 := by
  rw [Update.rightCode.lit_eq]; decide +kernel

theorem update_x27 : Reg.x27∉Update.optimized.flatMap Forward.instrClob := by
  rw [Update.rightCode.lit_eq]; decide +kernel

theorem batch_ok {base : Addr} {m : Nat} (hL : InvLay p256.invP 8192)
    {s : State} (hs : Scr s base 8192) (hM : ModOkA p256.invP.M 8192 m s.mem base)
    {I : Divstep.IState} (hI : IInv p256.invP base I s)
    (hd : |I.d|≤2^30) (hf1 : I.f%2=1) (hf : |I.f|≤m) (hg : |I.g|≤m)
    (ha : |I.a|≤m) (hb : |I.b|≤m) (hz : s.gpr .x27=0)
    {j : Nat} (hj : 1≤j) (hj' : j<2^64) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa Impl.P256.EcdhInverse.batch s fun t =>
      IInv p256.invP base (Divstep.batch 59 m p256.invP.M.minv.toNat I) t ∧
      t.gpr .x19=BitVec.ofNat 64 (j-1) ∧ KeepRegs batchRegs s t ∧
      Unch base batchMemory s.mem t.mem ∧ t.gpr .x27=0 := by
  unfold Impl.P256.EcdhInverse.batch
  refine WP.seq (WP.mono (words_ok hs hI hd hf1 hz hj hj' h19) fun a qa => ?_)
  refine WP.seq (WP.mono qa fun b ⟨bd,bu,bv,bq,br,b19,bmem,bkeep,bzero⟩ => ?_)
  have hsb := hs.of_keepRegs bkeep (by decide)
  have mb : ModOkA p256.invP.M 8192 m b.mem base := by rw [bmem]; exact hM
  have qb := raw_update_ok hL hsb mb
    (by rw [bmem]; exact hI.f) (by rw [bmem]; exact hI.g)
    (by rw [bmem]; exact hI.a) (by rw [bmem]; exact hI.b) hf1 hf hg ha hb bd bu bv bq br
  refine WP.mono (Update.refine hsb (by decide) qb) fun t ⟨u,qu,hu,kt,ut⟩ => ?_
  obtain ⟨iu,u19,ku,uu⟩ := qu
  have heq : ∀a∈[p256.invP.sF,p256.invP.sG,p256.invP.sA,p256.invP.sB],
      ∀n, n≤(if a=p256.invP.sF ∨ a=p256.invP.sG then 5 else 4) →
      wordsVal t.mem base a n=wordsVal u.mem base a n := by
    intro a ha n hn
    have hn5 : n≤5 := by split at hn <;> omega
    change a∈[2272,2312,2352,2384] at ha
    apply word_values
    intro i hi
    apply hu
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> simp only [Update.observe] <;>
        norm_num [show p256.invP.sF=2272 from rfl,show p256.invP.sG=2312 from rfl] at hn <;> omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> omega
  have hnot1 : Reg.x1∉Update.optimized.flatMap Forward.instrClob :=
    fun hr => (Update.keepsDeltaCounter _ hr).1 rfl
  have hnot19 : Reg.x19∉Update.optimized.flatMap Forward.instrClob :=
    fun hr => (Update.keepsDeltaCounter _ hr).2 rfl
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · rw [kt.gpr _ hnot1]; simpa only [Divstep.batch] using bd
  · rw [heq _ (by simp) _ (by decide)]; exact iu.f
  · rw [heq _ (by simp) _ (by decide)]; exact iu.g
  · rw [heq _ (by simp) _ (by decide)]; exact iu.a
  · rw [heq _ (by simp) _ (by decide)]; exact iu.b
  · rw [kt.gpr _ hnot19]; exact b19
  · exact bkeep.trans (kt.mono fun r hr => List.mem_cons_of_mem _ (update_clob r hr))
  · have h := ut.cover update_writes
    rw [bmem] at h
    exact h
  · rw [kt.gpr _ update_x27]; exact bzero

end VG.Proof.P256.EcdhInverse
