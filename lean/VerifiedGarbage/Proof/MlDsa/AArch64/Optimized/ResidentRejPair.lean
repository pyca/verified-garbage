import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Resident (RateBlock originalCore)

/-- The registers the sixth block's pair changes. -/
def blockRegs : List Reg := [.x0,.x1,.x16,.x17,.x6,.x7]

/-- The adaptive sixth block: a call, the states loaded back, and the same vector
serialization as the resident path. -/
theorem pair_ok {s : State} {p a b w : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : s.gpr rp=p) (ha : s.gpr ra=a) (hb : s.gpr rb=b)
    (hw : s.gpr .x19+BitVec.ofNat 64 Impl.MlDsa.AArch64.Sample.Rej4.oX2=w)
    (hp1 : rp≠.x1) (hpc : rp∉X2.clobbered) (hac : ra∉X2.clobbered) (hbc : rb∉X2.clobbered)
    (ha6 : ra≠.x6) (ha7 : ra≠.x7) (hb6 : rb≠.x6) (hb7 : rb≠.x7)
    (hpair : PairAt s.mem p A B)
    (hin : ∀i<25,InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hwa : ∀i<10,InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀i<10,InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16)
    (hwal : InRegions s.wr (a+BitVec.ofNat 64 160) 8)
    (hwbl : InRegions s.wr (b+BitVec.ofNat 64 160) 8)
    (hd : (Region.mk a 168).Disjoint ⟨b,168⟩)
    (hpa : (pairR p).Disjoint ⟨a,168⟩) (hpb : (pairR p).Disjoint ⟨b,168⟩)
    (hpw : (pairR p).Disjoint (X2.callR w)) (hcov : Covers [pairR p,X2.callR w] s.wr) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.pair rp ra rb) s fun t =>
      RegKeep blockRegs s t ∧ PairAt t.mem p (Spec.Sha3.keccakF A) (Spec.Sha3.keccakF B) ∧
      RateBlock t.mem a 10 (Spec.Sha3.keccakF A) ∧
      RateBlock t.mem b 10 (Spec.Sha3.keccakF B) ∧
      Frame [pairR p,⟨a,168⟩,⟨b,168⟩,X2.callR w] s.mem t.mem := by
  unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.pair
  refine WP.seq (WP.mono (X2.call_ok true (by decide) hp1 hp hw hpw hpair hcov) fun t ⟨hk,hf,hpt⟩ => ?_)
  have hkt : RegKeep X2.clobbered s t := ⟨hk.gpr,hk.rd,hk.wr,hk.sp⟩
  rw [WP.block_append_iff]
  refine WP.mono (load_ok ((hkt.gpr _ hpc).trans hp) hpt (fun i hi => by rw [hk.rd,hk.wr]; exact hin i hi))
    fun s1 ⟨h1,hpair1⟩ => ?_
  refine WP.mono (Resident.squeeze_ok (n := 10) (by decide)
    (A := Spec.Sha3.keccakF A) (B := Spec.Sha3.keccakF B) hpair1
    (by rw [h1.gpr,hkt.gpr _ hac,ha]) (by rw [h1.gpr,hkt.gpr _ hbc,hb]) ha6 ha7 hb6 hb7 hd
    (fun i hi => by rw [h1.wr,hk.wr]; exact hwa i hi)
    (fun i hi => by rw [h1.wr,hk.wr]; exact hwb i hi)
    (by rw [h1.wr,hk.wr]; exact hwal)
    (by rw [h1.wr,hk.wr]; exact hwbl)) fun u ⟨h4,_,hra,hrb,hf4⟩ => ?_
  have hku : RegKeep [.x6,.x7] t u := ⟨fun r hr => by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      rw [h4.gpr r hr.1 hr.2,h1.gpr],
    h4.rd.trans h1.rd,h4.wr.trans h1.wr,h4.sp.trans h1.sp⟩
  have hf4' : Frame [⟨a,168⟩,⟨b,168⟩] t.mem u.mem := by rw [← h1.mem]; exact hf4
  refine ⟨(hkt.trans hku).mono (by decide),fun i hi => ?_,hra,hrb,?_⟩
  · rw [hf4'.read (pair_contains p hi) (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact hpa
      · exact hpb) (by decide)]
    exact hpt i hi
  · exact (hf.mono fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with h | h <;> simp [h]).trans
      (hf4'.mono fun r hr => by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; rcases hr with h | h <;> simp [h])

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
