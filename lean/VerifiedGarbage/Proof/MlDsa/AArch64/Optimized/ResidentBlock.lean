import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRate

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- An odd-word rate: complete vector groups and its final scalar word. -/
def RateBlock (m : Mem) (a : Addr) (n : Nat) (A : Spec.Sha3.State) : Prop :=
  RatePairs m a n A ∧ m.readW (a+BitVec.ofNat 64 (16*n)) 64 = A[2*n]!

/-- Vector serialization of either SHAKE rate, including the odd final word. -/
theorem squeeze_ok {s : State} {a b : Addr} {ra rb : Reg} {n : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 10) (hp : Pairs s A B)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hd : (Region.mk a (16*n+8)).Disjoint ⟨b,16*n+8⟩)
    (hwa : ∀ i < n, InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ i < n, InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16)
    (hwal : InRegions s.wr (a+BitVec.ofNat 64 (16*n)) 8)
    (hwbl : InRegions s.wr (b+BitVec.ofNat 64 (16*n)) 8) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.Resident.squeeze (2*n+1) ra rb)) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RateBlock t.mem a n A ∧ RateBlock t.mem b n B ∧
        Frame [⟨a,16*n+8⟩,⟨b,16*n+8⟩] s.mem t.mem := by
  have ac (i : Nat) (hi : i < n) : (Region.mk a (16*n+8)).Contains (a+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base a (by omega) (by omega)
  have bc (i : Nat) (hi : i < n) : (Region.mk b (16*n+8)).Contains (b+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base b (by omega) (by omega)
  have al : (Region.mk a (16*n+8)).Contains (a+BitVec.ofNat 64 (16*n)) 8 :=
    Offset.contains_base a (by omega) (by omega)
  have bl : (Region.mk b (16*n+8)).Contains (b+BitVec.ofNat 64 (16*n)) 8 :=
    Offset.contains_base b (by omega) (by omega)
  have haSub : (Region.mk a (16*n)).Sub ⟨a,16*n+8⟩ := by
    simpa using Offset.sub_base a (d := 0) (n := 16*n) (k := 16*n+8) (by omega)
  have hbSub : (Region.mk b (16*n)).Sub ⟨b,16*n+8⟩ := by
    simpa using Offset.sub_base b (d := 0) (n := 16*n) (k := 16*n+8) (by omega)
  unfold Impl.MlDsa.AArch64.Optimized.Resident.squeeze
  rw [show (2*n+1)/2=n by omega,show (2*n+1)%2=1 by omega,ite_eq_left rfl,
    show 2*n+1-1=2*n by omega,WP.block_append_iff]
  refine WP.mono (squeezePairs_ok (by omega) hp ha hb ha6 ha7 hb6 hb7
    ((hd.sub_left haSub).sub_right hbSub) hwa hwb) ?_
  intro t ht
  refine WP.mono (squeezeLast_ok (i := 2*n) (by omega)
    ((ht.1.gpr ra ha6 ha7).trans ha) ((ht.1.gpr rb hb6 hb7).trans hb)
    ha6 ha7 hb6 hb7
    (by rw [ht.1.wr]; simpa [VG.Proof.Sha3.AArch64.Neon.outAddr,show 8*(2*n)=16*n by omega] using hwal)
    (by rw [ht.1.wr]; simpa [VG.Proof.Sha3.AArch64.Neon.outAddr,show 8*(2*n)=16*n by omega] using hwbl)) ?_
  intro u hu
  have hm : u.mem = (t.mem.writeW (a+BitVec.ofNat 64 (16*n)) A[2*n]!).writeW
      (b+BitVec.ofNat 64 (16*n)) B[2*n]! := by
    rw [hu.2,ht.2.1 _ (by omega),vdword_ofVDwords_0,vdword_ofVDwords_1]
    simp only [VG.Proof.Sha3.AArch64.Neon.outAddr,show 8*(2*n)=16*n by omega]
  refine ⟨ht.1.trans hu.1,hu.1.pairs ht.2.1,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩
  · intro i hi
    rw [hm,Mem.writeW,Mem.writeW,
      Mem.read_write_sep (hd.sep (ac i hi) bl) (by decide),
      Mem.read_write_sep (Offset.sep a (d := 16*i) (n := 16) (e := 16*n) (k := 8)
        (by omega) (by omega) (by omega)) (by decide)]
    exact ht.2.2.1 i hi
  · rw [hm,Mem.readW_writeW_sep (hd.sep al bl) (by decide),Mem.readW_writeW_self64]
  · intro i hi
    rw [hm,Mem.writeW,Mem.writeW,
      Mem.read_write_sep (Offset.sep b (d := 16*i) (n := 16) (e := 16*n) (k := 8)
        (by omega) (by omega) (by omega)) (by decide),
      Mem.read_write_sep (hd.symm.sep (bc i hi) al) (by decide)]
    exact ht.2.2.2.1 i hi
  · rw [hm,Mem.readW_writeW_self64]
  · rw [hm]
    have hf : Frame [⟨a,16*n+8⟩,⟨b,16*n+8⟩] s.mem t.mem :=
      ht.2.2.2.2.sub (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_,by simp,haSub⟩
        · exact ⟨_,by simp,hbSub⟩)
    exact (hf.writeW (by simp) _ al).writeW (by simp) _ bl
end VG.Proof.MlDsa.AArch64.Optimized.Resident
