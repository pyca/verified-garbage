import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentStream
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.Stream

/-! ## From `ResidentPair.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr)

/-- Five SHAKE256 blocks with one initial state load and one final state store.
This is an internal fragment; its enclosing sampler saves the ABI registers. -/
theorem maskPairWith_ok (core : Core) {s : State} {p a b : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : PairAt s.mem p A B) (hrp : s.gpr rp=p) (ha : s.gpr ra=a) (hb : s.gpr rb=b)
    (hra : rp ≠ ra) (hrb : rp ≠ rb) (hr28 : rp ≠ .x28)
    (hr6 : rp ≠ .x6) (hr7 : rp ≠ .x7) (hr16 : rp ≠ .x16)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16) (ha28 : ra ≠ .x28)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hb28 : rb ≠ .x28)
    (hab : ra ≠ rb)
    (hd : (Region.mk a 680).Disjoint ⟨b,680⟩)
    (hpa : (Region.mk a 680).Disjoint (pairR p))
    (hpb : (Region.mk b 680).Disjoint (pairR p))
    (hin : ∀ i < 25, InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hw : ∀ i < 25, InRegions s.wr (wordAddr p i) 16)
    (hwa : ∀ j < 5, ∀ i < 8, InRegions s.wr ((a+BitVec.ofNat 64 (136*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ j < 5, ∀ i < 8, InRegions s.wr ((b+BitVec.ofNat 64 (136*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwal : ∀ j < 5, InRegions s.wr ((a+BitVec.ofNat 64 (136*j))+BitVec.ofNat 64 128) 8)
    (hwbl : ∀ j < 5, InRegions s.wr ((b+BitVec.ofNat 64 (136*j))+BitVec.ofNat 64 128) 8) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Resident.maskPairWith core.code rp ra rb) s fun t =>
      PairAt t.mem p (permuted A 5) (permuted B 5) ∧
      StreamOutput t.mem a 8 5 A ∧ StreamOutput t.mem b 8 5 B ∧
      Frame [⟨a,680⟩,⟨b,680⟩,pairR p] s.mem t.mem ∧
      (∀ r, r ≠ ra → r ≠ rb → r ≠ .x28 → r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → t.gpr r=s.gpr r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  unfold Impl.MlDsa.AArch64.Optimized.Resident.maskPairWith
  apply WP.seq
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.load_ok hrp hp hin) ?_
  intro u hu
  apply WP.seq
  refine WP.mono (streamWith_ok core (n := 8) (blocks := 5) (by decide) (by decide) (by decide) hu.2
    (by rw [hu.1.gpr]; exact ha) (by rw [hu.1.gpr]; exact hb)
    ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab hd
    (by simpa only [hu.1.wr] using hwa) (by simpa only [hu.1.wr] using hwb)
    (by simpa only [hu.1.wr] using hwal) (by simpa only [hu.1.wr] using hwbl)) ?_
  intro v hv
  refine WP.mono (VG.Proof.Sha3.AArch64.Neon.store_ok (p := p) (r := rp)
    (by rw [hv.gpr rp hra hrb hr28 hr6 hr7 hr16,hu.1.gpr]; exact hrp) hv.pairs
    (by simpa only [hv.wr,hu.1.wr] using hw)) ?_
  intro t ht
  refine ⟨ht.2.1,?_,?_,?_,?_,ht.1.rd.trans (hv.rd.trans hu.1.rd),
    ht.1.wr.trans (hv.wr.trans hu.1.wr),ht.1.sp.trans (hv.sp.trans hu.1.sp)⟩
  · intro i hi
    refine (hv.outA i hi).keep (by decide) ht.2.2 ?_
    intro r hr
    have he : r=pairR p := by simpa only [List.mem_singleton] using hr
    subst r
    exact hpa.sub_left (Offset.sub_base a (by omega))
  · intro i hi
    refine (hv.outB i hi).keep (by decide) ht.2.2 ?_
    intro r hr
    have he : r=pairR p := by simpa only [List.mem_singleton] using hr
    subst r
    exact hpb.sub_left (Offset.sub_base b (by omega))
  · have hfirst : Frame [⟨a,680⟩,⟨b,680⟩,pairR p] s.mem v.mem := by
      have h := hv.frame.mono (rs' := [⟨a,680⟩,⟨b,680⟩,pairR p]) (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
        rcases hr with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
      simpa only [hu.1.mem] using h
    exact hfirst.trans (ht.2.2.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp))
  · intro r h1 h2 h3 h4 h5 h6
    rw [ht.1.gpr,hv.gpr r h1 h2 h3 h4 h5 h6,hu.1.gpr]

theorem maskPair_ok {s : State} {p a b : Addr} {rp ra rb : Reg} {A B : Spec.Sha3.State}
    (hp : PairAt s.mem p A B) (hrp : s.gpr rp=p) (ha : s.gpr ra=a) (hb : s.gpr rb=b)
    (hra : rp ≠ ra) (hrb : rp ≠ rb) (hr28 : rp ≠ .x28)
    (hr6 : rp ≠ .x6) (hr7 : rp ≠ .x7) (hr16 : rp ≠ .x16)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (ha16 : ra ≠ .x16) (ha28 : ra ≠ .x28)
    (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7) (hb16 : rb ≠ .x16) (hb28 : rb ≠ .x28)
    (hab : ra ≠ rb)
    (hd : (Region.mk a 680).Disjoint ⟨b,680⟩)
    (hpa : (Region.mk a 680).Disjoint (pairR p))
    (hpb : (Region.mk b 680).Disjoint (pairR p))
    (hin : ∀ i < 25, InRegions (s.rd++s.wr) (wordAddr p i) 16)
    (hw : ∀ i < 25, InRegions s.wr (wordAddr p i) 16)
    (hwa : ∀ j < 5, ∀ i < 8, InRegions s.wr ((a+BitVec.ofNat 64 (136*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ j < 5, ∀ i < 8, InRegions s.wr ((b+BitVec.ofNat 64 (136*j))+BitVec.ofNat 64 (16*i)) 16)
    (hwal : ∀ j < 5, InRegions s.wr ((a+BitVec.ofNat 64 (136*j))+BitVec.ofNat 64 128) 8)
    (hwbl : ∀ j < 5, InRegions s.wr ((b+BitVec.ofNat 64 (136*j))+BitVec.ofNat 64 128) 8) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Resident.maskPair rp ra rb) s fun t =>
      PairAt t.mem p (permuted A 5) (permuted B 5) ∧
      StreamOutput t.mem a 8 5 A ∧ StreamOutput t.mem b 8 5 B ∧
      Frame [⟨a,680⟩,⟨b,680⟩,pairR p] s.mem t.mem ∧
      (∀ r, r ≠ ra → r ≠ rb → r ≠ .x28 → r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → t.gpr r=s.gpr r) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp :=
  maskPairWith_ok originalCore hp hrp ha hb hra hrb hr28 hr6 hr7 hr16 ha6 ha7 ha16 ha28 hb6 hb7 hb16 hb28 hab
    hd hpa hpb hin hw hwa hwb hwal hwbl

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end

/-! ## From `ResidentBytes.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64

/-- The vectorized rate block has the same little-endian words as scalar
SHAKE serialization. -/
theorem RateBlock.word {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RateBlock m a n A) {i : Nat} (hi : i < 2*n+1) :
    m.readW (a+BitVec.ofNat 64 (8*i)) 64 = A[i]! := by
  by_cases he : i = 2*n
  · subst i
    simpa only [show 8*(2*n)=16*n by omega] using h.2
  · have hp := h.1 (i/2) (by omega)
    have hv := congrArg (fun v => vdword v (i%2)) hp
    rw [vdword_read16 _ _ (by omega)] at hv
    rcases (show i%2=0 ∨ i%2=1 by omega) with hm | hm
    · rw [hm,vdword_ofVDwords_0] at hv
      simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
        show 16*(i/2)+8*0=8*i by omega,show 2*(i/2)=i by omega] using hv
    · rw [hm,vdword_ofVDwords_1] at hv
      simpa only [BitVec.add_assoc,BitVec.ofNat_add_ofNat,
        show 16*(i/2)+8*1=8*i by omega,show 2*(i/2)+1=i by omega] using hv

/-- The caller's byte parser sees exactly the specification's state bytes. -/
theorem RateBlock.byte {m : Mem} {a : Addr} {n : Nat} {A : Spec.Sha3.State}
    (h : RateBlock m a n A) {j : Nat} (hj : j < 16*n+8) :
    m (a+BitVec.ofNat 64 j) = VG.Proof.Sha3.byteOf A j := by
  have hw := h.word (i := j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (a+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [BitVec.add_assoc,← BitVec.ofNat_add,show 8*(j/8)+j%8=j by omega] at he
  exact he

theorem permuted_eq_iterF (A : Spec.Sha3.State) (j : Nat) :
    permuted A j = VG.Proof.Sha3.iterF j A := by
  induction j with
  | zero => rfl
  | succ j ih => rw [permuted,VG.Proof.Sha3.iterF_succ,ih]

/-- Complete byte serialization agrees with the SHAKE specification, starting
with the first resident permutation. The caller supplies the absorbed state. -/
theorem StreamOutput.byte {m : Mem} {a : Addr} {n blocks : Nat} {A : Spec.Sha3.State}
    (h : StreamOutput m a n blocks A) (hn : n ≤ 10) {j : Nat}
    (hj : j < (16*n+8)*blocks) :
    m (a+BitVec.ofNat 64 j) =
      (Spec.Sha3.squeezeBlocks (16*n+8) (Spec.Sha3.keccakF A) blocks)[j]'(by
        rw [VG.Proof.Sha3.length_squeezeBlocks (by omega)]; exact hj) := by
  have hk : j/(16*n+8) < blocks := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa only [Nat.mul_comm] using hj)
  have hb := (h _ hk).byte (j := j%(16*n+8)) (Nat.mod_lt _ (by omega))
  rw [BitVec.add_assoc,← BitVec.ofNat_add,Nat.div_add_mod] at hb
  rw [hb,VG.Proof.Sha3.getElem_squeezeBlocks (by omega) (by omega),permuted_eq_iterF,
    VG.Proof.Sha3.iterF_keccakF]

end VG.Proof.MlDsa.AArch64.Optimized.Resident

end
