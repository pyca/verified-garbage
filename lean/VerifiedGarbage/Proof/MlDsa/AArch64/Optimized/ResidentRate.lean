import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentSqueeze

namespace VG.Proof.MlDsa.AArch64.Optimized.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Neon (Pairs)

/-- Complete 128-bit groups of one serialized SHAKE rate. -/
def RatePairs (m : Mem) (a : Addr) (n : Nat) (A : Spec.Sha3.State) : Prop :=
  ∀ i < n, m.read (a+BitVec.ofNat 64 (16*i)) 16 = ofVDwords A[2*i]! A[2*i+1]!

theorem squeezePairs_ok {s : State} {a b : Addr} {ra rb : Reg} {n : Nat}
    {A B : Spec.Sha3.State} (hn : n ≤ 12) (hp : Pairs s A B)
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hd : (Region.mk a (16*n)).Disjoint ⟨b,16*n⟩)
    (hwa : ∀ i < n, InRegions s.wr (a+BitVec.ofNat 64 (16*i)) 16)
    (hwb : ∀ i < n, InRegions s.wr (b+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range n).flatMap
      (Impl.MlDsa.AArch64.Optimized.Resident.squeezePair ra rb))) s fun t =>
      SqueezeKeep s t ∧ Pairs t A B ∧ RatePairs t.mem a n A ∧ RatePairs t.mem b n B ∧
        Frame [⟨a,16*n⟩,⟨b,16*n⟩] s.mem t.mem := by
  have ac (i : Nat) (hi : i < n) : (Region.mk a (16*n)).Contains (a+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base a (by omega) (by omega)
  have bc (i : Nat) (hi : i < n) : (Region.mk b (16*n)).Contains (b+BitVec.ofNat 64 (16*i)) 16 :=
    Offset.contains_base b (by omega) (by omega)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => SqueezeKeep s t ∧ RatePairs t.mem a k A ∧ RatePairs t.mem b k B ∧
      Frame [⟨a,16*n⟩,⟨b,16*n⟩] s.mem t.mem)
    (fun k t hk ht => ?_) n (Nat.le_refl _) s
    ⟨SqueezeKeep.refl _,fun _ h => by omega,fun _ h => by omega,Frame.refl _ _⟩)
    (fun t h => ⟨h.1,h.1.pairs hp,h.2.1,h.2.2.1,h.2.2.2⟩)
  have hpt := ht.1.pairs hp
  refine WP.mono (squeezePair_ok (by omega)
    ((ht.1.gpr ra ha6 ha7).trans ha) ((ht.1.gpr rb hb6 hb7).trans hb)
    (by rw [ht.1.wr]; exact hwa k hk) (by rw [ht.1.wr]; exact hwb k hk)) ?_
  intro u hu
  have hm : u.mem = (t.mem.write (a+BitVec.ofNat 64 (16*k)) 16 (ofVDwords A[2*k]! A[2*k+1]!)).write
      (b+BitVec.ofNat 64 (16*k)) 16 (ofVDwords B[2*k]! B[2*k+1]!) := by
    rw [hu.2,hpt _ (by omega),hpt _ (by omega),vdword_ofVDwords_0,vdword_ofVDwords_0,
      vdword_ofVDwords_1,vdword_ofVDwords_1]
  refine ⟨ht.1.trans hu.1,?_,?_,?_⟩
  · intro i hi
    rw [hm,Mem.read_write_sep (hd.sep (ac i (by omega)) (bc k hk)) (by decide)]
    by_cases he : i = k
    · subst i
      exact VG.Proof.Sha3.AArch64.Neon.read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep a (d := 16*i) (n := 16) (e := 16*k) (k := 16)
        (by omega) (by omega) (by omega)) (by decide)]
      exact ht.2.1 i (by omega)
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      exact VG.Proof.Sha3.AArch64.Neon.read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep b (d := 16*i) (n := 16) (e := 16*k) (k := 16)
        (by omega) (by omega) (by omega)) (by decide),
        Mem.read_write_sep (hd.symm.sep (bc i (by omega)) (ac k hk)) (by decide)]
      exact ht.2.2.1 i (by omega)
  · rw [hm]
    exact (ht.2.2.2.write (by simp) _ (ac k hk)).write (by simp) _ (bc k hk)
end VG.Proof.MlDsa.AArch64.Optimized.Resident
