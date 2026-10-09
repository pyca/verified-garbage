import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

def rateR (p : Addr) : Region := ⟨p,136⟩
def Rate136 (m : Mem) (p : Addr) (A : Spec.Sha3.State) : Prop :=
 ∀i<17,m.readW (outAddr p i) 64=A[i]!
theorem rate_contains (p : Addr) {i : Nat} (hi : i<17) :
 (rateR p).Contains (outAddr p i) 8 := Offset.contains_base p (by omega) (by omega)

theorem squeeze136_ok {s : State} {a b : Addr} {ra rb : Reg} {A B : Spec.Sha3.State}
    (ha : s.gpr ra = a) (hb : s.gpr rb = b)
    (ha6 : ra ≠ .x6) (ha7 : ra ≠ .x7) (hb6 : rb ≠ .x6) (hb7 : rb ≠ .x7)
    (hp : Pairs s A B) (hd : (rateR a).Disjoint (rateR b))
    (hwa : ∀ i < 17, InRegions s.wr (outAddr a i) 8)
    (hwb : ∀ i < 17, InRegions s.wr (outAddr b i) 8) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.BoundedFour.squeeze ra rb)) s fun t =>
      OutKeep s t ∧ Rate136 t.mem a A ∧ Rate136 t.mem b B ∧ Frame [rateR a,rateR b] s.mem t.mem := by
  unfold Impl.MlDsa.AArch64.Optimized.BoundedFour.squeeze
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => OutKeep s t ∧ Frame [rateR a,rateR b] s.mem t.mem ∧
      (∀ i < k, t.mem.readW (outAddr a i) 64 = A[i]!) ∧
      (∀ i < k, t.mem.readW (outAddr b i) 64 = B[i]!))
    (fun k t hk ⟨ht,hf,hva,hvb⟩ => ?_) 17 (Nat.le_refl _) s
    ⟨OutKeep.refl _,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h),
      fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun t ⟨ht,hf,hva,hvb⟩ => ⟨ht,hva,hvb,hf⟩
  refine WP.mono (squeeze_step (by omega) ((ht.gpr ra ha6 ha7).trans ha) ((ht.gpr rb hb6 hb7).trans hb)
    ha6 ha7 hb6 hb7 (by rw [ht.wr]; exact hwa k hk) (by rw [ht.wr]; exact hwb k hk))
    fun u ⟨hu,hm⟩ => ⟨ht.trans hu,?_,?_,?_⟩
  · rw [hm]
    exact (hf.writeW (by simp) _ (rate_contains a hk)).writeW (by simp) _ (rate_contains b hk)
  · intro i hi
    rw [hm,Mem.readW_writeW_sep (hd.sep (rate_contains a (by omega)) (rate_contains b hk)) (by decide)]
    by_cases he : i = k
    · subst i
      rw [Mem.readW_writeW_self64,ht.vec,hp k (by omega),vdword_ofVDwords_0]
    · rw [Mem.readW_writeW_sep (Offset.sep a (d := 8*i) (n := 8) (e := 8*k) (k := 8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact hva i (by omega)
  · intro i hi
    rw [hm]
    by_cases he : i = k
    · subst i
      rw [Mem.readW_writeW_self64,ht.vec,hp k (by omega),vdword_ofVDwords_1]
    · rw [Mem.readW_writeW_sep (Offset.sep b (d := 8*i) (n := 8) (e := 8*k) (k := 8)
        (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (hd.symm.sep (rate_contains b (by omega)) (rate_contains a hk)) (by decide)]
      exact hvb i (by omega)

theorem Rate136.byte {m : Mem} {p : Addr} {A : Spec.Sha3.State} (h : Rate136 m p A)
    {j : Nat} (hj : j < 136) : m (p+BitVec.ofNat 64 j) = Proof.Sha3.byteOf A j := by
  have hw := h (j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (outAddr p (j/8)) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega)] at he
  rw [outAddr,BitVec.add_assoc,← BitVec.ofNat_add,
    show 8*(j/8)+j%8 = j by omega] at he
  exact he
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
