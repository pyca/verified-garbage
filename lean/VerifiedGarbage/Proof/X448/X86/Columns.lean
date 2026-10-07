import VerifiedGarbage.Proof.X448.X86.FnCtx

/-!
# X448 on x86 (32-bit): pointwise field operations

A pointwise operation fills `TMP` before the carry passes write the output,
permitting input/output aliasing.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem columns_ok {s : State} {base : Addr} (hs : Scr s base) {code : Nat → List Instr}
    {f : Nat → Nat} {rs : List Reg} (hr : .edi ∉ rs) (hb : ∀ i < 28, f i ≤ 2 ^ 32 - radix)
    (step : ∀ i < 28, ∀ t, Scr t base → Outside base TMP 112 s.mem t.mem → Keeps rs s t →
      WP isa (.block (code i)) t fun u =>
        u.mem = t.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (f i)) ∧ Keeps rs t u) :
    WP isa (.block ((List.range 28).flatMap code)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = f i) ∧ Outside base TMP 112 s.mem t.mem ∧ Keeps rs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = f i) ∧ Outside base TMP 112 s.mem t.mem ∧ Keeps rs s t
  have st : ∀ n t, n < 28 → inv n t → WP isa (.block (code n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (step n hn t (hs.of_keeps tk hr) tm tk) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (TMP + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [TMP]; omega)
    refine ⟨?_, tm.trans (out.mono (by omega) (by omega)), tk.trans uk⟩
    intro i hi
    change (word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  exact wp_range_flatMap (M := isa) (N := 28) inv st 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- Reading an input during a pointwise operation. -/
theorem input_limb {s t : State} {base : Addr} {a i : Nat} (h : Outside base TMP 112 s.mem t.mem)
    (ha : Slot a) (hi : i < 28) : limbs t.mem base a i = limbs s.mem base a i :=
  h.limbs (Or.inl (Nat.le_trans ha (by decide))) (Nat.le_trans ha (by decide)) hi

/-- Carry propagation after a pointwise operation, into the element at `o`,
with the common frame. -/
theorem columns_normalize {s : State} {base : Addr} {n o a : Nat} (hc : FnCtx s base n o a)
    {code : List Instr} {f : Nat → Nat} (hb : ∀ i < 28, f i ≤ 2 ^ 32 - radix)
    (hcode : WP isa (.block code) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = f i) ∧ Outside base TMP 112 s.mem t.mem ∧ Keeps clob s t) :
    WP isa (.block (code ++ normalize)) s fun t =>
      (Keeps clob s t ∧ FieldMem base o s.mem t.mem WORK) ∧ Bounded t.mem base o ∧
        fe t.mem base o % Spec.X448.P = valN f 28 % Spec.X448.P := by
  rw [WP.block_append_iff]
  refine WP.mono hcode fun t ⟨tf, tm, tk⟩ => ?_
  have tc := hc.keep tk (by decide) (by decide) (tm.mono (by decide) (by decide))
  refine WP.mono (normalize_ok tc.scr tc.args (by have := tc.n3; omega) tc.slotO tc.argO tf hb)
    fun u ⟨uf, um, uk⟩ => ?_
  refine ⟨⟨tk.trans (uk.mono (by decide)), (FieldMem.work tm (by decide) (by decide)).trans um⟩, ?_, ?_⟩
  · intro i hi; rw [uf i hi]; exact digit_lt _ _
  · rw [show fe u.mem base o = valN (normalized f) 28 from valN_congr uf, normalized_mod hb]

end VG.Proof.X448.X86
