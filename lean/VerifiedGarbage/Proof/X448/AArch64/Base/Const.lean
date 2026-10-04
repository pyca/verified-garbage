import VerifiedGarbage.Impl.X448.AArch64.Base
import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
import VerifiedGarbage.Proof.X448.Wide.Limbs
import VerifiedGarbage.Proof.Framework.AArch64.Tbl

/-!
# X448 on AArch64: field elements from immediates

Untrusted: everything here is checked by Lean. `constSlot` stores a field
element's eight 56-bit limbs (`limb`), each built from immediates; the slot
then holds that element. Light (no group law), so that every function that
starts from constants can use it.
-/

namespace VG.Proof.X448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside store_ok)

theorem limb_valN (v : Spec.X448.Fe) : ∀ n, VG.Proof.X448.Wide.valN (fun i => (limb v i).toNat) n =
    v.val % VG.Proof.X448.Wide.radix ^ n
  | 0 => by simp [VG.Proof.X448.Wide.valN, Nat.mod_one]
  | n + 1 => by
    rw [VG.Proof.X448.Wide.valN_succ, limb_valN v n, Nat.pow_succ, Nat.mod_mul]
    congr 2
    simp only [limb, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)),
      show 2 ^ (56 * n) = VG.Proof.X448.Wide.radix ^ n by rw [Nat.pow_mul]; rfl]
    rfl

theorem limb_val (v : Spec.X448.Fe) : VG.Proof.X448.Wide.valN (fun i => (limb v i).toNat) 8 = v.val := by
  rw [limb_valN]
  refine Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le v.isLt ?_)
  rw [show VG.Proof.X448.Wide.radix ^ 8 = VG.Proof.X448.Wide.full from rfl, VG.Proof.X448.Wide.full_eq]
  omega

theorem limb_lt (v : Spec.X448.Fe) (w : Nat) : (limb v w).toNat < 2 ^ 56 := by
  simp only [limb, BitVec.toNat_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by decide))

/-- A constant slot: its limbs from immediates, through `x4`. -/
theorem constSlot_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 64 ≤ 8192)
    (ho8 : o % 8 = 0) (v : Spec.X448.Fe) :
    WP isa (.block (constSlot o v)) s fun t =>
      (∀ w < 8, word t.mem base (o + 8 * w) = limb v w) ∧ Outside base o 64 s.mem t.mem ∧
      Keeps [.x4] s t := by
  let inv := fun n (t : State) =>
    (∀ w < n, word t.mem base (o + 8 * w) = limb v w) ∧ Outside base o 64 s.mem t.mem ∧ Keeps [.x4] s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (const64 .x4 (limb v n) ++ [st .x4 (o + 8 * n)])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    rw [WP.block_append_iff]
    refine WP.mono (VG.AArch64.Tbl.const64_ok t .x4 (limb v n)) fun a ⟨a4, ka, ea⟩ => ?_
    have kt : Keeps [.x4] t a := ⟨fun r hr => ka r (by simpa using hr), by rw [ea], by rw [ea]⟩
    have ha : Scr a base := (hs.of_keeps tk (by decide)).of_keeps kt (by decide)
    have am : a.mem = t.mem := by rw [ea]
    refine WP.mono (store_ok ha (by omega) (by omega) .x4) fun u ⟨um, uk⟩ => ⟨fun w hw => ?_, ?_, ?_⟩
    · rw [um, VG.Proof.X448.AArch64.word_write_aligned _ _ (by omega) (by omega) (by omega) (by omega)]
      by_cases h : w = n
      · subst h; rw [ite_eq_left rfl, a4]
      · rw [ite_eq_right (by omega), am]; exact tv w (by omega)
    · intro x hx
      rw [um, VG.Proof.X448.AArch64.writeW_outside _ _ _ (by omega) x (by omega), am]
      exact tm x hx
    · exact (tk.trans kt).trans (uk.mono (by simp))
  have := wp_range_flatMap (M := isa) (N := 8) inv step 8 (Nat.le_refl _) s
    ⟨fun _ hw => absurd hw (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keeps.refl _ _⟩
  exact this

theorem F_of_words {m : Mem} {base : Addr} {o : Nat} {v : Spec.X448.Fe}
    (h : ∀ w < 8, word m base (o + 8 * w) = limb v w) : VG.Proof.X448.AArch64.Weak.F m base o = v := by
  simp only [VG.Proof.X448.AArch64.Weak.F]
  rw [VG.Proof.X448.Wide.valN_congr (fun w hw => show (word m base (o + 8 * w)).toNat = _ by rw [h w hw]),
    limb_val, VG.Proof.X448.toFe_self]

end VG.Proof.X448.AArch64.Base
