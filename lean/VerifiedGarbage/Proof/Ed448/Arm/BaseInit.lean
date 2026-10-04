import VerifiedGarbage.Proof.X448.Arm.Save
import VerifiedGarbage.Proof.X448.Arm.Env
import VerifiedGarbage.Impl.Ed448.Arm.ScalarBase

/-!
# Ed448 base-point multiplication on ARMv7: the entry

The callee-saved registers saved (X448's `setupHead`) and every slot set to
its initial value (`initSlots_ok`): `R = (0 : 1 : 1)`, `Q` the base point, `d`,
and zero elsewhere, every limb below `2¹⁶`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot ACC st)

theorem initVal_lt (i : Nat) : initVal i < Spec.X448.P := by
  unfold initVal
  repeat (first | exact Fin.isLt _ | (split; exact Fin.isLt _) | split)
  decide +kernel

theorem initLimb_lt (i k : Nat) : initLimb i k < 65536 := Nat.mod_lt _ (by decide)

theorem valN_digits (v : Nat) : ∀ n, valN (fun k => v / 2 ^ (16 * k) % 65536) n = v % radix ^ n
  | 0 => by simp [valN, Nat.mod_one]
  | n + 1 => by
    rw [valN_succ, valN_digits v n, Nat.mod_pow_succ, radix, ← Nat.pow_mul]

theorem initStep_ok {s : State} {base : Addr} (hs : Scr s base) (h4 : s.gpr .r4 = 0) {i k : Nat}
    (hi : i < 22) (hk : k < 28) :
    WP isa (.block (initStep i k)) s fun t =>
      t.mem = s.mem.writeW (off base (slot i + 4 * k)) (BitVec.ofNat 32 (initLimb i k)) ∧
        Keeps [.r3] s t := by
  have hsl : slot i + 4 * k + 4 ≤ 4096 := by simp only [slot]; omega
  unfold initStep
  split
  · rename_i h0
    refine store_ok hs (by omega) fun t ht => WP.block_nil ⟨?_, ⟨fun r _ => by rw [ht.gpr], ht.rd, ht.wr⟩⟩
    rw [ht.mem, h4, h0]; rfl
  · refine VG.Proof.X25519.Arm.wp_movw fun u hu => ?_
    refine store_ok (hs.of_upd hu (by decide) (by decide)) (by omega) fun t ht => WP.block_nil ⟨?_, ?_⟩
    · rw [ht.mem, hu.mem, hu.gpr]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (initLimb_lt i k)]
    · exact ⟨fun r hr => by rw [ht.gpr, hu.other r (fun h => hr (by simp [h]))], by rw [ht.rd, hu.rd],
        by rw [ht.wr, hu.wr]⟩

theorem initSlot_ok {s : State} {base : Addr} (hs : Scr s base) (h4 : s.gpr .r4 = 0) {i : Nat}
    (hi : i < 22) :
    WP isa (.block (initSlot i)) s fun t =>
      (∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.r3] s t := by
  have hsl : slot i + 112 ≤ 4096 := by simp only [slot]; omega
  let inv := fun n (t : State) => (∀ k < n, limbs t.mem base (slot i) k = initLimb i k) ∧
    Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.r3] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (initStep_ok (hs.of_keeps tk (by decide)) ((tk.1 _ (by decide)).trans h4) hi hn)
    fun u ⟨um, uk⟩ => ⟨fun k hk => ?_, tm.trans ?_, tk.trans uk⟩
  · change (word u.mem base (slot i + 4 * k)).toNat = _
    rw [um, word_write t.mem base (by omega) (by omega)]
    by_cases h : k = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := initLimb_lt i n; omega)]
    · rw [ite_eq_right h]; exact tf k (by omega)
  · rw [um]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block initSlots) s fun t =>
      (∀ i < 22, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base 64 2816 s.mem t.mem ∧ Keeps [.r3, .r4] s t := by
  unfold initSlots
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  have hsu := hs.of_upd hu (by decide) (by decide)
  have ku : Keeps [.r3, .r4] s u := rest_keeps (hu.rest (by decide))
  let inv := fun n (t : State) => (∀ i < n, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
    Outside base 64 2816 u.mem t.mem ∧ Keeps [.r3] u t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 22
    (by decide) u ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨tf, tm, tk⟩ => ⟨tf, by rw [← hu.mem]; exact tm, ku.trans (tk.mono (by simp))⟩
  refine WP.mono (initSlot_ok (hsu.of_keeps tk (by decide)) ((tk.1 _ (by decide)).trans hu.gpr) hn)
    fun v ⟨vf, vm, vk⟩ => ⟨fun i hi k hk => ?_, tm.trans (vm.mono (by simp only [slot]; omega)
      (by simp only [slot]; omega)), tk.trans vk⟩
  by_cases h : i = n
  · subst h; exact vf k hk
  · rw [vm.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) hk]
    exact tf i (by omega) k hk

/-- The slots' values. -/
theorem initSlots_E {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) (i : Index) :
    E m base i = Proof.X448.toFe (initVal i.val) := by
  simp only [E, F, fe]
  rw [valN_congr (g := fun k => initVal i.val / 2 ^ (16 * k) % 65536) (h i.val i.isLt), valN_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans (initVal_lt _) (by decide +kernel))]

theorem initSlots_bounded {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) : BoundedEnv m base :=
  fun i k hk => by rw [h i.val i.isLt k hk]; exact initLimb_lt _ _

end VG.Proof.Ed448.Arm
