import VerifiedGarbage.Proof.Mont.Arm.Ops

/-!
# Constants in the working space, on 32-bit ARM

`setConst_ok`: `setConst n o x` stores the `n`-word number `x` at `[o]`,
a 32-bit word at a time, each from a `movw` and a `movt`.
-/

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_str wp_movw)

/-- The words of `x`, word by word, are `x`. -/
theorem val32_of_shifts (m : Mem) (base : Addr) : ∀ (o k x : Nat), x < 2 ^ (32 * k) →
    (∀ j < k, w32 m base (o + 4 * j) = (x >>> (32 * j)) % 2 ^ 32) → val32 m base o k = x
  | _, 0, x, hx, _ => by simp only [Nat.mul_zero, Nat.pow_zero] at hx; simp only [val32]; omega
  | o, k + 1, x, hx, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.shiftRight_zero] at h0
    have hr := val32_of_shifts m base (o + 4) k (x >>> 32) (by
        rw [Nat.shiftRight_eq_div_pow]
        rw [pow32_succ] at hx
        exact Nat.div_lt_of_lt_mul hx) fun j hj => by
      rw [show o + 4 + 4 * j = o + 4 * (j + 1) by omega, h (j + 1) (by omega), ← Nat.shiftRight_add,
        show 32 + 32 * j = 32 * (j + 1) by omega]
    rw [val32, hr, h0, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_add_div x _

/-- `movw` and `movt` of the halves of `x`. -/
theorem movImm_val (x : Nat) :
    (BitVec.ofNat 16 (x >>> 16) ++ ((BitVec.ofNat 16 x).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

theorem wp_movt {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- One word of `setConst`. -/
def constStep (o x j : Nat) : List Instr := movImm (x >>> (32 * j)) ++ [.str .r4 wb (o + 4 * j)]

theorem setConst_eq (n o x : Nat) : setConst n o x = (List.range (2 * n)).flatMap (constStep o x) := rfl

theorem constSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o x : Nat} :
    ∀ k, o + 4 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (constStep o x))) s fun s' =>
      (∀ j < k, w32 s'.mem base (o + 4 * j) = (x >>> (32 * j)) % 2 ^ 32) ∧
      Rest [.r4] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (constSteps_ok hs k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    simp only [constStep, movImm, List.cons_append, List.nil_append]
    refine wp_movw fun s₂ u₂ => wp_movt fun s₃ u₃ => ?_
    have k₃ : Rest [.r4] s s₃ := k₁.trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
    have hs₃ := hs.of_rest k₃ (by decide)
    refine wp_str (hs.off_lt (by omega)) (hs₃.ea (by omega)) (hs₃.write (d := o + 4 * k) (n := 4) (by omega))
      fun s₄ m₄ => WP.block_nil ?_
    have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₄.mem := by
      rw [m₄.mem, u₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₃.trans (m₄.rest _),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.w32 (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₄.mem, u₃.mem, u₂.mem, w32_write_self, u₃.gpr, u₂.gpr, movImm_val, BitVec.toNat_ofNat]

/-- `[o] = x`. -/
theorem setConst_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o x : Nat}
    (ho : o + 8 * n ≤ size) (hx : x < 2 ^ (64 * n)) :
    WP isa (.block (setConst n o x)) s fun s' =>
      wordsVal s'.mem base o n = x ∧ Rest [.r4] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [setConst_eq]
  refine WP.mono (constSteps_ok hs (2 * n) (by omega)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, by rw [show 8 * n = 4 * (2 * n) by omega]; exact O⟩
  rw [wordsVal_eq_val32]
  exact val32_of_shifts _ _ o (2 * n) x (by rw [show 32 * (2 * n) = 64 * n by omega]; exact hx) e

end VG.Proof.Weierstrass.Arm
