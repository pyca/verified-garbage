module
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context

import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the exponent's bits

The facts about `m` a context gives (`Context.odd`, `Context.coprime`), the
Montgomery forms of one and of the base (`mont_one`, `mont_encode`), a step of
the exponentiation (`exponent_step_value`), the mask of the exponent's low bit
(`exponentMask_ok`) and the exponent shifted down a bit (`shiftExponent_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp op2_imm op2_reg op2_lsr op2_lsl dpVal
  toNat_shr toNat_shl)

theorem Context.odd {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s) : m % 2 = 1 := by
  have hi := h.inverse
  have hmod : (m * w32 s.mem base invO + 1) % 2 = 0 := by omega
  rcases (by omega : m % 2 = 0 ∨ m % 2 = 1) with hm | hm
  · rw [Nat.add_mod, Nat.mul_mod, hm] at hmod; simp at hmod
  · exact hm

theorem Context.coprime {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s) :
    Nat.Coprime (2 ^ (64 * n)) m :=
  VG.Proof.Bignum.coprime_pow2 h.odd _

/-- The right-to-left exponentiation step consumes one bit. -/
theorem exponent_step_value (y b e : Nat) :
    (if e % 2 = 1 then y * b else y) * (b * b) ^ (e / 2) = y * b ^ e := by
  have he : e = e % 2 + 2 * (e / 2) := by omega
  have hp : b * b = b ^ 2 := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  rw [hp, ← Nat.pow_mul]
  have hpowe : b ^ e = b ^ (e % 2) * b ^ (2 * (e / 2)) := by
    rw [← Nat.pow_add]
    exact congrArg (b ^ ·) he
  rw [hpowe]
  rcases (by omega : e % 2 = 0 ∨ e % 2 = 1) with hm | hm
  · rw [hm]; simp
  · rw [hm]; simp only [ite_true, Nat.pow_one, Nat.mul_assoc]

theorem radix_squared (n : Nat) : 2 ^ (128 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) := by
  rw [← Nat.pow_add]; congr 1; omega

theorem mont_one {v n m : Nat} (hc : Nat.Coprime (2 ^ (64 * n)) m) (hv : v < m)
    (h : v * 2 ^ (64 * n) % m = 2 ^ (128 * n) % m) : v = 2 ^ (64 * n) % m := by
  have he : v % m = 2 ^ (64 * n) % m := VG.Proof.Bignum.mont_cancel hc (by rw [h, radix_squared])
  rwa [Nat.mod_eq_of_lt hv] at he

theorem mont_encode {v a n m : Nat} (hc : Nat.Coprime (2 ^ (64 * n)) m) (hv : v < m)
    (h : v * 2 ^ (64 * n) % m = a * (2 ^ (128 * n) % m) % m) : v = a * 2 ^ (64 * n) % m := by
  rw [radix_squared] at h
  have he := VG.Proof.Dsa.mont_scale hc h
  rwa [Nat.mod_eq_of_lt hv] at he

/-! ## The exponent's low bit -/

theorem lowBit_nat (x : BitVec 32) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]

theorem negative_lowBit (x : BitVec 32) :
    (0 : BitVec 32) - (x &&& 1) = if x.toNat % 2 = 1 then BitVec.allOnes 32 else 0 := by
  rcases (by omega : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1) with h | h
  · have e : x &&& 1 = 0 := by apply BitVec.eq_of_toNat_eq; rw [lowBit_nat, h]; rfl
    rw [e, h]; rfl
  · have e : x &&& 1 = 1 := by apply BitVec.eq_of_toNat_eq; rw [lowBit_nat, h]; rfl
    rw [e, h]; rfl

/-- `[maskO]` and `r3` all ones if the low bit of the exponent's word at `[exp]` is set, else zero. -/
theorem exponentMask_ok {n size : Nat} {base : Addr} {s : State} (hs : Ws s base size)
    (he : expS n + 4 ≤ size) (h16 : expS n < 2 ^ 16) (hm : 8 ≤ size) :
    WP isa (.block (exponentMask n)) s fun t => Ws t base size ∧
      w32 t.mem base maskO = (if w32 s.mem base (expS n) % 2 = 1 then BitVec.allOnes 32 else 0 : BitVec 32).toNat ∧
      Outside base maskO 4 s.mem t.mem ∧ Rest [.r1, .r3, .r4] s t := by
  unfold exponentMask
  refine wp_ptr (d := .r1) (by decide) h16 fun s₁ u₁ => ?_
  have w₁ := hs.of_upd u₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (d := 0) (K := expS n) (by rw [u₁.gpr, u₁.other .r12 (by decide)]) (by omega))
    (w₁.read (d := expS n + 0) (n := 4) (by omega)) fun s₂ u₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have w₅ := (((w₁.of_upd u₂ (by decide)).of_upd u₃ (by decide)).of_upd u₄ (by decide)).of_upd u₅ (by decide)
  refine wp_str (by decide) (w₅.ea12 (by simp only [maskO]; omega)) (w₅.write (d := maskO) (n := 4)
    (by simp only [maskO]; omega)) fun t m => WP.block_nil ⟨w₅.of_mupd m, ?_, ?_, ?_⟩
  · rw [m.mem, w32_write_self]
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte, dpVal, u₁.mem, Nat.add_zero]
    rw [negative_lowBit]
  · rw [m.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by decide)
  · exact ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans ((u₃.rest (by decide)).trans
      (u₄.rest (by decide)))).trans (u₅.rest (by decide))).trans (m.rest _)

/-! ## The exponent shifted down a bit -/

theorem shifted_word (x y : BitVec 32) :
    (x >>> 1 ||| y <<< 31).toNat = x.toNat / 2 + 2 ^ 31 * (y.toNat % 2) := by
  rw [BitVec.toNat_or, toNat_shr, toNat_shl]
  have hx := x.isLt
  have e : y.toNat * 2 ^ 31 % 2 ^ 32 = (y.toNat % 2) <<< 31 := by rw [Nat.shiftLeft_eq]; omega
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : x.toNat / 2 ^ 1 < 2 ^ 31), Nat.shiftLeft_eq]
  omega

theorem val32_parity (m : Mem) (base : Addr) (out n : Nat) : val32 m base out (n + 1) % 2 = w32 m base out % 2 := by
  rw [val32]; omega

/-- The `k` words at `[r1 + 4j]` (`r1 = r12 + E`) shifted down a bit. -/
theorem shiftWords_ok {E size : Nat} {base : Addr} :
    ∀ (k j : Nat) (s : State), Ws s base size → s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 E →
    E + 4 * (j + k) ≤ size → 4 * (j + k) ≤ 4096 →
    WP isa (.block (shiftWords k j)) s fun t => Ws t base size ∧
      Outside base (E + 4 * j) (4 * k) s.mem t.mem ∧
      val32 t.mem base (E + 4 * j) k = val32 s.mem base (E + 4 * j) k / 2 ∧ Rest [.r4, .r5] s t
  | 0, j, s, hs, _, _, _ => WP.block_nil ⟨hs, Outside.refl _ _ _ _, by simp only [val32, Nat.zero_div], Rest.refl _ _⟩
  | k + 1, j, s, hs, h1, hk, h4 => by
    have hnw := hs.nowrap
    rw [shiftWords]
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    refine wp_ldr (by omega) (hs.ea h1 (by omega)) (hs.read (by omega)) fun s₁ u₁ =>
      wp_mov (op2_lsr (by decide)) fun s₂ u₂ => ?_
    have w₂ := (hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)
    have e1 : s₂.gpr .r1 = s₂.gpr .r12 + BitVec.ofNat 32 E := by
      simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h1
    -- The word, with the next word's low bit on top.
    have main : WP isa (.block ((if k = 0 then [] else [.ldr .r5 .r1 (4 * j + 4), .mov .r5 (.shifted .r5 .lsl 31),
        .dp .orr .r4 .r4 (.reg .r5)]) ++ ([.str .r4 .r1 (4 * j)] ++ shiftWords k (j + 1)))) s₂ fun t =>
        Ws t base size ∧ Outside base (E + 4 * j) (4 * (k + 1)) s.mem t.mem ∧
        val32 t.mem base (E + 4 * j) (k + 1) = val32 s.mem base (E + 4 * j) (k + 1) / 2 ∧
        Rest [.r4, .r5] s t := by
      have r4₂ : (s₂.gpr .r4).toNat = w32 s.mem base (E + 4 * j) / 2 := by
        rw [u₂.gpr, toNat_shr, u₁.gpr]
      have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
      have R₂ : Rest [.r4, .r5] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
      -- After the word's value is in `r4`, with `v` its value.
      have fin : ∀ (s₃ : State) (v : Nat), Ws s₃ base size → s₃.mem = s.mem → Rest [.r4, .r5] s s₃ →
          (s₃.gpr .r4).toNat = v → v = w32 s.mem base (E + 4 * j) / 2 + 2 ^ 31 *
            (if k = 0 then 0 else w32 s.mem base (E + 4 * j + 4) % 2) →
          WP isa (.block ([.str .r4 .r1 (4 * j)] ++ shiftWords k (j + 1))) s₃ fun t =>
            Ws t base size ∧ Outside base (E + 4 * j) (4 * (k + 1)) s.mem t.mem ∧
            val32 t.mem base (E + 4 * j) (k + 1) = val32 s.mem base (E + 4 * j) (k + 1) / 2 ∧
            Rest [.r4, .r5] s t := by
        intro s₃ v w₃ m₃ R₃ r4 hv
        have e3 : s₃.gpr .r1 = s₃.gpr .r12 + BitVec.ofNat 32 E := by
          rw [R₃.gpr .r1 (by decide), R₃.gpr .r12 (by decide)]; exact h1
        simp only [List.cons_append, List.nil_append]
        refine wp_str (by omega) (w₃.ea e3 (by omega)) (w₃.write (by omega)) fun s₄ m₄ => ?_
        have w₄ := w₃.of_mupd m₄
        refine WP.mono (shiftWords_ok (E := E) k (j + 1) s₄ w₄ (by rw [m₄.gpr]; exact e3) (by omega) (by omega))
          fun t ⟨wt, O, V, R⟩ => ⟨wt, ?_, ?_, (R₃.trans (m₄.rest _)).trans R⟩
        · rw [m₄.mem, m₃] at O
          exact ((writeW32_outside _ _ _ (by omega)).mono (by omega) (by omega)).trans
            (O.mono (by omega) (by omega))
        · rw [m₄.mem, m₃, show E + 4 * (j + 1) = E + 4 * j + 4 by omega] at O V
          have head : w32 t.mem base (E + 4 * j) = v := by
            rw [O.w32 (by omega) (by omega), w32_write_self, r4]
          rw [val32, val32, head, V]
          have tail : val32 (s.mem.writeW (off base (E + 4 * j)) (s₃.gpr .r4)) base (E + 4 * j + 4) k =
              val32 s.mem base (E + 4 * j + 4) k :=
            (writeW32_outside s.mem base (d := E + 4 * j) (s₃.gpr .r4) (by omega)).val32 (by omega) (by omega)
          rw [tail, hv]
          cases k with
          | zero => simp only [val32, ↓reduceIte]; omega
          | succ k =>
            have hp := val32_parity s.mem base (E + 4 * j + 4) k
            simp only [Nat.add_one_ne_zero, ↓reduceIte]
            omega
      by_cases hk0 : k = 0
      · subst hk0
        simp only [↓reduceIte, List.nil_append]
        exact fin s₂ _ w₂ m₂ R₂ r4₂ (by simp)
      · simp only [hk0, ↓reduceIte, List.cons_append, List.nil_append]
        refine wp_ldr (by omega) (w₂.ea e1 (by omega)) (w₂.read (by omega)) fun s₃ u₃ =>
          wp_mov (op2_lsl (by decide)) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
        refine fin s₅ _ ((((w₂.of_upd u₃ (by decide)).of_upd u₄ (by decide))).of_upd u₅ (by decide))
          (by rw [u₅.mem, u₄.mem, u₃.mem, m₂]) (R₂.trans (((u₃.rest (by decide)).trans (u₄.rest (by decide))).trans
            (u₅.rest (by decide)))) rfl ?_
        simp only [u₅.get, u₄.get, u₃.get, reduceCtorEq, ↓reduceIte, dpVal]
        rw [u₂.gpr, shifted_word, u₁.gpr, u₂.mem, u₁.mem, show E + (4 * j + 4) = E + 4 * j + 4 by omega]
        simp only [hk0, ↓reduceIte]
    exact main

end VG.Proof.Mont.Arm.Dyn
