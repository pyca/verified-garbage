module
-- separate module: target-independent, for every target's lazy steps of long division (RISC-V's now)
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Multiword arithmetic: lazy steps of long division, 63 bits at a time

The arithmetic of long division (Knuth, TAOCP vol. 2, §4.3.1, Algorithm D)
whose remainder is kept in `[0, 2 m)` rather than reduced, independent of the
target. The number of a step is `V = r 2^63 + c` for the remainder
`r < 2 m` and the next 63-bit digit `c` of the dividend, so that
`V < m 2^64`, as an estimate of `⌊V / m⌋` from the top words needs; then
`WordDiv.lean`'s `wordDiv_step` with `W = 63` is the recurrence:

* `dec_bounds`: an estimate `q ≤ q̂ ≤ q + 1` lowered by one unless it is 0 is
  `q - 1 ≤ q̂ ≤ q`;
* `lazy_step`: and then `t = V - q̂ m` computed modulo `2^K` (with its
  borrow) needs no correction: `t < 2 m` and `t ≡ V` modulo `m`;
* `shr_or_shl`, `shr_words`: a word of a number shifted right by `s < 64`
  bits, from two of its words, which is how the digits are read and how
  `V / 2^63` is written back.
-/

@[expose] public section

namespace VG.Proof.Bignum.WordStep

/-- The estimate lowered by one unless it is 0. -/
theorem dec_bounds {q q0 : Nat} (h1 : q ≤ q0) (h2 : q0 ≤ q + 1) :
    q0 - (if 0 < q0 then 1 else 0) ≤ q ∧ q ≤ q0 - (if 0 < q0 then 1 else 0) + 1 := by
  split <;> omega

/-- A lazy step: for `q̂` with `q - 1 ≤ q̂ ≤ q`, `q = ⌊y / m⌋`, `t = y - q̂ m`
modulo `2^K` (`t + q̂ m = y + 2^K b`, `b` the borrow) is `y - q̂ m`
itself, below `2 m` and congruent to `y`. -/
theorem lazy_step {Y M qh T b K : Nat} (hM : 0 < M) (hle : qh ≤ Y / M)
    (hge : Y / M ≤ qh + 1) (hT : T < 2 ^ K) (hb : b < 2) (h : T + qh * M = Y + 2 ^ K * b) :
    T + qh * M = Y ∧ T < 2 * M ∧ T % M = Y % M := by
  have e : T + qh * M = Y := by
    have hd := Nat.div_add_mod Y M
    have hm := Nat.mod_lt Y hM
    have h1 : qh * M ≤ M * (Y / M) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left M hle
    have h2 : M * (Y / M) ≤ qh * M + M := by
      rw [Nat.mul_comm qh, ← Nat.mul_succ]; exact Nat.mul_le_mul_left M hge
    generalize M * (Y / M) = A at hd h1 h2
    generalize qh * M = Q at h h1 h2 ⊢
    have hb0 : b = 0 := by
      rcases Nat.lt_or_ge b 1 with e | e
      · omega
      · have : 2 ^ K ≤ 2 ^ K * b := Nat.le_mul_of_pos_right _ e
        omega
    subst hb0
    omega
  refine ⟨e, ?_, by rw [← e, Nat.add_mul_mod_self_right]⟩
  have hd := Nat.div_add_mod Y M
  have hm := Nat.mod_lt Y hM
  have h2 : M * (Y / M) ≤ qh * M + M := by
    rw [Nat.mul_comm qh, ← Nat.mul_succ]; exact Nat.mul_le_mul_left M hge
  omega

/-- `(x >> s) | (y << t)`, `s + t = 64`, is `x / 2^s + (y mod 2^s) 2^t`. -/
theorem shr_or_shl (x y : BitVec 64) {s t : Nat} (hst : s + t = 64) :
    ((x >>> s) ||| (y <<< t)).toNat = x.toNat / 2 ^ s + y.toNat % 2 ^ s * 2 ^ t := by
  have hx := x.isLt
  have e64 : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ t := by rw [← Nat.pow_add, hst]
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, e64, Nat.mul_mod_mul_right]
  have hlt : x.toNat / 2 ^ s < 2 ^ t := Nat.div_lt_of_lt_mul (by rw [← e64]; exact hx)
  rw [Nat.or_comm, Nat.mul_comm (y.toNat % 2 ^ s), ← Nat.two_pow_add_eq_or_of_lt hlt]
  omega

/-- Word `J` of `X` shifted right by `s < 64` bits, from `X`'s words `J` and
`J + 1`. -/
theorem shr_words (X J : Nat) {s : Nat} (hs : s < 64) :
    X / 2 ^ (64 * J + s) % 2 ^ 64 =
      X / 2 ^ (64 * J) % 2 ^ 64 / 2 ^ s + X / 2 ^ (64 * (J + 1)) % 2 ^ 64 % 2 ^ s * 2 ^ (64 - s) := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
  generalize hY : X / 2 ^ (64 * J) = Y
  have hH : X / 2 ^ (64 * (J + 1)) = Y / 2 ^ 64 := by
    rw [← hY, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]
  have hS : X / 2 ^ (64 * J + s) = Y / 2 ^ s := by
    rw [← hY, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [hH, hS, Nat.mod_mod_of_dvd _ (by rw [e64]; exact Nat.dvd_mul_right _ _)]
  have hY' := Nat.div_add_mod Y (2 ^ 64)
  generalize Y / 2 ^ 64 = H at hY' ⊢
  generalize hL : Y % 2 ^ 64 = L at hY'
  have hLt : L < 2 ^ 64 := hL ▸ Nat.mod_lt _ (by decide)
  rw [← hY', show 2 ^ 64 * H + L = 2 ^ s * (2 ^ (64 - s) * H) + L by rw [e64, Nat.mul_assoc],
    Nat.mul_add_div (Nat.two_pow_pos s)]
  have hl : L / 2 ^ s < 2 ^ (64 - s) := Nat.div_lt_of_lt_mul (by rw [← e64]; exact hLt)
  have hH := Nat.div_add_mod H (2 ^ s)
  generalize H / 2 ^ s = A at hH
  generalize hb : H % 2 ^ s = b at hH ⊢
  have hbl : b < 2 ^ s := hb ▸ Nat.mod_lt _ (Nat.two_pow_pos s)
  have hlow : b * 2 ^ (64 - s) + L / 2 ^ s < 2 ^ 64 := by
    have := Nat.mul_le_mul_right (2 ^ (64 - s)) (show b + 1 ≤ 2 ^ s by omega)
    rw [Nat.add_mul, Nat.one_mul, ← e64] at this
    omega
  have hx : 2 ^ (64 - s) * H = 2 ^ 64 * A + b * 2 ^ (64 - s) := by
    rw [← hH, Nat.mul_add, e64, Nat.mul_left_comm, Nat.mul_comm b, Nat.mul_assoc]
  rw [hx, Nat.add_assoc, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow, Nat.add_comm]

end VG.Proof.Bignum.WordStep
