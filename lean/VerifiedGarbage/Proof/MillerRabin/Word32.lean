module

public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Bignum.Math

/-!
# Prepared Miller–Rabin arithmetic with native 32-bit words

The round runs Miller–Rabin by windows of four bits
(`Proof/RsaKeyGen/MrWindow.lean`) in Montgomery form: a product of `x` and
`y` is `mm c w x y = x y R⁻¹ mod c`, with `R⁻¹ = ((c + 1) / 2)^(64 w) mod
c` the inverse of `R = 2^(64 w)` (`mm_eq`). From the witness `X`,
Montgomery one `O` and minus one `M`: the table `tp` of the powers of `X`;
a run of squarings (`msqs`), each or'ing the flag with `y = M` while the
threshold `r` is below the run's count; a window (`mwin`) and the windows of
the exponent from the top (`mrun`). For any `b` with `X = b R mod c` they
are `wSq`, `wWin` and `wRun` in Montgomery form (`msq_rel`, `mwin_rel`,
`mrun_rel`), and the flag after the windows and three squarings with the
threshold `4 − σ` is the round's result (`final_eq`).

The words: the digit of a window from a word shifted left four bits a
window (`shl_shr28`, `digit_word`), the masks the code computes
(`mask_lt`, `mask_eq`, `mask_zero`, `flag_bits`), and `4 − σ` from the word
`2^(t mod 64)` (`foldR_eq`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.Word32
open VG.Spec.RsaKeyGen VG.Spec.Rsa VG.Proof.RsaKeyGen

/-! ## Montgomery products -/

/-- The inverse of `2^(64 w)` modulo the odd `c`. -/
def rinv (c w : Nat) : Nat := ((c + 1) / 2) ^ (64 * w) % c

/-- `x y R⁻¹ mod c`. -/
def mm (c w x y : Nat) : Nat := x * y * rinv c w % c

theorem R_rinv {c w : Nat} (hc : c % 2 = 1) : 2 ^ (64 * w) * rinv c w % c = 1 % c := by
  unfold rinv
  rw [Nat.mul_mod_mod, ← Nat.mul_pow, Nat.pow_mod, show 2 * ((c + 1) / 2) = c + 1 by omega,
    show (c + 1) % c = 1 % c by rw [Nat.add_mod_left], ← Nat.pow_mod, Nat.one_pow]

/-- The value of a Montgomery product. -/
theorem mm_eq {c w T x y : Nat} (hc : c % 2 = 1) (hT : T < c) (h : T * 2 ^ (64 * w) % c = x * y % c) :
    T = mm c w x y := by
  unfold mm
  have e : T % c = T * (2 ^ (64 * w) * rinv c w) % c := by
    rw [Nat.mul_mod, R_rinv hc, ← Nat.mul_mod, Nat.mul_one]
  rw [← Nat.mod_eq_of_lt hT, e, ← Nat.mul_assoc, Nat.mul_mod, h, ← Nat.mul_mod]

/-- The product of two Montgomery forms. -/
theorem mm_val {c w x z : Nat} (hc : c % 2 = 1) :
    mm c w (x * 2 ^ (64 * w) % c) (z * 2 ^ (64 * w) % c) = x * z % c * 2 ^ (64 * w) % c := by
  unfold mm
  generalize hR : 2 ^ (64 * w) = R
  have r := R_rinv (w := w) hc
  rw [hR] at r
  rw [Nat.mul_mod (x * R % c * (z * R % c)), ← Nat.mul_mod (x * R) (z * R), ← Nat.mul_mod,
    Nat.mul_mod (x * z % c) R, Nat.mod_mod, ← Nat.mul_mod,
    show x * R * (z * R) * rinv c w = x * z * R * (R * rinv c w) by
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm],
    Nat.mul_mod (x * z * R), r, ← Nat.mul_mod, Nat.mul_one]

theorem mm_lt {c w x y : Nat} (hc : 0 < c) : mm c w x y < c := Nat.mod_lt _ hc

/-! ## The table -/

/-- The powers of `X`, from `O`. -/
def tp (c w X O : Nat) : Nat → Nat
  | 0 => O
  | 1 => X
  | k + 2 => mm c w (tp c w X O (k + 1)) X

theorem tp_val {c w b X O : Nat} (hc : c % 2 = 1) (hc3 : 3 ≤ c) (hX : X = b % c * 2 ^ (64 * w) % c)
    (hO : O = 2 ^ (64 * w) % c) : ∀ k, tp c w X O k = powMod b k c * 2 ^ (64 * w) % c
  | 0 => by
    have h1 : 1 % c = 1 := Nat.mod_eq_of_lt (by omega)
    rw [tp, hO, VG.Proof.Bignum.powMod_eq, Nat.pow_zero, h1, Nat.one_mul]
  | 1 => by rw [tp, hX, VG.Proof.Bignum.powMod_eq, Nat.pow_one]
  | k + 2 => by
    rw [tp, tp_val hc hc3 hX hO (k + 1), hX, mm_val hc, VG.Proof.Bignum.powMod_eq, VG.Proof.Bignum.powMod_eq,
      ← Nat.mul_mod, ← Nat.pow_succ]

theorem tp_lt {c w X O : Nat} (hc : 0 < c) (hX : X < c) (hO : O < c) : ∀ k, tp c w X O k < c
  | 0 => hO
  | 1 => hX
  | _ + 2 => mm_lt hc

/-! ## Squarings and windows -/

/-- A squaring, the flag or'ed with `y = M` if `m`. -/
def msq (c w M : Nat) (m : Bool) (st : Nat × Bool) : Nat × Bool :=
  (mm c w st.1 st.1, st.2 || (m && decide (mm c w st.1 st.1 = M)))

/-- `k` squarings of a run of `q0` with the threshold `r`: the `i`th or's the
flag if `r < q0 − i`. -/
def msqs (c w M r q0 : Nat) (st : Nat × Bool) : Nat → Nat × Bool
  | 0 => st
  | k + 1 => msq c w M (decide (r < q0 - k)) (msqs c w M r q0 st k)

/-- A window with digit `d`, the table `T`. -/
def mwin (c w M : Nat) (T : Nat → Nat) (d : Nat) (st : Nat × Bool) : Nat × Bool :=
  (mm c w (msqs c w M 0 4 st 4).1 (T d),
    if d = 0 then (msqs c w M 0 4 st 4).2 else
      (decide (mm c w (msqs c w M 0 4 st 4).1 (T d) = T 0) ||
        decide (mm c w (msqs c w M 0 4 st 4).1 (T d) = M)))

/-- The top `j` of the `W` windows of `E`. -/
def mrun (c w M : Nat) (T : Nat → Nat) (E W : Nat) : Nat → Nat × Bool
  | 0 => (T 0, false)
  | j + 1 => mwin c w M T (E / 16 ^ (W - 1 - j) % 16) (mrun c w M T E W j)

/-! ## In Montgomery form -/

section
variable {c w b M : Nat}

theorem msq_rel (hc : c % 2 = 1) (hc3 : 3 ≤ c) (hM : M = c - 2 ^ (64 * w) % c) (y : Nat)
    (m F : Bool) :
    msq c w M m (y * 2 ^ (64 * w) % c, F) =
      ((wSq c m (y, F)).1 * 2 ^ (64 * w) % c, (wSq c m (y, F)).2) := by
  have hR := VG.Proof.Bignum.coprime_pow2 hc (64 * w)
  unfold msq wSq
  simp only
  rw [mm_val hc, hM, decide_eq_decide.mpr (mont_eq_m1 hR (by omega) (Nat.mod_lt _ (by omega)))]

/-- Four squarings of a window. -/
theorem msqs4_rel (hc : c % 2 = 1) (hc3 : 3 ≤ c) (hM : M = c - 2 ^ (64 * w) % c) (y : Nat) (F : Bool) :
    msqs c w M 0 4 (y * 2 ^ (64 * w) % c, F) 4 =
      ((wSq c true (wSq c true (wSq c true (wSq c true (y, F))))).1 * 2 ^ (64 * w) % c,
        (wSq c true (wSq c true (wSq c true (wSq c true (y, F))))).2) := by
  simp only [msqs, show decide (0 < 4 - 0) = true from rfl, show decide (0 < 4 - 1) = true from rfl,
    show decide (0 < 4 - 2) = true from rfl, show decide (0 < 4 - 3) = true from rfl]
  rw [msq_rel hc hc3 hM, msq_rel hc hc3 hM, msq_rel hc hc3 hM, msq_rel hc hc3 hM]

/-- A window. -/
theorem mwin_rel (hc : c % 2 = 1) (hc3 : 3 ≤ c) (hM : M = c - 2 ^ (64 * w) % c) {T : Nat → Nat}
    (hT : ∀ k < 16, T k = powMod b k c * 2 ^ (64 * w) % c) {d : Nat} (hd : d < 16) (y : Nat) (F : Bool) :
    mwin c w M T d (y * 2 ^ (64 * w) % c, F) =
      ((wWin c b d (y, F)).1 * 2 ^ (64 * w) % c, (wWin c b d (y, F)).2) := by
  have hR := VG.Proof.Bignum.coprime_pow2 hc (64 * w)
  unfold mwin wWin
  rw [msqs4_rel hc hc3 hM, hT d hd, mm_val hc]
  generalize wSq c true (wSq c true (wSq c true (wSq c true (y, F)))) = s
  have lt : s.1 * powMod b d c % c < c := Nat.mod_lt _ (by omega)
  have h1 : 1 % c = 1 := Nat.mod_eq_of_lt (by omega)
  have t0 : T 0 = 2 ^ (64 * w) % c := by
    rw [hT 0 (by decide), VG.Proof.Bignum.powMod_eq, Nat.pow_zero, h1, Nat.one_mul]
  simp only [t0, hM]
  rw [decide_eq_decide.mpr (mont_eq_one hR (by omega) lt), decide_eq_decide.mpr (mont_eq_m1 hR (by omega) lt)]

/-- The windows. -/
theorem mrun_rel (hc : c % 2 = 1) (hc3 : 3 ≤ c) (hM : M = c - 2 ^ (64 * w) % c) {T : Nat → Nat}
    (hT : ∀ k < 16, T k = powMod b k c * 2 ^ (64 * w) % c) (E W : Nat) :
    ∀ j, mrun c w M T E W j = ((wRun c b E W j).1 * 2 ^ (64 * w) % c, (wRun c b E W j).2) ∧
      (wRun c b E W j).1 < c
  | 0 => by
    refine ⟨?_, by show 1 < c; omega⟩
    have h1 : 1 % c = 1 := Nat.mod_eq_of_lt (by omega)
    simp only [mrun, wRun, Nat.one_mul]
    rw [hT 0 (by decide), VG.Proof.Bignum.powMod_eq, Nat.pow_zero, h1, Nat.one_mul]
  | j + 1 => by
    obtain ⟨ih, lt⟩ := mrun_rel hc hc3 hM hT E W j
    rw [mrun, wRun, ih]
    refine ⟨mwin_rel hc hc3 hM hT (Nat.mod_lt _ (by decide)) _ _, ?_⟩
    exact Nat.mod_lt _ (by omega)

end

/-! ## The round's result -/

theorem mrA_le {c : Nat} (hc3 : 3 ≤ c) : mrA c ≤ bitLength c - 1 := by
  obtain ⟨hN, _⟩ := splitTwos_spec (c - 1) (by omega)
  change c - 1 = (splitTwos (c - 1)).2 * 2 ^ mrA c at hN
  have hm : 0 < (splitTwos (c - 1)).2 := by
    rcases Nat.eq_zero_or_pos (splitTwos (c - 1)).2 with h | h
    · rw [h, Nat.zero_mul] at hN; omega
    · exact h
  have h2a : 2 ^ mrA c ≤ c := by
    have := Nat.le_mul_of_pos_left (2 ^ mrA c) hm; omega
  have e : bitLength c = c.log2 + 1 := by unfold bitLength; split <;> omega
  rw [e, Nat.add_sub_cancel]
  exact (Nat.le_log2 (by omega)).mpr h2a

/-- The windows of `E` and three squarings with the threshold `4 − σ`: the round. -/
theorem final_eq {c w b X O M : Nat} (hc : c % 2 = 1) (hc3 : 3 ≤ c) (hcR : c < 2 ^ (64 * w))
    (hX : X = b % c * 2 ^ (64 * w) % c) (hO : O = 2 ^ (64 * w) % c) (hM : M = c - 2 ^ (64 * w) % c) :
    (msqs c w M (4 - sigOf (mrA c)) 3 (mrun c w M (tp c w X O) (mrE c) (16 * w) (16 * w)) 3).2 =
      Proof.MillerRabin.Round.round c b := by
  have hT : ∀ k < 16, tp c w X O k = powMod b k c * 2 ^ (64 * w) % c := fun k _ => tp_val hc hc3 hX hO k
  obtain ⟨hr, lt⟩ := mrun_rel (b := b) hc hc3 hM hT (mrE c) (16 * w) (16 * w)
  rw [hr]
  have hs := sigOf_pos (mrA c)
  have m1 : decide (4 - sigOf (mrA c) < 3 - 0) = decide (1 < mrSig c) :=
    decide_eq_decide.mpr (by show _ ↔ 1 < sigOf (mrA c); omega)
  have m2 : decide (4 - sigOf (mrA c) < 3 - 1) = decide (2 < mrSig c) :=
    decide_eq_decide.mpr (by show _ ↔ 2 < sigOf (mrA c); omega)
  have m3 : decide (4 - sigOf (mrA c) < 3 - 2) = decide (3 < mrSig c) :=
    decide_eq_decide.mpr (by show _ ↔ 3 < sigOf (mrA c); omega)
  simp only [msqs, m1, m2, m3]
  rw [msq_rel hc hc3 hM, msq_rel hc hc3 hM, msq_rel hc hc3 hM]
  show (wEnd c (wRun c b (mrE c) (16 * w) (16 * w))).2 = _
  rw [wEnd_eq b hc3 hc (mrA_le hc3) ?_]
  · rfl
  · have : mrE c ≤ c - 1 := Nat.div_le_self _ _
    rw [sixteen_pow, show 4 * (16 * w) = 64 * w by omega]
    omega

/-! ## Words and digits -/

/-- The digit at the top of a word shifted left by `4 t`: digit `7 − t`. -/
theorem shl_shr28 (x : BitVec 32) {t : Nat} (ht : t < 8) :
    ((x <<< (4 * t)) >>> 28).toNat = x.toNat / 2 ^ (28 - 4 * t) % 2 ^ 4 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow]
  by_cases hi : i < 4
  · simp only [show i + 28 < 32 by omega, hi, decide_true, Bool.true_and, show 4 * t ≤ i + 28 by omega]
    congr 1; omega
  · simp only [show ¬ i + 28 < 32 by omega, hi, decide_false, Bool.false_and]

theorem shl4_succ32 (x : BitVec 32) (t : Nat) : x <<< (4 * t) <<< 4 = x <<< (4 * (t + 1)) := by
  rw [← BitVec.shiftLeft_add, show 4 * t + 4 = 4 * (t + 1) by omega]

/-- The digit `8 i + p` of `E` is the digit `p` of its 32-bit word `i`. -/
theorem digit_word (E i p : Nat) (hp : p < 8) :
    E / 2 ^ (32 * i) % 2 ^ 32 / 2 ^ (4 * p) % 2 ^ 4 = E / 16 ^ (8 * i + p) % 16 := by
  rw [mod_div_mod (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add, sixteen_pow,
    show 32 * i + 4 * p = 4 * (8 * i + p) by omega]

/-- `(r − q) >> 31` for small `r` and `q`: whether `r < q`. -/
theorem mask_lt {r q : Nat} (hr : r < 2 ^ 31) (hq : q < 2 ^ 31) :
    ((BitVec.ofNat 32 r - BitVec.ofNat 32 q) >>> 31).toNat = (decide (r < q)).toNat := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (a := r) (by omega), Nat.mod_eq_of_lt (a := q) (by omega)]
  by_cases h : r < q
  · simp only [h, decide_true, Bool.toNat_true]
    rw [show 2 ^ 32 - q + r = 2 ^ 32 - (q - r) by omega, Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [h, decide_false, Bool.toNat_false]
    rw [show 2 ^ 32 - q + r = (r - q) + 2 ^ 32 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The scan's mask: `((d ⊕ j) − 1) >> 31` is whether the digit `d` is `j`. -/
theorem mask_eq : ∀ d < 16, ∀ j < 16,
    (((BitVec.ofNat 32 d ^^^ BitVec.ofNat 32 j) - 1) >>> 31).toNat = (decide (d = j)).toNat := by
  decide

/-- `(d − 1) >> 31`: whether the digit `d` is 0. -/
theorem mask_zero : ∀ d < 16, ((BitVec.ofNat 32 d - 1) >>> 31).toNat = (decide (d = 0)).toNat := by
  decide

/-- The flag after a window: `(e₁ ∨ e₂) ∧ d ≠ 0`, or the flag if `d = 0`. -/
theorem flag_bits (z e1 e2 F : Bool) :
    ((((BitVec.ofNat 32 e1.toNat ||| BitVec.ofNat 32 e2.toNat) &&& (BitVec.ofNat 32 z.toNat ^^^ 1)) |||
      (BitVec.ofNat 32 F.toNat &&& BitVec.ofNat 32 z.toNat))).toNat = (if z then F else (e1 || e2)).toNat := by
  cases z <;> cases e1 <;> cases e2 <;> cases F <;> decide

/-- `4 − σ` from the halves of `2^k`: the halves or'ed, folded to four bits. -/
def foldR (lo hi : BitVec 32) : BitVec 32 :=
  let x1 := lo ||| hi
  let x2 := x1 ||| x1 >>> 16
  let x3 := x2 ||| x2 >>> 8
  let x4 := x3 ||| x3 >>> 4
  (x4 >>> 3 &&& 1) + (x4 >>> 1 &&& 1) + ((x4 >>> 1 &&& 1) <<< 1) + ((x4 >>> 2 &&& 1) <<< 1)

theorem foldR_eq : ∀ k < 64,
    foldR (BitVec.ofNat 32 (2 ^ k % 2 ^ 32)) (BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) = BitVec.ofNat 32 (4 - sigOf k) := by
  decide

end VG.Proof.MillerRabin.Word32
