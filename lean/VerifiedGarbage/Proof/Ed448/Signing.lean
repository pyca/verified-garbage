import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Impl.Ed448.Formulas
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Framework.PowLit

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.VerifyFormulas`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Scalar`. -/
section

/-!
# Ed448 scalar arithmetic: the numbers

`L = 2^446 - c` with `c < 2^224`. Folding a word into a remainder below `L`
(`fold_nat`) leaves a value below `2L` and congruent to it; a conditional
subtraction (`csub_nat`) then leaves the remainder. The bytes of the
specification are X25519's little-endian numbers (`decodeLE_eq`).
-/

namespace VG.Proof.Ed448

open VG VG.Spec.Ed448

/-- `c = 2^446 - L`. -/
def cL : Nat := 13818066809895115352007386748515426880336692474882178609894547503885

theorem L_add : L + VG.Proof.Ed448.cL = 2 ^ 446 := by decide +kernel
theorem cL_lt : VG.Proof.Ed448.cL < 2 ^ 224 := by decide +kernel
theorem L_pos : 0 < L := by decide +kernel
theorem L_lt : L < 2 ^ 446 := by decide +kernel
theorem K_eq : 2 ^ 448 - L = 3 * 2 ^ 446 + VG.Proof.Ed448.cL := by decide +kernel

theorem L_lit : L = 181709681073901722637330951972001133588410340171829515070372549795146003961539585716195755291692375963310293709091662304773755859649779 := by
  decide +kernel

/-- One word folded in, on words (exponents above 256 stay unevaluated, so
the numbers are written with nested factors `2^64`): the remainder
`r = (r₀, …, r₆) < L` and the next word `w` give `v = w + 2^64 r =
h 2^446 + l`, with `l = (w, r₀, …, r₄, r₅ mod 2^62)` and
`h = r₅ / 2^62 + 4 r₆`; then `l + h c` is below `2L` and congruent to `v`
modulo `L`. -/
theorem fold_words (w r0 r1 r2 r3 r4 r5 r6 : Nat) (hw : w < 2 ^ 64) (h0 : r0 < 2 ^ 64)
    (h1 : r1 < 2 ^ 64) (h2 : r2 < 2 ^ 64) (h3 : r3 < 2 ^ 64) (h4 : r4 < 2 ^ 64)
    (h5 : r5 < 2 ^ 64) (h6 : r6 < 2 ^ 64)
    (hr : r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 + 2 ^ 64 * (r4 + 2 ^ 64 *
      (r5 + 2 ^ 64 * r6))))) < L) :
    let l := w + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 + 2 ^ 64 *
      (r4 + 2 ^ 64 * (r5 % 2 ^ 62))))))
    let h := r5 / 2 ^ 62 + 4 * r6
    r6 < 2 ^ 62 ∧ h < 2 ^ 64 ∧ l + h * VG.Proof.Ed448.cL < 2 * L ∧
      (l + h * VG.Proof.Ed448.cL) % L = (w + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 +
        2 ^ 64 * (r4 + 2 ^ 64 * (r5 + 2 ^ 64 * r6))))))) % L := by
  obtain ⟨m, q, rfl, hm⟩ : ∃ m q, r5 = m + 2 ^ 62 * q ∧ m < 2 ^ 62 :=
    ⟨_, _, (Nat.mod_add_div r5 (2 ^ 62)).symm, Nat.mod_lt r5 (by decide)⟩
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm, Nat.add_mul_div_left _ _ (by decide),
    Nat.div_eq_of_lt hm, Nat.zero_add]
  dsimp only
  have h6' : r6 < 2 ^ 62 := by omega_using [hr, VG.Proof.Ed448.L_lt]
  have hh : q + 4 * r6 < 2 ^ 64 := by omega_using [h5, h6, h6']
  have hhc : (q + 4 * r6) * VG.Proof.Ed448.cL < 2 ^ 64 * 2 ^ 224 := Nat.mul_lt_mul'' hh VG.Proof.Ed448.cL_lt
  have e : w + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 + 2 ^ 64 * (r4 +
      2 ^ 64 * (m + 2 ^ 62 * q + 2 ^ 64 * r6)))))) =
      (w + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 + 2 ^ 64 * (r4 + 2 ^ 64 * m))))) +
        (q + 4 * r6) * VG.Proof.Ed448.cL) + (q + 4 * r6) * L := by
    have e' : w + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 + 2 ^ 64 * (r4 +
        2 ^ 64 * (m + 2 ^ 62 * q + 2 ^ 64 * r6)))))) =
        w + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 + 2 ^ 64 * (r4 + 2 ^ 64 * m))))) +
          (q + 4 * r6) * 2 ^ 446 := by omega_using []
    rw [e', ← VG.Proof.Ed448.L_add, Nat.mul_add (q + 4 * r6) L VG.Proof.Ed448.cL, ← Nat.add_assoc, Nat.add_right_comm]
  refine ⟨h6', hh, by omega_using [VG.Proof.Ed448.L_add, VG.Proof.Ed448.cL_lt, hhc, hm, hw, h0, h1, h2, h3, h4], ?_⟩
  rw [e, Nat.add_mul_mod_self_right]

/-- The conditional subtraction: `K = M - L` added to `x < 2L` carries out of
`M` (`2^448`) exactly when `x ≥ L`, and then the sum is `x - L`. -/
theorem csub_nat {M x y : Nat} {c : Bool} (hM : 2 * L ≤ M) (hx : x < 2 * L) (hy : y < M)
    (he : y + M * c.toNat = x + (M - L)) :
    (if c then y else x) = x % L := by
  have hL := VG.Proof.Ed448.L_pos
  cases c with
  | false =>
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at he
    rw [ite_eq_right Bool.false_ne_true, Nat.mod_eq_of_lt (by omega)]
  | true =>
    simp only [Bool.toNat_true, Nat.mul_one] at he
    rw [ite_eq_left rfl, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- Folding a word into the remainder of the words above it. -/
theorem mod_step (a w : Nat) : (a % L * 2 ^ 64 + w) % L = (w + 2 ^ 64 * a) % L := by
  have hd := Nat.mod_add_div a L
  generalize a % L = r at hd ⊢
  generalize a / L = q at hd
  subst hd
  rw [← Nat.add_mul_mod_self_left (r * 2 ^ 64 + w) L (q * 2 ^ 64)]
  congr 1
  rw [Nat.mul_add, Nat.add_comm w, Nat.add_assoc, Nat.add_comm w, ← Nat.add_assoc,
    Nat.mul_comm (2 ^ 64) r, Nat.mul_left_comm (2 ^ 64) L q, Nat.mul_comm (2 ^ 64) q,
    ← Nat.mul_assoc]

theorem decodeLE_eq (xs : List Byte) : decodeLE xs = Proof.X25519.leNum xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [decodeLE, Proof.X25519.leNum, ih]

theorem decodeLE_append (xs ys : List Byte) :
    decodeLE (xs ++ ys) = decodeLE xs + 256 ^ xs.length * decodeLE ys := by
  simp only [VG.Proof.Ed448.decodeLE_eq, Proof.X25519.leNum_append]

theorem decodeLE_lt' (xs : List Byte) : decodeLE xs < 256 ^ xs.length := by
  rw [VG.Proof.Ed448.decodeLE_eq]; exact Proof.X25519.leNum_lt xs

theorem encodeLE_eq (n x : Nat) : encodeLE n x = Proof.X25519.leBytes n x := by
  simp only [encodeLE, Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem bytesAt_eq (m : Mem) (p : Addr) (n : Nat) : VG.Spec.Ed448.bytesAt m p n = Spec.X25519.bytesAt m p n := rfl

theorem leBytes_one (x : Nat) : Proof.X25519.leBytes 1 x = [BitVec.ofNat 8 x] := by
  simp [Proof.X25519.leBytes]

/-- A point's encoding (§5.2.2): the 56 bytes of `y < 2^448`, then the sign
bit `b` as the top bit of the 57th byte. Stated here, where `2 ^ 455` is the
specification's term. -/
theorem encodeLE_57 (y b : Nat) (hy : y < 256 ^ 56) :
    encodeLE 57 (y + b * 2 ^ 455) =
      Proof.X25519.leBytes 56 y ++ [BitVec.ofNat 8 (128 * b)] := by
  have h455 : (2 : Nat) ^ 455 = 256 ^ 56 * 128 := by decide +kernel
  rw [VG.Proof.Ed448.encodeLE_eq, show 57 = 56 + 1 from rfl, Proof.X25519.leBytes_add, h455, VG.Proof.Ed448.leBytes_one]
  generalize hM : (256 : Nat) ^ 56 = M at *
  have hM0 : 0 < M := by omega
  have e1 : (y + b * (M * 128)) % M = y := by
    rw [show y + b * (M * 128) = y + M * (b * 128) by grind, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
  have e2 : (y + b * (M * 128)) / M = 128 * b := by
    rw [show y + b * (M * 128) = y + M * (b * 128) by grind, Nat.add_mul_div_left _ _ hM0, Nat.div_eq_of_lt hy,
      Nat.zero_add, Nat.mul_comm]
  rw [e2, ← Proof.X25519.leBytes_mod 56, hM, e1]

/-- A 57-byte number has no bits from 456 up. -/
theorem decodeLE_shift_456 (xs : List Byte) (h : xs.length = 57) : decodeLE xs >>> 456 = 0 := by
  have hl := VG.Proof.Ed448.decodeLE_lt' xs
  rw [h] at hl
  have e : (2 : Nat) ^ 456 = 256 ^ 57 := by decide +kernel
  rw [Nat.shiftRight_eq_div_pow, e]
  exact Nat.div_eq_of_lt hl

/-- The check of `S < L` on its low 448 bits `y` and byte 56 `b`: `y + (2^448 - L)`
leaves `r` and the carry `c`. -/
theorem sCheck_nat {y b r c : Nat} (hy : y < 2 ^ 448) (hr : r < 2 ^ 448) (hc : c ≤ 1)
    (h : r + 2 ^ 448 * c = y + (2 ^ 448 - L)) : (c = 0 ∧ b = 0) ↔ y + 256 ^ 56 * b < L := by
  have e : (256 : Nat) ^ 56 = 2 ^ 448 := by decide +kernel
  have hL : L < 2 ^ 448 := by decide +kernel
  rw [e]
  generalize (2 : Nat) ^ 448 = M at *
  constructor
  · rintro ⟨rfl, rfl⟩; simp only [Nat.mul_zero, Nat.add_zero] at h ⊢; omega
  · intro h'
    have : b = 0 := by
      rcases Nat.eq_zero_or_pos b with hb | hb
      · exact hb
      · have : M ≤ M * b := Nat.le_mul_of_pos_right M hb
        omega
    subst this
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> omega

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (VG.Spec.Ed448.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  rw [VG.Proof.Ed448.bytesAt_eq]
  simp [Spec.X25519.bytesAt, List.getD_eq_getElem?_getD, hi]

/-- Bit `t` of the scalar is bit `t % 8` of its byte `t / 8`. -/
theorem scalar_bit (m : Mem) (p : Addr) {t : Nat} (ht : t < 456) :
    ((m (p + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1 =
      (decodeLE (VG.Spec.Ed448.bytesAt m p 57) >>> t) &&& 1 := by
  rw [VG.Proof.Ed448.decodeLE_eq, Proof.X25519.leNum_bit, VG.Proof.Ed448.bytesAt_getD m p (by omega)]

end VG.Proof.Ed448

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.DecodeBytes`. -/
section

/-!
# Ed448: decoding a point, from its bytes

`decodePoint` of 57 bytes, in terms of what code computes: the number `y₀` of
the first 56 bytes and the last byte `b`. The encoding's `y` (its bits
0–454) is below `p` exactly when bits 0–6 of `b` are 0 and `y₀ < p`, and the
sign is bit 7 of `b`. Stated here, without Mathlib, where `2 ^ 455` is the
specification's term.
-/

namespace VG.Proof.Ed448

open VG.Spec.Ed448 (decodeLE)
open VG.Proof.X448 (toFe)

theorem decodeLE_57 (bs : List Byte) (h : bs.length = 57) :
    decodeLE bs = decodeLE (bs.take 56) + 256 ^ 56 * (bs.getD 56 0).toNat := by
  have e : bs = bs.take 56 ++ [bs.getD 56 0] := by
    conv => lhs; rw [← List.take_append_drop 56 bs]
    congr 1
    apply List.ext_getElem
    · simp [h]
    · intro i h1 h2
      simp only [List.length_drop, h] at h1
      simp only [List.getElem_drop, List.length_singleton] at h2 ⊢
      have : i = 0 := by omega
      subst this
      simp [List.getD_eq_getElem?_getD, h]
  conv => lhs; rw [e]
  rw [VG.Proof.Ed448.decodeLE_append]
  simp [decodeLE, List.length_take, h]

theorem decodePoint_bytes (bs : List Byte) (h : bs.length = 57) :
    Spec.Ed448.decodePoint bs =
      if (bs.getD 56 0).toNat % 128 = 0 ∧ decodeLE (bs.take 56) < Spec.X448.P then
        (Spec.Ed448.recoverX (toFe (decodeLE (bs.take 56))) ((bs.getD 56 0).toNat / 128 == 1)).map
          fun x => ⟨x, toFe (decodeLE (bs.take 56)), 1⟩
      else none := by
  have hy0 : decodeLE (bs.take 56) < 256 ^ 56 := by
    have := VG.Proof.Ed448.decodeLE_lt' (bs.take 56)
    rwa [List.length_take, h] at this
  have hb : (bs.getD 56 0).toNat < 256 := (bs.getD 56 0).isLt
  have hP : Spec.X448.P < 256 ^ 56 := by decide +kernel
  have e455 : (2 : Nat) ^ 455 = 256 ^ 56 * 128 := by decide +kernel
  generalize hy : decodeLE (bs.take 56) = y0 at *
  generalize hbb : (bs.getD 56 0).toNat = b at *
  unfold Spec.Ed448.decodePoint
  rw [VG.Proof.Ed448.decodeLE_57 bs h, hy, hbb, h]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
  rw [e455]
  generalize (256 : Nat) ^ 56 = M at *
  have hM : 0 < M := by omega
  have em : (y0 + M * b) % (M * 128) = y0 + M * (b % 128) := by
    rw [Nat.add_mod, show M * b % (M * 128) = M * (b % 128) from Nat.mul_mod_mul_left M b 128]
    rw [Nat.mod_eq_of_lt (by omega : y0 < M * 128)]
    have : b % 128 < 128 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt]
    have : M * (b % 128) ≤ M * 127 := Nat.mul_le_mul_left M (by omega)
    omega
  have ed : (y0 + M * b) / (M * 128) = b / 128 := by
    rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hy0, Nat.zero_add]
  by_cases hc : b % 128 = 0 ∧ y0 < Spec.X448.P
  · rw [ite_eq_left hc]
    have hl : (y0 + M * b) % (M * 128) < Spec.X448.P := by
      rw [em, hc.1, Nat.mul_zero, Nat.add_zero]; exact hc.2
    rw [dite_eq_left hl]
    have hfe : (⟨(y0 + M * b) % (M * 128), hl⟩ : Spec.X448.Fe) = toFe y0 :=
      Fin.ext (by
        show (y0 + M * b) % (M * 128) = y0 % Spec.X448.P
        rw [em, hc.1, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hc.2])
    rw [hfe, ed]
    cases Spec.Ed448.recoverX (toFe y0) (b / 128 == 1) <;> rfl
  · rw [ite_eq_right hc]
    have hl : ¬ (y0 + M * b) % (M * 128) < Spec.X448.P := by
      rw [em]
      intro h'
      apply hc
      rcases Nat.eq_zero_or_pos (b % 128) with h0 | h0
      · rw [h0, Nat.mul_zero, Nat.add_zero] at h'; exact ⟨h0, h'⟩
      · have : M ≤ M * (b % 128) := Nat.le_mul_of_pos_right M h0
        omega
    rw [dite_eq_right hl]

end VG.Proof.Ed448

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Root`. -/
section

/-!
# Ed448: the square-root exponent `(p-3)/4` as an addition chain

`x^((p-3)/4)`, which decoding raises `u⁵v³` to (RFC 8032 §5.2.3), shares
X448's addition chain for the inversion as far as `x^(2²²³ - 1)`, and
`(p-3)/4 = 2²⁴⁶ - 2²²² - 1 = (2²²³ - 1) 2²²³ + (2²²² - 1)`.
-/

namespace VG.Proof.Ed448

open VG.Spec.X448
open VG.Proof.X448 (sqn pw pw_one pw_mul sqn_pw pow_pw)

/-- An addition chain for `z^((P - 3) / 4)`. -/
def rootPow (z : VG.Spec.X448.Fe) : VG.Spec.X448.Fe :=
  let t2 := VG.Proof.X448.sqn z 1 * z            -- 2^2 - 1
  let t4 := VG.Proof.X448.sqn t2 2 * t2          -- 2^4 - 1
  let t8 := VG.Proof.X448.sqn t4 4 * t4          -- 2^8 - 1
  let t16 := VG.Proof.X448.sqn t8 8 * t8         -- 2^16 - 1
  let t32 := VG.Proof.X448.sqn t16 16 * t16      -- 2^32 - 1
  let t64 := VG.Proof.X448.sqn t32 32 * t32      -- 2^64 - 1
  let t128 := VG.Proof.X448.sqn t64 64 * t64     -- 2^128 - 1
  let t192 := VG.Proof.X448.sqn t128 64 * t64    -- 2^192 - 1
  let t208 := VG.Proof.X448.sqn t192 16 * t16    -- 2^208 - 1
  let t216 := VG.Proof.X448.sqn t208 8 * t8      -- 2^216 - 1
  let t220 := VG.Proof.X448.sqn t216 4 * t4      -- 2^220 - 1
  let t222 := VG.Proof.X448.sqn t220 2 * t2      -- 2^222 - 1
  let t223 := VG.Proof.X448.sqn t222 1 * z       -- 2^223 - 1
  VG.Proof.X448.sqn t223 223 * t222

theorem rootPow_eq (z : VG.Spec.X448.Fe) : VG.Proof.Ed448.rootPow z = VG.Spec.X448.pow z ((VG.Spec.X448.P - 3) / 4) := by
  rw [VG.Proof.X448.pow_pw, ← congrArg VG.Proof.Ed448.rootPow (VG.Proof.X448.pw_one z)]
  simp only [VG.Proof.Ed448.rootPow, VG.Proof.X448.pw_mul, VG.Proof.X448.sqn_pw]
  exact congrArg (VG.Proof.X448.pw z) (by decide +kernel)

end VG.Proof.Ed448

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Ref`. -/
section

/-!
# Ed448: what code computes, and its agreement with the specification

Untrusted and target-independent, and light: no Mathlib algebra, so that
every target's proofs can import it. The reference computations here are
what Ed448 code computes, on the specification's field elements and
projective points:

* `double`, RFC 8032 §5.2.4's doubling formulas, and `negPoint`, `-x` as
  `0 - x`;
* `ladder`: `[k]B` from the top bit of 456 down, doubling and adding `B`
  when the bit is set, from the neutral point;
* `vladder`: `[S]B + [k]A` the same way, adding `B` for the bits of `S` and
  `A` for those of `k`;
* `recoverRef`: `recoverX` with its products associated as code computes
  them, and the power by `rootPow`'s addition chain.

That they agree with the specification (`BaseLadderOk`, `VerifyEqOk`,
`RecoverOk`) needs the group law over `ZMod p`, which is heavy: these are
`Prop`s, proved once in `Proof/Ed448/Facts.lean`. A target's proofs take
them as hypotheses, and only its registration files import `Facts` and
pass them in.
-/

namespace VG.Proof.Ed448

open Spec.X448 (Fe P)
open Spec.Ed448 (Point)

/-! ## Doubling and negation -/

/-- `B = (X+Y)²`, `C = X²`, `D = Y²`, `E = C+D`, `H = Z²`, `J = E-2H`, and
`((B-E)J, E(C-D), EJ)` (RFC 8032 §5.2.4). -/
def double (p : Point) : Point :=
  let b := (p.X + p.Y) * (p.X + p.Y)
  let c := p.X * p.X
  let dd := p.Y * p.Y
  let e := c + dd
  let h := p.Z * p.Z
  let j := e - (h + h)
  ⟨(b - e) * j, e * (c - dd), e * j⟩

section
variable (p : Point)

theorem double_X : (VG.Proof.Ed448.double p).X = ((p.X + p.Y) * (p.X + p.Y) - (p.X * p.X + p.Y * p.Y)) *
    (p.X * p.X + p.Y * p.Y - (p.Z * p.Z + p.Z * p.Z)) := rfl

theorem double_Y : (VG.Proof.Ed448.double p).Y = (p.X * p.X + p.Y * p.Y) * (p.X * p.X - p.Y * p.Y) := rfl

theorem double_Z : (VG.Proof.Ed448.double p).Z = (p.X * p.X + p.Y * p.Y) *
    (p.X * p.X + p.Y * p.Y - (p.Z * p.Z + p.Z * p.Z)) := rfl

end

/-- `⟨-X, Y, Z⟩`. -/
def negPoint (p : Point) : Point := ⟨0 - p.X, p.Y, p.Z⟩

/-! ## Base-point multiplication -/

/-- `k` has at most 456 bits, as the 57 bytes of a scalar do. (Stated here,
without Mathlib, so that `2 ^ 456` has the instances of the specification's
terms.) -/
def Below456 (k : Nat) : Prop := k < 2 ^ 456

theorem shift_456 {k : Nat} (hk : VG.Proof.Ed448.Below456 k) : k >>> 456 = 0 :=
  (Nat.shiftRight_eq_div_pow k 456).trans (Nat.div_eq_of_lt hk)

theorem decodeLE_below {bs : List Byte} (h : bs.length = 57) : VG.Proof.Ed448.Below456 (Spec.Ed448.decodeLE bs) := by
  have := VG.Proof.Ed448.decodeLE_lt' bs
  rw [h] at this
  exact Nat.lt_of_lt_of_le this (Nat.le_of_eq (by decide +kernel))

/-- Bit `t` of `k`. -/
def bitAt (k t : Nat) : Bool := decide ((k >>> t) &&& 1 = 1)

/-- One bit: the point doubled, and `B` added if the bit is set. -/
def ladderStep (b : Bool) (r : Point) : Point :=
  if b then Spec.Ed448.pointAdd (VG.Proof.Ed448.double r) Spec.Ed448.basePoint else VG.Proof.Ed448.double r

/-- The point after the top `m` of the 456 bits of `k`, from the neutral
point: bits 455 down to `456 - m`. -/
def ladder (k : Nat) : Nat → Point
  | 0 => Spec.Ed448.identity
  | m + 1 => VG.Proof.Ed448.ladderStep (VG.Proof.Ed448.bitAt k (455 - m)) (VG.Proof.Ed448.ladder k m)

/-- The bits from `t` up, after bit `t + 1`'s. -/
theorem ladder_bit (k : Nat) {t : Nat} (ht : t < 456) :
    VG.Proof.Ed448.ladder k (456 - t) = VG.Proof.Ed448.ladderStep (VG.Proof.Ed448.bitAt k t) (VG.Proof.Ed448.ladder k (456 - (t + 1))) := by
  rw [show 456 - t = (456 - (t + 1)) + 1 by omega, VG.Proof.Ed448.ladder, show 455 - (456 - (t + 1)) = t by omega]

/-- The ladder over all 456 bits encodes `[k]B`. -/
def BaseLadderOk : Prop :=
  ∀ k, VG.Proof.Ed448.Below456 k → Spec.Ed448.encodePoint (VG.Proof.Ed448.ladder k 456) =
    Spec.Ed448.encodePoint (Spec.Ed448.pointMul k Spec.Ed448.basePoint)

/-- A point's encoding, as code computes it: the 56 bytes of `y = Y/Z` and
the low bit of `x = X/Z` as the top bit of the 57th, with `1/Z` by X448's
addition chain. -/
theorem encodePoint_code (X Y Z : Fe) :
    Spec.Ed448.encodePoint ⟨X, Y, Z⟩ =
      Proof.X25519.leBytes 56 (Y * Proof.X448.invert Z).val ++
        [BitVec.ofNat 8 (128 * ((X * Proof.X448.invert Z).val % 2))] := by
  unfold Spec.Ed448.encodePoint
  dsimp only [-Nat.reducePow]
  rw [Proof.X448.invert_eq, VG.Proof.Ed448.encodeLE_57 _ _ (Nat.lt_trans (Fin.isLt _) (by decide +kernel))]

/-! ## Verification's equation -/

/-- One bit of both scalars: the point doubled, `B` added if the bit of `S`
is set, and `a` if that of `k` is. -/
def vstepRef (bs bk : Bool) (a q : Point) : Point :=
  let r₁ := VG.Proof.Ed448.double q
  let r₂ := if bs then Spec.Ed448.pointAdd r₁ Spec.Ed448.basePoint else r₁
  if bk then Spec.Ed448.pointAdd r₂ a else r₂

/-- The point after the top `m` of the 456 bits of `S` and `k`. -/
def vladder (S K : Nat) (a : Point) : Nat → Point
  | 0 => Spec.Ed448.identity
  | m + 1 => VG.Proof.Ed448.vstepRef (VG.Proof.Ed448.bitAt S (455 - m)) (VG.Proof.Ed448.bitAt K (455 - m)) a (VG.Proof.Ed448.vladder S K a m)

theorem vladder_bit (S K : Nat) (a : Point) {t : Nat} (ht : t < 456) :
    VG.Proof.Ed448.vladder S K a (456 - t) = VG.Proof.Ed448.vstepRef (VG.Proof.Ed448.bitAt S t) (VG.Proof.Ed448.bitAt K t) a (VG.Proof.Ed448.vladder S K a (456 - (t + 1))) := by
  rw [show 456 - t = (456 - (t + 1)) + 1 by omega, VG.Proof.Ed448.vladder, show 455 - (456 - (t + 1)) = t by omega]

/-- The equation (RFC 8032 §5.2.7) of decoded `A` and `R`: `S < L`, and
`[4]([S]B + [k](-A))` (by `vladder`) and `[4]R` (by doubling) represent the
same point. -/
def VerifyEqOk : Prop :=
  ∀ (pk sig ch : List Byte) (a r : Point), pk.length = 57 → sig.length = 114 → ch.length = 57 →
    Spec.Ed448.decodePoint pk = some a → Spec.Ed448.decodePoint (sig.take 57) = some r →
    Spec.Ed448.verifyEquation pk sig ch =
      (decide (Spec.Ed448.decodeLE (sig.drop 57) < Spec.Ed448.L) &&
        Spec.Ed448.pointEqual
          (VG.Proof.Ed448.double (VG.Proof.Ed448.double (VG.Proof.Ed448.vladder (Spec.Ed448.decodeLE (sig.drop 57)) (Spec.Ed448.decodeLE ch)
            (VG.Proof.Ed448.negPoint a) 456)))
          (VG.Proof.Ed448.double (VG.Proof.Ed448.double r)))

theorem verifyEquation_none {pk sig ch : List Byte}
    (h : Spec.Ed448.decodePoint pk = none ∨ Spec.Ed448.decodePoint (sig.take 57) = none) :
    Spec.Ed448.verifyEquation pk sig ch = false := by
  unfold Spec.Ed448.verifyEquation
  split
  · rfl
  · rcases h with h | h
    · simp only [h]
    · rw [h]; cases Spec.Ed448.decodePoint pk <;> rfl

/-! ## Decoding -/

/-- `recoverX` (RFC 8032 §5.2.3) as code computes it: `v = d y² - 1`,
`u⁵v³ = (u³v)(uv)²`, the power by `rootPow`'s addition chain, the check
`v x² = u`, and `-x = (x - x) - x`. -/
def recoverRef (y : Fe) (sign : Bool) : Option Fe :=
  let u := y * y - 1
  let v := Spec.Ed448.d * (y * y) - 1
  let t := u * u * u * v
  let x := t * VG.Proof.Ed448.rootPow (t * ((u * v) * (u * v)))
  if v * (x * x) ≠ u then none
  else if x = 0 && sign then none
  else some (if (x.val % 2 == 1) == sign then x else (x - x) - x)

/-- `recoverX` is `recoverRef`. -/
def RecoverOk : Prop := ∀ y sign, Spec.Ed448.recoverX y sign = VG.Proof.Ed448.recoverRef y sign

end VG.Proof.Ed448

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Formulas`. -/
section

/-!
# Ed448: the point formulas' field programs, evaluated

Target-independent and light. A field program (`Impl/Ed448/Formulas.lean`)
evaluates on twenty-two field-element slots (`evalOps`): each operation
replaces its destination. A target's proof shows that its code for each
operation updates its slots so; then `doubleOps` doubles the point in slots
0–2 (`double`) and `addOps` adds the point in slots 8–10 to it, into slots
3–5 (`addWith`, the specification's `pointAdd` with `d` the value of slot
11), and each leaves the other slots it does not write as they were.
-/

namespace VG.Proof.Ed448

open VG.Impl.Ed448 (FOp doubleOps addOps)
open Spec.X448 (Fe)

/-- A slot by its number (below 22 in every program here). -/
def idx (n : Nat) : Fin 22 := ⟨n % 22, Nat.mod_lt _ (by decide)⟩

/-- Every slot of the operation is below 22. -/
def fopValid : FOp → Prop
  | .mul o a b | .add o a b | .sub o a b => o < 22 ∧ a < 22 ∧ b < 22
  | .sqr o a => o < 22 ∧ a < 22

instance (op : FOp) : Decidable (VG.Proof.Ed448.fopValid op) := by cases op <;> unfold VG.Proof.Ed448.fopValid <;> infer_instance

/-- The slots after an operation. -/
def evalOp : FOp → (Fin 22 → Fe) → Fin 22 → Fe
  | .mul o a b, e => Function.update e (VG.Proof.Ed448.idx o) (e (VG.Proof.Ed448.idx a) * e (VG.Proof.Ed448.idx b))
  | .sqr o a, e => Function.update e (VG.Proof.Ed448.idx o) (e (VG.Proof.Ed448.idx a) * e (VG.Proof.Ed448.idx a))
  | .add o a b, e => Function.update e (VG.Proof.Ed448.idx o) (e (VG.Proof.Ed448.idx a) + e (VG.Proof.Ed448.idx b))
  | .sub o a b, e => Function.update e (VG.Proof.Ed448.idx o) (e (VG.Proof.Ed448.idx a) - e (VG.Proof.Ed448.idx b))

def evalOps (ops : List FOp) (e : Fin 22 → Fe) : Fin 22 → Fe := ops.foldl (fun e op => VG.Proof.Ed448.evalOp op e) e

/-- The point in slots `i`, `j`, `k`. -/
def pt (e : Fin 22 → Fe) (i j k : Fin 22) : Spec.Ed448.Point := ⟨e i, e j, e k⟩

/-- The specification's addition, with `d` a parameter. -/
def addWith (dd : Fe) (p q : Spec.Ed448.Point) : Spec.Ed448.Point :=
  let a := p.Z * q.Z
  let b := a * a
  let c := p.X * q.X
  let d' := p.Y * q.Y
  let e := dd * c * d'
  let f := b - e
  let g := b + e
  let h := (p.X + p.Y) * (q.X + q.Y)
  ⟨a * f * (h - c - d'), a * g * (d' - c), f * g⟩

theorem addWith_d (p q : Spec.Ed448.Point) : VG.Proof.Ed448.addWith Spec.Ed448.d p q = Spec.Ed448.pointAdd p q := rfl

theorem doubleOps_valid : ∀ op ∈ doubleOps, VG.Proof.Ed448.fopValid op := by decide
theorem addOps_valid : ∀ op ∈ addOps, VG.Proof.Ed448.fopValid op := by decide

theorem doubleOps_eval (e : Fin 22 → Fe) :
    VG.Proof.Ed448.pt (VG.Proof.Ed448.evalOps doubleOps e) 0 1 2 = VG.Proof.Ed448.double (VG.Proof.Ed448.pt e 0 1 2) := rfl

theorem addOps_eval (e : Fin 22 → Fe) :
    VG.Proof.Ed448.pt (VG.Proof.Ed448.evalOps addOps e) 3 4 5 = VG.Proof.Ed448.addWith (e 11) (VG.Proof.Ed448.pt e 0 1 2) (VG.Proof.Ed448.pt e 8 9 10) := rfl

/-- The slot an operation writes. -/
def fopDest : FOp → Nat
  | .mul o _ _ | .sqr o _ | .add o _ _ | .sub o _ _ => o

theorem evalOps_keep (ops : List FOp) (e : Fin 22 → Fe) (i : Fin 22)
    (hi : ∀ op ∈ ops, VG.Proof.Ed448.fopDest op % 22 ≠ i.val) : VG.Proof.Ed448.evalOps ops e i = e i := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    change VG.Proof.Ed448.evalOps ops (VG.Proof.Ed448.evalOp op e) i = e i
    rw [ih _ fun o h => hi o (List.mem_cons_of_mem _ h)]
    have h := hi op List.mem_cons_self
    have hne : i ≠ VG.Proof.Ed448.idx (VG.Proof.Ed448.fopDest op) := fun h' => h (by rw [h']; rfl)
    cases op <;> simp only [VG.Proof.Ed448.evalOp] <;> exact Function.update_of_ne hne _ _

theorem doubleOps_keep (e : Fin 22 → Fe) (i : Fin 22) (hi : 3 ≤ i.val ∧ i.val < 12 ∨ i.val = 20 ∨ i.val = 21) :
    VG.Proof.Ed448.evalOps doubleOps e i = e i :=
  VG.Proof.Ed448.evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleOps, VG.Proof.Ed448.fopDest op < 3 ∨ (12 ≤ VG.Proof.Ed448.fopDest op ∧ VG.Proof.Ed448.fopDest op < 20) := by decide
    have := this op hop
    omega

theorem addOps_keep (e : Fin 22 → Fe) (i : Fin 22) (hi : i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21) :
    VG.Proof.Ed448.evalOps addOps e i = e i :=
  VG.Proof.Ed448.evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ addOps, (3 ≤ VG.Proof.Ed448.fopDest op ∧ VG.Proof.Ed448.fopDest op < 6) ∨ (12 ≤ VG.Proof.Ed448.fopDest op ∧ VG.Proof.Ed448.fopDest op < 21) := by decide
    have := this op hop
    omega

end VG.Proof.Ed448

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.ScalarWords`. -/
section

/-!
# Ed448 scalar arithmetic: little-endian bytes as words

Untrusted and target-independent. A buffer of `len` bytes read from word `k`
up is that word and `2^64` times the bytes above it (`words_step`), which is
how the reductions consume their input from the top.
-/

namespace VG.Proof.Ed448

open VG VG.Spec.Ed448

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (VG.Spec.Ed448.bytesAt m p n).length = n := by
  simp only [VG.Spec.Ed448.bytesAt, List.length_map, List.length_range]

/-- The input from word `k` up: that word, and `2^64` times the bytes above
it. -/
theorem words_step (m : Mem) (p : Addr) (len k : Nat) (hk : 8 * (k + 1) ≤ len) :
    decodeLE (VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k)) (len - 8 * k)) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat +
        2 ^ 64 * decodeLE (VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * (k + 1))) (len - 8 * (k + 1))) := by
  have e : len - 8 * k = 8 + (len - 8 * (k + 1)) := by omega
  have hs : VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k)) (8 + (len - 8 * (k + 1))) =
      VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8 ++
        VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8) (len - 8 * (k + 1)) :=
    Proof.X25519.bytesAt_add m _ 8 _
  have hw : decodeLE (VG.Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat := by
    rw [VG.Proof.Ed448.decodeLE_eq]; exact Proof.X25519.leNum_bytesAt_64 m _
  have ha : p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  rw [e, hs, VG.Proof.Ed448.decodeLE_append, VG.Proof.Ed448.bytesAt_length, hw, ha]

/-- The 57 bytes at `p`: seven words and a byte. -/
theorem decode57 (m : Mem) (p : Addr) :
    decodeLE (VG.Spec.Ed448.bytesAt m p 57) =
      (m.readW (p + BitVec.ofNat 64 0) 64).toNat + 2 ^ 64 * ((m.readW (p + BitVec.ofNat 64 8) 64).toNat +
      2 ^ 64 * ((m.readW (p + BitVec.ofNat 64 16) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 24) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 32) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 40) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 48) 64).toNat + 2 ^ 64 *
      (m (p + BitVec.ofNat 64 56)).toNat)))))) := by
  have e0 := VG.Proof.Ed448.words_step m p 57 0 (by omega)
  have e1 := VG.Proof.Ed448.words_step m p 57 1 (by omega)
  have e2 := VG.Proof.Ed448.words_step m p 57 2 (by omega)
  have e3 := VG.Proof.Ed448.words_step m p 57 3 (by omega)
  have e4 := VG.Proof.Ed448.words_step m p 57 4 (by omega)
  have e5 := VG.Proof.Ed448.words_step m p 57 5 (by omega)
  have e6 := VG.Proof.Ed448.words_step m p 57 6 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.mul_zero, Nat.sub_zero] at e0 e1 e2 e3 e4 e5 e6
  rw [show p = p + BitVec.ofNat 64 0 from (BitVec.add_zero p).symm, e0, e1, e2, e3, e4, e5, e6]
  simp only [VG.Spec.Ed448.bytesAt, List.range_one, List.map_cons, List.map_nil, decodeLE, BitVec.add_zero,
    Nat.mul_zero, Nat.add_zero]

end VG.Proof.Ed448

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Limbs16`. -/
section

/-!
# Ed448 scalar arithmetic on 16-bit limbs: the numbers

Untrusted and target-independent: the numbers of a reduction modulo `L` on a
remainder of twenty-eight 16-bit limbs `r` (`valN r 28 < L`, X448's
representation, `Radix16`), for any limbs `c` of `cL = 2^446 - L`.

Folding a chunk `w` in (`foldC`): the limbs of `l` (`foldL`, `w` and `r`
shifted up by one limb, the top masked to 14 bits) plus `h = foldH r` times
the limbs of `c`, each sum at most `2^32 - 2^16`; their number is below `2L`
and congruent to `w + 2^16 r` (`fold_facts`). A conditional subtraction
(`csub_facts`) then leaves the remainder. The input's bytes are consumed two
at a time from the top (`decode_drop2`), the product's limbs one at a time
(`accFrom_step`), and the result is written as twenty-eight limbs and a zero
byte (`encode_57`).
-/

namespace VG.Proof.Ed448.Limbs16

open VG VG.Proof.X448.Radix16
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)
open VG.Proof.Ed448 (cL L_lit L_lt L_add L_pos bytesAt_length)

/-- `2^c = 2^a 2^b`, without evaluating either side (the elaborator does not
evaluate powers with exponents above 256). -/
theorem pow2_split (a b c : Nat) (h : a + b = c) : (2 : Nat) ^ c = 2 ^ a * 2 ^ b := by
  rw [← h, Nat.pow_add]

theorem radix_pow (n : Nat) : VG.Proof.X448.Radix16.radix ^ n = 2 ^ (16 * n) := by
  rw [VG.Proof.X448.Radix16.radix, ← Nat.pow_mul]

/-! ## Folding a chunk in -/

/-- The limbs of `l`: the chunk `w`, then those of the remainder `r`
shifted up by one, the top one masked to 14 bits. -/
def foldL (r : Nat → Nat) (w k : Nat) : Nat :=
  if k = 0 then w else if k < 27 then r (k - 1) else r 26 % 16384

/-- `h = r₂₆ >> 14 + 4 r₂₇`, the bits of `w + 2^16 r` from 446 up. -/
def foldH (r : Nat → Nat) : Nat := r 26 / 16384 + 4 * r 27

/-- The sums of `l + h c`, before carrying, for the limbs `c` of `cL`. -/
def foldC (c r : Nat → Nat) (w k : Nat) : Nat := VG.Proof.Ed448.Limbs16.foldL r w k + VG.Proof.Ed448.Limbs16.foldH r * c k

theorem foldL_lt {r : Nat → Nat} (hr : ∀ k < 28, r k < VG.Proof.X448.Radix16.radix) {w : Nat} (hw : w < VG.Proof.X448.Radix16.radix) :
    ∀ k < 28, VG.Proof.Ed448.Limbs16.foldL r w k < VG.Proof.X448.Radix16.radix := by
  intro k hk
  unfold VG.Proof.Ed448.Limbs16.foldL
  split
  · exact hw
  · split
    · exact hr _ (by omega)
    · have : (16384 : Nat) < VG.Proof.X448.Radix16.radix := by decide
      have := Nat.mod_lt (r 26) (by decide : 0 < 16384)
      omega

/-- `w + 2^16 r = l + 2^446 h`. -/
theorem foldL_val (r : Nat → Nat) (w : Nat) :
    VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 28 + 2 ^ 446 * VG.Proof.Ed448.Limbs16.foldH r = w + VG.Proof.X448.Radix16.radix * VG.Proof.X448.Radix16.valN r 28 := by
  have e1 : VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 28 = w + VG.Proof.X448.Radix16.radix * (VG.Proof.X448.Radix16.valN r 26 + VG.Proof.X448.Radix16.radix ^ 26 * (r 26 % 16384)) := by
    rw [show (28 : Nat) = 1 + 27 from rfl, VG.Proof.X448.Radix16.valN_split]
    have hs : VG.Proof.X448.Radix16.valN (fun k => VG.Proof.Ed448.Limbs16.foldL r w (1 + k)) 27 =
        VG.Proof.X448.Radix16.valN (fun k => if k < 26 then r k else r 26 % 16384) 27 :=
      VG.Proof.X448.Radix16.valN_congr fun k hk => by
        unfold VG.Proof.Ed448.Limbs16.foldL
        rw [ite_eq_right (by omega)]
        by_cases h : k < 26
        · rw [ite_eq_left (by omega), ite_eq_left h, show 1 + k - 1 = k by omega]
        · rw [ite_eq_right (by omega), ite_eq_right h]
    have hs2 : VG.Proof.X448.Radix16.valN (fun k => if k < 26 then r k else r 26 % 16384) 27 =
        VG.Proof.X448.Radix16.valN r 26 + VG.Proof.X448.Radix16.radix ^ 26 * (r 26 % 16384) := by
      rw [VG.Proof.X448.Radix16.valN_succ, ite_eq_right (by omega), VG.Proof.X448.Radix16.valN_congr (g := r) (n := 26) fun k hk => ite_eq_left hk]
    have h1 : VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 1 = w := by
      simp only [VG.Proof.X448.Radix16.valN, VG.Proof.Ed448.Limbs16.foldL, ite_true, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    rw [hs, hs2, h1, Nat.pow_one]
  have e2 : VG.Proof.X448.Radix16.valN r 28 = VG.Proof.X448.Radix16.valN r 26 + VG.Proof.X448.Radix16.radix ^ 26 * r 26 + VG.Proof.X448.Radix16.radix ^ 26 * VG.Proof.X448.Radix16.radix * r 27 := by
    rw [VG.Proof.X448.Radix16.valN_succ, VG.Proof.X448.Radix16.valN_succ, show VG.Proof.X448.Radix16.radix ^ 27 = VG.Proof.X448.Radix16.radix ^ 26 * VG.Proof.X448.Radix16.radix from Nat.pow_succ ..]
  rw [e1, e2, VG.Proof.Ed448.Limbs16.foldH]
  generalize VG.Proof.X448.Radix16.valN r 26 = v
  have hd : r 26 = r 26 % 16384 + 16384 * (r 26 / 16384) := (Nat.mod_add_div _ _).symm
  generalize r 26 % 16384 = a at hd ⊢
  generalize r 26 / 16384 = b at hd ⊢
  rw [hd]
  generalize r 27 = c
  have p1 : (2 : Nat) ^ 446 = VG.Proof.X448.Radix16.radix ^ 26 * 2 ^ 30 := by
    decide +kernel
  rw [p1]
  have hr : VG.Proof.X448.Radix16.radix = 65536 := rfl
  rw [hr]
  generalize (65536 : Nat) ^ 26 = A
  grind

/-- The facts the code relies on: the sums fit with a carry, `h` and the
top limb fit, and the result is below `2L` and congruent to `w + 2^16 r`. -/
theorem fold_facts {c : Nat → Nat} (hc : ∀ k < 28, c k < VG.Proof.X448.Radix16.radix) (hcv : VG.Proof.X448.Radix16.valN c 28 = VG.Proof.Ed448.cL)
    {r : Nat → Nat} (hr : ∀ k < 28, r k < VG.Proof.X448.Radix16.radix) (hv : VG.Proof.X448.Radix16.valN r 28 < L) {w : Nat} (hw : w < VG.Proof.X448.Radix16.radix) :
    r 27 < 16384 ∧ VG.Proof.Ed448.Limbs16.foldH r < VG.Proof.X448.Radix16.radix ∧ (∀ k < 28, VG.Proof.Ed448.Limbs16.foldC c r w k ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix) ∧
      VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldC c r w) 28 < 2 * L ∧
      VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldC c r w) 28 % L = (w + VG.Proof.X448.Radix16.radix * VG.Proof.X448.Radix16.valN r 28) % L := by
  have hL := VG.Proof.Ed448.L_lit
  have hR : VG.Proof.X448.Radix16.radix = 65536 := rfl
  have h446 : (2 : Nat) ^ 446 = VG.Proof.X448.Radix16.radix ^ 27 * 16384 := by
    decide +kernel
  have h27 : r 27 < 16384 := by
    have e : VG.Proof.X448.Radix16.valN r 28 = VG.Proof.X448.Radix16.valN r 27 + VG.Proof.X448.Radix16.radix ^ 27 * r 27 := VG.Proof.X448.Radix16.valN_succ r 27
    have : L < VG.Proof.X448.Radix16.radix ^ 27 * 16384 := by rw [← h446]; exact VG.Proof.Ed448.L_lt
    rcases Nat.lt_or_ge (r 27) 16384 with h | h
    · exact h
    · have := Nat.mul_le_mul_left (VG.Proof.X448.Radix16.radix ^ 27) h
      omega
  have hH : VG.Proof.Ed448.Limbs16.foldH r < VG.Proof.X448.Radix16.radix := by
    unfold VG.Proof.Ed448.Limbs16.foldH
    have := hr 26 (by omega)
    rw [hR] at this ⊢
    omega
  have hl := VG.Proof.Ed448.Limbs16.foldL_lt hr hw
  refine ⟨h27, hH, fun k hk => ?_, ?_⟩
  · have hm : VG.Proof.Ed448.Limbs16.foldH r * c k ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by rw [hR] at hH; omega) (by have := hc k hk; rw [hR] at this; omega)
    have := hl k hk
    unfold VG.Proof.Ed448.Limbs16.foldC
    rw [hR] at this ⊢
    omega
  have eC : VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldC c r w) 28 = VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 28 + VG.Proof.Ed448.Limbs16.foldH r * VG.Proof.Ed448.cL := by
    unfold VG.Proof.Ed448.Limbs16.foldC
    rw [VG.Proof.X448.Radix16.valN_add, VG.Proof.X448.Radix16.valN_scale, hcv]
  have hL28 : VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 28 < 2 ^ 446 := by
    have e : VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 28 = VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 27 + VG.Proof.X448.Radix16.radix ^ 27 * (r 26 % 16384) := by
      rw [VG.Proof.X448.Radix16.valN_succ]; rfl
    have h1 : VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 27 < VG.Proof.X448.Radix16.radix ^ 27 := VG.Proof.X448.Radix16.valN_lt fun k hk => hl k (by omega)
    have h2 := Nat.mul_le_mul_left (VG.Proof.X448.Radix16.radix ^ 27) (by omega : r 26 % 16384 ≤ 16383)
    rw [h446]
    omega
  have hval := VG.Proof.Ed448.Limbs16.foldL_val r w
  have hP' : (2 : Nat) ^ 446 = L + VG.Proof.Ed448.cL := L_add.symm
  have hcL : VG.Proof.Ed448.cL = 13818066809895115352007386748515426880336692474882178609894547503885 := rfl
  rw [hP'] at hval hL28
  have hHc : VG.Proof.Ed448.Limbs16.foldH r * VG.Proof.Ed448.cL < VG.Proof.X448.Radix16.radix * VG.Proof.Ed448.cL := Nat.mul_lt_mul_of_pos_right hH (by rw [hcL]; decide)
  refine ⟨?_, ?_⟩
  · rw [eC]; rw [hL, hcL, hR] at *; omega
  · rw [eC, ← hval]
    have e : VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 28 + (L + VG.Proof.Ed448.cL) * VG.Proof.Ed448.Limbs16.foldH r =
        VG.Proof.X448.Radix16.valN (VG.Proof.Ed448.Limbs16.foldL r w) 28 + VG.Proof.Ed448.Limbs16.foldH r * VG.Proof.Ed448.cL + VG.Proof.Ed448.Limbs16.foldH r * L := by
      rw [Nat.add_mul, Nat.mul_comm L, Nat.mul_comm VG.Proof.Ed448.cL]; omega
    rw [e, Nat.add_mul_mod_self_right]

/-! ## The conditional subtraction -/

/-- `x + K` for `x < 2L` carries out of `M ≥ 2L` (448 bits) exactly when
`x ≥ L`, and selecting the sum if it carried, else `x`, leaves `x mod L`. -/
theorem csub_facts {M x y c : Nat} (hLM : 2 * L ≤ M) (hx : x < 2 * L) (hy : y < M)
    (he : y + M * c = x + (M - L)) :
    c ≤ 1 ∧ (if c = 1 then y else x) = x % L := by
  have hc : c ≤ 1 := by
    rcases Nat.lt_or_ge c 2 with h | h
    · omega
    · have : M * 2 ≤ M * c := Nat.mul_le_mul_left _ h
      omega
  refine ⟨hc, ?_⟩
  have := Proof.Ed448.csub_nat (M := M) (x := x) (y := y) (c := decide (c = 1)) hLM hx hy
    (by rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simpa using he)
  rw [← this]
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> rfl

/-- `2L` fits in 448 bits. -/
theorem two_L_le : 2 * L ≤ VG.Proof.X448.Radix16.radix ^ 28 := by
  have h := VG.Proof.Ed448.Limbs16.pow2_split 446 2 (16 * 28) rfl
  have := VG.Proof.Ed448.L_lt
  rw [VG.Proof.Ed448.Limbs16.radix_pow]
  omega

/-- A carry pass of a number below `2^448` carries nothing out. -/
theorem carry_zero {f : Nat → Nat} (h : VG.Proof.X448.Radix16.valN f 28 < VG.Proof.X448.Radix16.radix ^ 28) : VG.Proof.X448.Radix16.carry f 28 = 0 := by
  have e := VG.Proof.X448.Radix16.pass_eq f 28
  rcases Nat.eq_zero_or_pos (VG.Proof.X448.Radix16.carry f 28) with hz | hz
  · exact hz
  · have := Nat.mul_le_mul_left (VG.Proof.X448.Radix16.radix ^ 28) hz
    omega

/-- The digits of a carry pass of a number below `2^448` are that number. -/
theorem digits_val {f : Nat → Nat} (h : VG.Proof.X448.Radix16.valN f 28 < VG.Proof.X448.Radix16.radix ^ 28) : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit f) 28 = VG.Proof.X448.Radix16.valN f 28 := by
  have e := VG.Proof.X448.Radix16.pass_eq f 28
  rw [VG.Proof.Ed448.Limbs16.carry_zero h, Nat.mul_zero, Nat.add_zero] at e
  exact e

/-! ## Consuming the input -/

theorem mod_fold (w D : Nat) : (w + VG.Proof.X448.Radix16.radix * (D % L)) % L = (w + VG.Proof.X448.Radix16.radix * D) % L := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- Two bytes more of a suffix. -/
theorem decode_drop2 (m : Mem) (p : Addr) {N n : Nat} (h : n + 2 ≤ N) :
    decodeLE ((bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat +
      256 * (m (p + BitVec.ofNat 64 (n + 1))).toNat + VG.Proof.X448.Radix16.radix * decodeLE ((bytesAt m p N).drop (n + 2)) := by
  rw [List.drop_eq_getElem_cons (by rw [VG.Proof.Ed448.bytesAt_length]; omega),
    List.drop_eq_getElem_cons (by rw [VG.Proof.Ed448.bytesAt_length]; omega)]
  simp only [decodeLE, bytesAt, List.getElem_map, List.getElem_range]
  rw [show n + 1 + 1 = n + 2 from rfl, show VG.Proof.X448.Radix16.radix = 65536 from rfl]
  omega

/-- A suffix of one byte. -/
theorem decode_drop1 (m : Mem) (p : Addr) {N n : Nat} (h : n + 1 = N) :
    decodeLE ((bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat := by
  rw [List.drop_eq_getElem_cons (by rw [VG.Proof.Ed448.bytesAt_length]; omega),
    List.drop_eq_nil_of_le (by rw [VG.Proof.Ed448.bytesAt_length]; omega)]
  simp only [decodeLE, bytesAt, List.getElem_map, List.getElem_range, Nat.mul_zero, Nat.add_zero]

/-- The number of the limbs `a j, …, a 55`. -/
def accFrom (a : Nat → Nat) (j : Nat) : Nat := VG.Proof.X448.Radix16.valN (fun i => a (j + i)) (56 - j)

theorem accFrom_step (a : Nat → Nat) {j : Nat} (hj : j < 56) :
    VG.Proof.Ed448.Limbs16.accFrom a j = a j + VG.Proof.X448.Radix16.radix * VG.Proof.Ed448.Limbs16.accFrom a (j + 1) := by
  unfold VG.Proof.Ed448.Limbs16.accFrom
  rw [show 56 - j = 1 + (56 - (j + 1)) by omega, VG.Proof.X448.Radix16.valN_split]
  simp only [VG.Proof.X448.Radix16.valN, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.pow_one]
  refine congrArg (a j + VG.Proof.X448.Radix16.radix * ·) (VG.Proof.X448.Radix16.valN_congr fun i _ => ?_)
  rw [show j + (1 + i) = j + 1 + i by omega]

theorem accFrom_zero (a : Nat → Nat) : VG.Proof.Ed448.Limbs16.accFrom a 0 = VG.Proof.X448.Radix16.valN a 56 :=
  VG.Proof.X448.Radix16.valN_congr fun i _ => by rw [Nat.zero_add]

/-! ## The result -/

theorem bytesAt_57 (m : Mem) (q : Addr) :
    bytesAt m q 57 = Spec.X448.bytesAt m q 56 ++ [m (q + BitVec.ofNat 64 56)] := by
  simp only [bytesAt, Spec.X448.bytesAt, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

/-- Twenty-eight 16-bit limbs and a zero byte are the 57-byte encoding of
their number. -/
theorem encode_57 {m : Mem} {q : Addr} {f : Nat → Nat} (hl : ∀ k < 28, f k < VG.Proof.X448.Radix16.radix)
    (hd : ∀ k < 28, VG.Proof.X448.Radix16.decoded m q k = f k) (h56 : m (q + BitVec.ofNat 64 56) = 0) :
    bytesAt m q 57 = encodeLE 57 (VG.Proof.X448.Radix16.valN f 28) := by
  have hv : VG.Proof.X448.Radix16.valN f 28 < 256 ^ 56 := by
    have := VG.Proof.X448.Radix16.valN_lt hl
    rwa [show VG.Proof.X448.Radix16.radix ^ 28 = 256 ^ 56 by decide +kernel] at this
  have e := Proof.Ed448.encodeLE_57 (VG.Proof.X448.Radix16.valN f 28) 0 hv
  generalize (2 : Nat) ^ 455 = M at e
  rw [Nat.zero_mul, Nat.add_zero, Nat.mul_zero] at e
  rw [VG.Proof.Ed448.Limbs16.bytesAt_57, e, VG.Proof.X448.Radix16.packed_bytes hd, h56]
  rfl

end VG.Proof.Ed448.Limbs16

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Recover`. -/
section

/-!
# Ed448: decoding a point, as code computes it

`decodePoint` of 57 bytes in terms of what code computes (`decodePoint_impl`),
given that `recoverX` is `recoverRef` (`RecoverOk`, proved in `Facts.lean`).
-/

namespace VG.Proof.Ed448

open Spec.X448 (Fe P)

/-- `decodePoint` of 57 bytes, as the code computes it: from the number `y₀`
of the first 56 bytes and the last byte `b`, `x` as `recoverRef` has it, and
the three checks. -/
theorem decodePoint_impl (hR : VG.Proof.Ed448.RecoverOk) (bs : List Byte) (h : bs.length = 57) (y0 b : Nat)
    (hy0 : Spec.Ed448.decodeLE (bs.take 56) = y0) (hb : (bs.getD 56 0).toNat = b) (Y u v t x : Fe)
    (hY : VG.Proof.X448.toFe y0 = Y) (hu : Y * Y - 1 = u) (hv : Spec.Ed448.d * (Y * Y) - 1 = v)
    (ht : u * u * u * v = t) (hx : t * VG.Proof.Ed448.rootPow (t * ((u * v) * (u * v))) = x) :
    Spec.Ed448.decodePoint bs =
      if (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1) then
        some ⟨if (x.val % 2 == 1) == (b / 128 == 1) then x else (x - x) - x, Y, 1⟩
      else none := by
  rw [VG.Proof.Ed448.decodePoint_bytes bs h, hy0, hb, hY, hR]
  unfold VG.Proof.Ed448.recoverRef
  dsimp only
  rw [hu, hv, ht, hx]
  have hbool : (decide (x = 0) && (b / 128 == 1)) = true ↔ x = 0 ∧ b / 128 = 1 := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  have hc (h1 : b % 128 = 0 ∧ y0 < P) (h2 : v * (x * x) = u) (h3 : ¬ (x = 0 ∧ b / 128 = 1)) :
      (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1) := ⟨h1, h2, h3⟩
  by_cases h1 : b % 128 = 0 ∧ y0 < P
  · rw [ite_eq_left (c := b % 128 = 0 ∧ y0 < P) h1]
    by_cases h2 : v * (x * x) = u
    · rw [ite_eq_right (c := v * (x * x) ≠ u) (not_not_intro h2)]
      by_cases h3 : x = 0 ∧ b / 128 = 1
      · rw [ite_eq_left (c := (decide (x = 0) && (b / 128 == 1)) = true) (hbool.mpr h3),
          ite_eq_right (c := (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1))
            (fun h => h.2.2 h3)]
        rfl
      · rw [ite_eq_right (c := (decide (x = 0) && (b / 128 == 1)) = true) (fun h => h3 (hbool.mp h)),
          ite_eq_left (c := (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1))
            (hc h1 h2 h3)]
        rfl
    · rw [ite_eq_left (c := v * (x * x) ≠ u) h2,
        ite_eq_right (c := (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1))
          (fun h => h2 h.2.1)]
      rfl
  · rw [ite_eq_right (c := b % 128 = 0 ∧ y0 < P) h1,
      ite_eq_right (c := (b % 128 = 0 ∧ y0 < P) ∧ v * (x * x) = u ∧ ¬ (x = 0 ∧ b / 128 = 1))
        (fun h => h1 h.1)]

end VG.Proof.Ed448

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.VerifyFormulas`. -/
section

/-!
# Ed448 verification's equation: its field programs, evaluated

Target-independent and light: the doubling and the addition at the slots
verification uses them with (`doubleAt`, `addAt`, RFC 8032 §5.2.4's formulas,
as for base-point multiplication), and the steps of decoding (`decodeUV`, the
products of `x`, and `-x`), evaluated on the slots (`evalOps`).
-/

namespace VG.Proof.Ed448

open VG.Impl.Ed448 (FOp doubleAt addAt decodeUV)

theorem doubleAt_valid0 : ∀ op ∈ doubleAt 0 1 2, VG.Proof.Ed448.fopValid op := by decide
theorem doubleAt_valid8 : ∀ op ∈ doubleAt 8 9 10, VG.Proof.Ed448.fopValid op := by decide
theorem addAt_valid8 : ∀ op ∈ VG.Impl.Ed448.addAt 8 9, VG.Proof.Ed448.fopValid op := by decide
theorem addAt_valid6 : ∀ op ∈ VG.Impl.Ed448.addAt 6 7, VG.Proof.Ed448.fopValid op := by decide

theorem doubleAt_eval0 (e : Fin 22 → Spec.X448.Fe) :
    VG.Proof.Ed448.pt (VG.Proof.Ed448.evalOps (doubleAt 0 1 2) e) 0 1 2 = VG.Proof.Ed448.double (VG.Proof.Ed448.pt e 0 1 2) := rfl

theorem doubleAt_eval8 (e : Fin 22 → Spec.X448.Fe) :
    VG.Proof.Ed448.pt (VG.Proof.Ed448.evalOps (doubleAt 8 9 10) e) 8 9 10 = VG.Proof.Ed448.double (VG.Proof.Ed448.pt e 8 9 10) := rfl

theorem addAt_eval8 (e : Fin 22 → Spec.X448.Fe) :
    VG.Proof.Ed448.pt (VG.Proof.Ed448.evalOps (VG.Impl.Ed448.addAt 8 9) e) 3 4 5 = VG.Proof.Ed448.addWith (e 11) (VG.Proof.Ed448.pt e 0 1 2) (VG.Proof.Ed448.pt e 8 9 10) := rfl

theorem addAt_eval6 (e : Fin 22 → Spec.X448.Fe) :
    VG.Proof.Ed448.pt (VG.Proof.Ed448.evalOps (VG.Impl.Ed448.addAt 6 7) e) 3 4 5 = VG.Proof.Ed448.addWith (e 11) (VG.Proof.Ed448.pt e 0 1 2) (VG.Proof.Ed448.pt e 6 7 10) := rfl

theorem doubleAt_keep0 (e : Fin 22 → Spec.X448.Fe) (i : Fin 22) (hi : 3 ≤ i.val ∧ i.val < 12 ∨ i.val = 20 ∨ i.val = 21) :
    VG.Proof.Ed448.evalOps (doubleAt 0 1 2) e i = e i :=
  VG.Proof.Ed448.evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleAt 0 1 2, VG.Proof.Ed448.fopDest op < 3 ∨ (12 ≤ VG.Proof.Ed448.fopDest op ∧ VG.Proof.Ed448.fopDest op < 20) := by decide
    have := this op hop
    omega

theorem doubleAt_keep8 (e : Fin 22 → Spec.X448.Fe) (i : Fin 22)
    (hi : i.val < 8 ∨ i.val = 11 ∨ i.val = 20 ∨ i.val = 21) :
    VG.Proof.Ed448.evalOps (doubleAt 8 9 10) e i = e i :=
  VG.Proof.Ed448.evalOps_keep _ _ _ fun op hop => by
    have : ∀ op ∈ doubleAt 8 9 10, (8 ≤ VG.Proof.Ed448.fopDest op ∧ VG.Proof.Ed448.fopDest op < 11) ∨
        (12 ≤ VG.Proof.Ed448.fopDest op ∧ VG.Proof.Ed448.fopDest op < 20) := by decide
    have := this op hop
    omega

theorem addAt_keep (x y : Nat) (e : Fin 22 → Spec.X448.Fe) (i : Fin 22)
    (hi : i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21) :
    VG.Proof.Ed448.evalOps (VG.Impl.Ed448.addAt x y) e i = e i :=
  VG.Proof.Ed448.evalOps_keep _ _ _ fun op hop => by
    have : ∀ x y, ∀ op ∈ VG.Impl.Ed448.addAt x y, (3 ≤ VG.Proof.Ed448.fopDest op ∧ VG.Proof.Ed448.fopDest op < 6) ∨
        (12 ≤ VG.Proof.Ed448.fopDest op ∧ VG.Proof.Ed448.fopDest op < 21) := by
      intro x y op hop
      simp only [VG.Impl.Ed448.addAt, List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [VG.Proof.Ed448.fopDest]
    have := this x y op hop
    omega

theorem idx_val (i : Fin 22) : VG.Proof.Ed448.idx i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem subNeg_eval (xo : Fin 22) (h : xo ≠ 12) (e : (Fin 22 → Spec.X448.Fe)) :
    VG.Proof.Ed448.evalOps [.sub 12 xo.val xo.val, .sub 12 12 xo.val] e 12 = (e xo - e xo) - e xo ∧
      ∀ i : Fin 22, i ≠ 12 → VG.Proof.Ed448.evalOps [.sub 12 xo.val xo.val, .sub 12 12 xo.val] e i = e i := by
  have h12 : VG.Proof.Ed448.idx 12 = 12 := rfl
  simp only [VG.Proof.Ed448.evalOps, List.foldl, VG.Proof.Ed448.evalOp, VG.Proof.Ed448.idx_val, h12]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [Function.update_self, Function.update_self, Function.update_of_ne h]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

theorem decodeUV_dest : ∀ xo yo : Nat, (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9) →
    ∀ op ∈ decodeUV yo xo, VG.Proof.Ed448.fopDest op % 22 = 3 ∨ VG.Proof.Ed448.fopDest op % 22 = 4 ∨ VG.Proof.Ed448.fopDest op % 22 = 5 ∨
      VG.Proof.Ed448.fopDest op % 22 = 12 ∨ VG.Proof.Ed448.fopDest op % 22 = 13 ∨ VG.Proof.Ed448.fopDest op % 22 = xo := by
  rintro xo yo (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

theorem decodeUV_eval (xo yo : Fin 22) (h : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9))
    (e : (Fin 22 → Spec.X448.Fe)) :
    let y := e yo
    let u := y * y - e 10
    let v := e 11 * (y * y) - e 10
    let t := u * u * u * v
    let e' := VG.Proof.Ed448.evalOps (decodeUV yo.val xo.val) e
    e' 13 = u ∧ e' 3 = v ∧ e' xo = t ∧ e' 12 = t * ((u * v) * (u * v)) ∧
      ∀ i : Fin 22, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 12 → i ≠ 13 → i ≠ xo → e' i = e i := by
  have hk : ∀ i : Fin 22, i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 12 → i ≠ 13 → i ≠ xo →
      VG.Proof.Ed448.evalOps (decodeUV yo.val xo.val) e i = e i := fun i h3 h4 h5 h12 h13 hx =>
    VG.Proof.Ed448.evalOps_keep _ _ _ fun op hop => by
      have hd := VG.Proof.Ed448.decodeUV_dest xo.val yo.val (by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) op hop
      have : i.val ≠ 3 := fun h => h3 (Fin.ext h)
      have : i.val ≠ 4 := fun h => h4 (Fin.ext h)
      have : i.val ≠ 5 := fun h => h5 (Fin.ext h)
      have : i.val ≠ 12 := fun h => h12 (Fin.ext h)
      have : i.val ≠ 13 := fun h => h13 (Fin.ext h)
      have := Fin.val_ne_of_ne hx
      omega
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, hk⟩
  · exact ⟨rfl, rfl, rfl, rfl, hk⟩

theorem decodeXOps_eval (xo : Fin 22) (h : xo = 6 ∨ xo = 8) (e : (Fin 22 → Spec.X448.Fe)) :
    let x := e xo * e 21
    let e' := VG.Proof.Ed448.evalOps [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12] e
    e' xo = x ∧ e' 12 = e 3 * (x * x) ∧ e' 13 = e 13 ∧ ∀ i : Fin 22, i ≠ xo → i ≠ 12 → e' i = e i := by
  have hk : ∀ i : Fin 22, i ≠ xo → i ≠ 12 →
      VG.Proof.Ed448.evalOps [.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12] e i = e i := fun i hx h12 =>
    VG.Proof.Ed448.evalOps_keep _ _ _ fun op hop => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      have := Fin.val_ne_of_ne hx
      have : i.val ≠ 12 := fun h => h12 (Fin.ext h)
      have := xo.isLt
      rcases hop with rfl | rfl | rfl <;> simp only [VG.Proof.Ed448.fopDest] <;> omega
  rcases h with rfl | rfl
  · exact ⟨rfl, rfl, rfl, hk⟩
  · exact ⟨rfl, rfl, rfl, hk⟩

theorem evalOps_append (a b : List FOp) (e : Fin 22 → Spec.X448.Fe) : VG.Proof.Ed448.evalOps (a ++ b) e = VG.Proof.Ed448.evalOps b (VG.Proof.Ed448.evalOps a e) :=
  List.foldl_append ..

end VG.Proof.Ed448

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Signing`. -/
section

/-!
# Ed448: the signing pipeline

The pieces the code computes, the nonce and the challenge reduced modulo `L`
by `scalarReduce`, `R` by `scalarBase` and `S` by `scalarMulAdd` of any
57-byte encoding of the pruned scalar, make up `Spec.Ed448.sign`
(`sign_pipeline`), given the public key of the private key.
-/

namespace VG.Proof.Ed448

open VG VG.Spec.Ed448

private theorem encodeLE_bytes (n x : Nat) : encodeLE n x = Proof.X25519.leBytes n x := by
  simp only [encodeLE, Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem decodeLE_encodeLE (n x : Nat) : decodeLE (encodeLE n x) = x % 256 ^ n := by
  rw [encodeLE_bytes, decodeLE_eq]
  induction n generalizing x with
  | zero => simp [Proof.X25519.leBytes, Proof.X25519.leNum, Nat.mod_one]
  | succ n ih =>
    rw [Proof.X25519.leBytes_succ, Proof.X25519.leNum, ih, BitVec.toNat_ofNat]
    change x % 256 + 256 * (x / 256 % 256 ^ n) = x % 256 ^ (n + 1)
    rw [Nat.pow_succ', Nat.mod_mul]

theorem decodeLE_scalarReduce (wide : List Byte) : decodeLE (scalarReduce wide) = decodeLE wide % L := by
  rw [scalarReduce, decodeLE_encodeLE, Nat.mod_eq_of_lt]
  have h : L < 256 ^ 57 := by decide +kernel
  exact Nat.lt_trans (Nat.mod_lt _ L_pos) h

/-- The cached key is constrained to the key derived from this very seed. -/
theorem sign_pipeline (seed context message pk sb : List Byte) (hpk : pk = publicKey seed)
    (hs : decodeLE sb = prune (Spec.Sha3.shake256 seed 114)) :
    scalarBase (scalarReduce (hash context ((Spec.Sha3.shake256 seed 114).drop 57 ++ message))) ++
      scalarMulAdd (scalarReduce (hash context ((Spec.Sha3.shake256 seed 114).drop 57 ++ message)))
        (scalarReduce (hash context (scalarBase (scalarReduce (hash context
          ((Spec.Sha3.shake256 seed 114).drop 57 ++ message))) ++ pk ++ message))) sb =
      sign seed context message := by
  rw [scalarMulAdd, decodeLE_scalarReduce, decodeLE_scalarReduce, hs, scalarBase, decodeLE_scalarReduce, hpk]
  rfl

end VG.Proof.Ed448

end
