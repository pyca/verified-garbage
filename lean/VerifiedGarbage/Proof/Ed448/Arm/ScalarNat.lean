import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X25519.Arm.Limbs
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Impl.Ed448.Arm.Scalar

/-!
# Ed448 scalar arithmetic on ARMv7: the numbers

The remainder is twenty-eight 16-bit limbs `r` (`val16 r 28 < L`). Folding a
chunk `w` in (`foldC`): the limbs of `l` (`foldL`, `w` and `r` shifted up
by one limb, the top masked to 14 bits) plus `h = foldH r` times the limbs
of `c = 2^446 - L` (`cLimb`), each sum below `2^32 - 2^16`; their number is
below `2L` and congruent to `w + 2^16 r` (`fold_facts`). The limbs of
`K = 2^448 - L` (`kLimb`) for the conditional subtraction.
-/

namespace VG.Proof.Ed448.Arm

open VG.Proof.X25519.Arm (val16 val16_succ val16_congr val16_lt val16_add val16_cmul val16_append)
open VG.Impl.Ed448.Arm
open VG.Spec.Ed448 (L)

/-! ## Constants -/

theorem cLimb_high {k : Nat} (h : 14 ≤ k) : cLimb k = 0 := by
  rw [cLimb, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
    simp only [cLimbs, List.length_cons, List.length_nil]; omega)]
  rfl

theorem cLimb_lt (k : Nat) : cLimb k < 65536 := by
  by_cases h : k < 14
  · have : ∀ k < 14, cLimb k < 65536 := by decide
    exact this k h
  · rw [cLimb_high (by omega)]; decide

theorem kLimb_lt (k : Nat) : kLimb k < 65536 := by
  unfold kLimb; split
  · decide
  · exact cLimb_lt k

theorem kLimb_mid {k : Nat} (h1 : 14 ≤ k) (h2 : k ≠ 27) : kLimb k = 0 := by
  rw [kLimb, ite_eq_right h2, cLimb_high h1]

theorem val16_cLimb : val16 cLimb 28 = cL := by decide +kernel

theorem val16_kLimb : val16 kLimb 28 = 2 ^ (16 * 28 : Nat) - L := by decide +kernel

/-- `2^c = 2^a 2^b`, without evaluating either side (the elaborator does not
evaluate powers with exponents above 256). -/
theorem pow2_split (a b c : Nat) (h : a + b = c) : (2 : Nat) ^ c = 2 ^ a * 2 ^ b := by
  rw [← h, Nat.pow_add]

/-! ## Folding a chunk in -/

/-- The limbs of `l`: the chunk `w`, then those of the remainder `r`
shifted up by one, the top one masked to 14 bits. -/
def foldL (r : Nat → Nat) (w k : Nat) : Nat :=
  if k = 0 then w else if k < 27 then r (k - 1) else r 26 % 16384

/-- `h = r₂₆ >> 14 + 4 r₂₇`, the bits of `w + 2^16 r` from 446 up. -/
def foldH (r : Nat → Nat) : Nat := r 26 / 16384 + 4 * r 27

/-- The sums of `l + h c`, before carrying. -/
def foldC (r : Nat → Nat) (w k : Nat) : Nat := foldL r w k + foldH r * cLimb k

theorem foldL_lt {r : Nat → Nat} (hr : ∀ k < 28, r k < 65536) {w : Nat} (hw : w < 65536) :
    ∀ k < 28, foldL r w k < 65536 := by
  intro k hk
  unfold foldL
  split
  · exact hw
  · split
    · exact hr _ (by omega)
    · omega

/-- `w + 2^16 r = l + 2^446 h`. -/
theorem foldL_val (r : Nat → Nat) (w : Nat) :
    val16 (foldL r w) 28 + 2 ^ 446 * foldH r = w + 65536 * val16 r 28 := by
  have e1 : val16 (foldL r w) 28 = w + 65536 * (val16 r 26 + 2 ^ 416 * (r 26 % 16384)) := by
    rw [show (28 : Nat) = 1 + 27 from rfl, val16_append]
    have hs : val16 (fun k => foldL r w (1 + k)) 27 =
        val16 (fun k => if k < 26 then r k else r 26 % 16384) 27 :=
      val16_congr fun k hk => by
        unfold foldL
        rw [ite_eq_right (by omega)]
        by_cases h : k < 26
        · rw [ite_eq_left (by omega), ite_eq_left h, show 1 + k - 1 = k by omega]
        · rw [ite_eq_right (by omega), ite_eq_right h]
    have hs2 : val16 (fun k => if k < 26 then r k else r 26 % 16384) 27 =
        val16 r 26 + 2 ^ 416 * (r 26 % 16384) := by
      rw [val16_succ, ite_eq_right (by omega), val16_congr (g := r) (n := 26) fun k hk => ite_eq_left hk,
        show 16 * 26 = 416 from rfl]
    have h1 : val16 (foldL r w) 1 = w := by
      simp only [val16, foldL, ite_true, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    rw [hs, hs2, h1]
  have e2 : val16 r 28 = val16 r 26 + 2 ^ 416 * r 26 + 2 ^ 432 * r 27 := by
    rw [val16_succ, val16_succ, show 16 * 26 = 416 from rfl, show 16 * 27 = 432 from rfl]
  rw [e1, e2, foldH]
  generalize val16 r 26 = v
  have hd : r 26 = r 26 % 16384 + 16384 * (r 26 / 16384) := (Nat.mod_add_div _ _).symm
  generalize r 26 % 16384 = a at hd ⊢
  generalize r 26 / 16384 = b at hd ⊢
  rw [hd]
  generalize r 27 = c
  have p1 : (2 : Nat) ^ 446 = 2 ^ 416 * 2 ^ 30 := pow2_split 416 30 446 rfl
  have p2 : (2 : Nat) ^ 432 = 2 ^ 416 * 2 ^ 16 := pow2_split 416 16 432 rfl
  rw [p1, p2]
  clear p1 p2 e1 e2
  generalize (2 : Nat) ^ 416 = A
  grind

/-- The facts the code relies on: the sums fit with a carry, `h` and the
top limb fit, and the result is below `2L` and congruent to `w + 2^16 r`. -/
theorem fold_facts {r : Nat → Nat} (hr : ∀ k < 28, r k < 65536) (hv : val16 r 28 < L)
    {w : Nat} (hw : w < 65536) :
    r 27 < 16384 ∧ foldH r < 65536 ∧ (∀ k < 28, foldC r w k + 65536 ≤ 2 ^ 32) ∧
      val16 (foldC r w) 28 < 2 * L ∧
      val16 (foldC r w) 28 % L = (w + 65536 * val16 r 28) % L := by
  have hL := L_lit
  have h27 : r 27 < 16384 := by
    have e : val16 r 28 = val16 r 27 + 2 ^ 432 * r 27 := by
      rw [val16_succ, show 16 * 27 = 432 from rfl]
    have : L < 2 ^ 432 * 2 ^ 14 := by
      rw [← pow2_split 432 14 446 rfl]; exact L_lt
    rcases Nat.lt_or_ge (r 27) 16384 with h | h
    · exact h
    · have := Nat.mul_le_mul_left (2 ^ 432) h
      omega
  have hH : foldH r < 65536 := by
    unfold foldH
    have := hr 26 (by omega)
    omega
  have hl := foldL_lt hr hw
  refine ⟨h27, hH, fun k hk => ?_, ?_⟩
  · have hm : foldH r * cLimb k ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by omega) (by have := cLimb_lt k; omega)
    have := hl k hk
    unfold foldC
    omega
  have eC : val16 (foldC r w) 28 = val16 (foldL r w) 28 + foldH r * cL := by
    unfold foldC
    rw [val16_add, val16_cmul, val16_cLimb]
  have hL28 : val16 (foldL r w) 28 < 2 ^ 432 * 2 ^ 14 := by
    have e : val16 (foldL r w) 28 = val16 (foldL r w) 27 + 2 ^ 432 * (r 26 % 16384) := by
      rw [val16_succ, show 16 * 27 = 432 from rfl, show foldL r w 27 = r 26 % 16384 from rfl]
    have h1 : val16 (foldL r w) 27 < 2 ^ 432 := by
      have := val16_lt (f := foldL r w) (n := 27) fun k hk => hl k (by omega)
      rwa [show 16 * 27 = 432 from rfl] at this
    have h2 := Nat.mul_le_mul_left (2 ^ 432) (by omega : r 26 % 16384 ≤ 16383)
    omega
  have hval := foldL_val r w
  have hP : (2 : Nat) ^ 446 = 2 ^ 432 * 2 ^ 14 := by
    exact pow2_split 432 14 446 rfl
  have hP' : (2 : Nat) ^ 446 = L + cL := L_add.symm
  have hcL : cL = 13818066809895115352007386748515426880336692474882178609894547503885 := rfl
  rw [hP'] at hval
  rw [← hP, hP'] at hL28
  have hHc : foldH r * cL < 65536 * cL := Nat.mul_lt_mul_of_pos_right hH (by rw [hcL]; decide)
  refine ⟨?_, ?_⟩
  · rw [eC]; rw [hL, hcL] at *; omega
  · rw [eC, ← hval]
    have e : val16 (foldL r w) 28 + (L + cL) * foldH r =
        val16 (foldL r w) 28 + foldH r * cL + foldH r * L := by
      rw [Nat.add_mul, Nat.mul_comm L, Nat.mul_comm cL]; omega
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
  have := csub_nat (M := M) (x := x) (y := y) (c := decide (c = 1)) hLM hx hy
    (by rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simpa using he)
  rw [← this]
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> rfl

/-- `2L` fits in 448 bits. -/
theorem two_L_le : 2 * L ≤ 2 ^ (16 * 28 : Nat) := by
  have h := pow2_split 446 2 (16 * 28) rfl
  have := L_lt
  omega

end VG.Proof.Ed448.Arm
