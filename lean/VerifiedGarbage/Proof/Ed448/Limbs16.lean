import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.X448.Radix16Bytes
import VerifiedGarbage.Proof.Framework.PowLit

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

theorem radix_pow (n : Nat) : radix ^ n = 2 ^ (16 * n) := by
  rw [radix, ← Nat.pow_mul]

/-! ## Folding a chunk in -/

/-- The limbs of `l`: the chunk `w`, then those of the remainder `r`
shifted up by one, the top one masked to 14 bits. -/
def foldL (r : Nat → Nat) (w k : Nat) : Nat :=
  if k = 0 then w else if k < 27 then r (k - 1) else r 26 % 16384

/-- `h = r₂₆ >> 14 + 4 r₂₇`, the bits of `w + 2^16 r` from 446 up. -/
def foldH (r : Nat → Nat) : Nat := r 26 / 16384 + 4 * r 27

/-- The sums of `l + h c`, before carrying, for the limbs `c` of `cL`. -/
def foldC (c r : Nat → Nat) (w k : Nat) : Nat := foldL r w k + foldH r * c k

theorem foldL_lt {r : Nat → Nat} (hr : ∀ k < 28, r k < radix) {w : Nat} (hw : w < radix) :
    ∀ k < 28, foldL r w k < radix := by
  intro k hk
  unfold foldL
  split
  · exact hw
  · split
    · exact hr _ (by omega)
    · have : (16384 : Nat) < radix := by decide
      have := Nat.mod_lt (r 26) (by decide : 0 < 16384)
      omega

/-- `w + 2^16 r = l + 2^446 h`. -/
theorem foldL_val (r : Nat → Nat) (w : Nat) :
    valN (foldL r w) 28 + 2 ^ 446 * foldH r = w + radix * valN r 28 := by
  have e1 : valN (foldL r w) 28 = w + radix * (valN r 26 + radix ^ 26 * (r 26 % 16384)) := by
    rw [show (28 : Nat) = 1 + 27 from rfl, valN_split]
    have hs : valN (fun k => foldL r w (1 + k)) 27 =
        valN (fun k => if k < 26 then r k else r 26 % 16384) 27 :=
      valN_congr fun k hk => by
        unfold foldL
        rw [ite_eq_right (by omega)]
        by_cases h : k < 26
        · rw [ite_eq_left (by omega), ite_eq_left h, show 1 + k - 1 = k by omega]
        · rw [ite_eq_right (by omega), ite_eq_right h]
    have hs2 : valN (fun k => if k < 26 then r k else r 26 % 16384) 27 =
        valN r 26 + radix ^ 26 * (r 26 % 16384) := by
      rw [valN_succ, ite_eq_right (by omega), valN_congr (g := r) (n := 26) fun k hk => ite_eq_left hk]
    have h1 : valN (foldL r w) 1 = w := by
      simp only [valN, foldL, ite_true, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    rw [hs, hs2, h1, Nat.pow_one]
  have e2 : valN r 28 = valN r 26 + radix ^ 26 * r 26 + radix ^ 26 * radix * r 27 := by
    rw [valN_succ, valN_succ, show radix ^ 27 = radix ^ 26 * radix from Nat.pow_succ ..]
  rw [e1, e2, foldH]
  generalize valN r 26 = v
  have hd : r 26 = r 26 % 16384 + 16384 * (r 26 / 16384) := (Nat.mod_add_div _ _).symm
  generalize r 26 % 16384 = a at hd ⊢
  generalize r 26 / 16384 = b at hd ⊢
  rw [hd]
  generalize r 27 = c
  have p1 : (2 : Nat) ^ 446 = radix ^ 26 * 2 ^ 30 := by
    decide +kernel
  rw [p1]
  have hr : radix = 65536 := rfl
  rw [hr]
  generalize (65536 : Nat) ^ 26 = A
  grind

/-- The facts the code relies on: the sums fit with a carry, `h` and the
top limb fit, and the result is below `2L` and congruent to `w + 2^16 r`. -/
theorem fold_facts {c : Nat → Nat} (hc : ∀ k < 28, c k < radix) (hcv : valN c 28 = cL)
    {r : Nat → Nat} (hr : ∀ k < 28, r k < radix) (hv : valN r 28 < L) {w : Nat} (hw : w < radix) :
    r 27 < 16384 ∧ foldH r < radix ∧ (∀ k < 28, foldC c r w k ≤ 2 ^ 32 - radix) ∧
      valN (foldC c r w) 28 < 2 * L ∧
      valN (foldC c r w) 28 % L = (w + radix * valN r 28) % L := by
  have hL := L_lit
  have hR : radix = 65536 := rfl
  have h446 : (2 : Nat) ^ 446 = radix ^ 27 * 16384 := by
    decide +kernel
  have h27 : r 27 < 16384 := by
    have e : valN r 28 = valN r 27 + radix ^ 27 * r 27 := valN_succ r 27
    have : L < radix ^ 27 * 16384 := by rw [← h446]; exact L_lt
    rcases Nat.lt_or_ge (r 27) 16384 with h | h
    · exact h
    · have := Nat.mul_le_mul_left (radix ^ 27) h
      omega
  have hH : foldH r < radix := by
    unfold foldH
    have := hr 26 (by omega)
    rw [hR] at this ⊢
    omega
  have hl := foldL_lt hr hw
  refine ⟨h27, hH, fun k hk => ?_, ?_⟩
  · have hm : foldH r * c k ≤ 65535 * 65535 :=
      Nat.mul_le_mul (by rw [hR] at hH; omega) (by have := hc k hk; rw [hR] at this; omega)
    have := hl k hk
    unfold foldC
    rw [hR] at this ⊢
    omega
  have eC : valN (foldC c r w) 28 = valN (foldL r w) 28 + foldH r * cL := by
    unfold foldC
    rw [valN_add, valN_scale, hcv]
  have hL28 : valN (foldL r w) 28 < 2 ^ 446 := by
    have e : valN (foldL r w) 28 = valN (foldL r w) 27 + radix ^ 27 * (r 26 % 16384) := by
      rw [valN_succ]; rfl
    have h1 : valN (foldL r w) 27 < radix ^ 27 := valN_lt fun k hk => hl k (by omega)
    have h2 := Nat.mul_le_mul_left (radix ^ 27) (by omega : r 26 % 16384 ≤ 16383)
    rw [h446]
    omega
  have hval := foldL_val r w
  have hP' : (2 : Nat) ^ 446 = L + cL := L_add.symm
  have hcL : cL = 13818066809895115352007386748515426880336692474882178609894547503885 := rfl
  rw [hP'] at hval hL28
  have hHc : foldH r * cL < radix * cL := Nat.mul_lt_mul_of_pos_right hH (by rw [hcL]; decide)
  refine ⟨?_, ?_⟩
  · rw [eC]; rw [hL, hcL, hR] at *; omega
  · rw [eC, ← hval]
    have e : valN (foldL r w) 28 + (L + cL) * foldH r =
        valN (foldL r w) 28 + foldH r * cL + foldH r * L := by
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
  have := Proof.Ed448.csub_nat (M := M) (x := x) (y := y) (c := decide (c = 1)) hLM hx hy
    (by rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simpa using he)
  rw [← this]
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> rfl

/-- `2L` fits in 448 bits. -/
theorem two_L_le : 2 * L ≤ radix ^ 28 := by
  have h := pow2_split 446 2 (16 * 28) rfl
  have := L_lt
  rw [radix_pow]
  omega

/-- A carry pass of a number below `2^448` carries nothing out. -/
theorem carry_zero {f : Nat → Nat} (h : valN f 28 < radix ^ 28) : carry f 28 = 0 := by
  have e := pass_eq f 28
  rcases Nat.eq_zero_or_pos (carry f 28) with hz | hz
  · exact hz
  · have := Nat.mul_le_mul_left (radix ^ 28) hz
    omega

/-- The digits of a carry pass of a number below `2^448` are that number. -/
theorem digits_val {f : Nat → Nat} (h : valN f 28 < radix ^ 28) : valN (digit f) 28 = valN f 28 := by
  have e := pass_eq f 28
  rw [carry_zero h, Nat.mul_zero, Nat.add_zero] at e
  exact e

/-! ## Consuming the input -/

theorem mod_fold (w D : Nat) : (w + radix * (D % L)) % L = (w + radix * D) % L := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- Two bytes more of a suffix. -/
theorem decode_drop2 (m : Mem) (p : Addr) {N n : Nat} (h : n + 2 ≤ N) :
    decodeLE ((bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat +
      256 * (m (p + BitVec.ofNat 64 (n + 1))).toNat + radix * decodeLE ((bytesAt m p N).drop (n + 2)) := by
  rw [List.drop_eq_getElem_cons (by rw [bytesAt_length]; omega),
    List.drop_eq_getElem_cons (by rw [bytesAt_length]; omega)]
  simp only [decodeLE, bytesAt, List.getElem_map, List.getElem_range]
  rw [show n + 1 + 1 = n + 2 from rfl, show radix = 65536 from rfl]
  omega

/-- A suffix of one byte. -/
theorem decode_drop1 (m : Mem) (p : Addr) {N n : Nat} (h : n + 1 = N) :
    decodeLE ((bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat := by
  rw [List.drop_eq_getElem_cons (by rw [bytesAt_length]; omega),
    List.drop_eq_nil_of_le (by rw [bytesAt_length]; omega)]
  simp only [decodeLE, bytesAt, List.getElem_map, List.getElem_range, Nat.mul_zero, Nat.add_zero]

/-- The number of the limbs `a j, …, a 55`. -/
def accFrom (a : Nat → Nat) (j : Nat) : Nat := valN (fun i => a (j + i)) (56 - j)

theorem accFrom_step (a : Nat → Nat) {j : Nat} (hj : j < 56) :
    accFrom a j = a j + radix * accFrom a (j + 1) := by
  unfold accFrom
  rw [show 56 - j = 1 + (56 - (j + 1)) by omega, valN_split]
  simp only [valN, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero, Nat.pow_one]
  refine congrArg (a j + radix * ·) (valN_congr fun i _ => ?_)
  rw [show j + (1 + i) = j + 1 + i by omega]

theorem accFrom_zero (a : Nat → Nat) : accFrom a 0 = valN a 56 :=
  valN_congr fun i _ => by rw [Nat.zero_add]

/-! ## The result -/

theorem bytesAt_57 (m : Mem) (q : Addr) :
    bytesAt m q 57 = Spec.X448.bytesAt m q 56 ++ [m (q + BitVec.ofNat 64 56)] := by
  simp only [bytesAt, Spec.X448.bytesAt, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

/-- Twenty-eight 16-bit limbs and a zero byte are the 57-byte encoding of
their number. -/
theorem encode_57 {m : Mem} {q : Addr} {f : Nat → Nat} (hl : ∀ k < 28, f k < radix)
    (hd : ∀ k < 28, decoded m q k = f k) (h56 : m (q + BitVec.ofNat 64 56) = 0) :
    bytesAt m q 57 = encodeLE 57 (valN f 28) := by
  have hv : valN f 28 < 256 ^ 56 := by
    have := valN_lt hl
    rwa [show radix ^ 28 = 256 ^ 56 by decide +kernel] at this
  have e := Proof.Ed448.encodeLE_57 (valN f 28) 0 hv
  generalize (2 : Nat) ^ 455 = M at e
  rw [Nat.zero_mul, Nat.add_zero, Nat.mul_zero] at e
  rw [bytesAt_57, e, packed_bytes hd, h56]
  rfl

end VG.Proof.Ed448.Limbs16
