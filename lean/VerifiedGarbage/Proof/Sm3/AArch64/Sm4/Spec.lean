module

-- separate module: its lemmas about lanes, which mention no machine state, build in parallel with `Lit`
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Sm3.Spec
public import VerifiedGarbage.Impl.Sm3.AArch64.Sm4
public import VerifiedGarbage.TCB.AArch64.Isa
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SM3's iterations and message expansion as the AArch64 SM3 instructions compute them

The registers `A … D` and `E … H` are the lanes of a vector each, `A` and
`E` in lane 3 (`abcd`, `efgh`), and the message words `W₄ₖ … W₄ₖ₊₃` those of
`quad M k`, `W₄ₖ` in lane 0.

* `round_abcd`, `round_efgh`: SM3SS1 and then SM3TT1 and SM3TT2 are an
  iteration (`Proof.Sm3.roundW`).
* `expand_eq`: SM3PARTW1 and SM3PARTW2, of the vectors `ext` makes, are four
  words of the message expansion. SM3PARTW1 makes the last of them from the
  first before SM3PARTW2 completes that one, and SM3PARTW2 adds what was
  missing: `P₁` and the rotations are linear.
* `tnext`: `shl #1` and `sri #31` rotate `T_j <<< (j mod 32)` to the next.
* `flip_eq`: `rev64 .4s` and `ext #8` reverse the four words.
-/

@[expose] public section

namespace VG.Proof.Sm3.AArch64.Sm4

open VG.AArch64
open VG.Impl.Sm3.AArch64.Sm4 (tRot)
open VG.Spec.Sm3 (HashValue Word Block W T ff gg p0 p1)

def abcd (v : HashValue) : BitVec 128 := ofVWords v[3] v[2] v[1] v[0]
def efgh (v : HashValue) : BitVec 128 := ofVWords v[7] v[6] v[5] v[4]

/-- The message words `4 k` through `4 k + 3`. -/
def quad (M : Block) (k : Nat) : BitVec 128 :=
  ofVWords (W M (4 * k)) (W M (4 * k + 1)) (W M (4 * k + 2)) (W M (4 * k + 3))

theorem vword_quad (M : Block) (k : Nat) : ∀ {e : Nat} (_ : e < 4), vword (quad M k) e = W M (4 * k + e)
  | 0, _ => vword_ofVWords_0 ..
  | 1, _ => vword_ofVWords_1 ..
  | 2, _ => vword_ofVWords_2 ..
  | 3, _ => vword_ofVWords_3 ..

theorem vword_xor (x y : BitVec 128) (e : Nat) : vword (x ^^^ y) e = vword x e ^^^ vword y e := by
  simp only [vword, BitVec.extractLsb'_xor]

/-! ## An iteration -/

/-- `FF_j` for `16 ≤ j`, as SM3TT1B orders it. -/
theorem maj3 (x y z : Word) : x &&& z ||| x &&& y ||| z &&& y = x &&& y ||| x &&& z ||| y &&& z := by
  ext i; simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> cases z[i] <;> rfl

theorem add_right_comm (a b c : Word) : a + b + c = a + c + b := by
  rw [BitVec.add_assoc, BitVec.add_comm b, ← BitVec.add_assoc]

theorem round_abcd (v : HashValue) (j : Nat) (w w₄ : Word) (x : BitVec 128) (hx : vword x 3 = tRot j) :
    sm3Tt1 (decide (16 ≤ j)) (abcd v) (sm3Ss1 (abcd v) x (efgh v)) (w ^^^ w₄) =
      abcd (roundW v j w w₄) := by
  simp only [sm3Tt1, sm3Ss1, abcd, efgh, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2,
    vword_ofVWords_3, hx, tRot, roundW_0, roundW_1, roundW_2, roundW_3]
  rw [add_right_comm (v[0].rotateLeft 12) ((T j).rotateLeft (j % 32)) v[4]]
  by_cases h : j < 16
  · simp only [ff, h, ite_true, show ¬ 16 ≤ j by omega_using [h], decide_false, Bool.false_eq_true,
      ite_false, BitVec.xor_comm v[2]]
  · simp only [ff, h, ite_false, show 16 ≤ j by omega_using [h], decide_true, ite_true, maj3]

theorem round_efgh (v : HashValue) (j : Nat) (w w₄ : Word) (x : BitVec 128) (hx : vword x 3 = tRot j) :
    sm3Tt2 (decide (16 ≤ j)) (efgh v) (sm3Ss1 (abcd v) x (efgh v)) w = efgh (roundW v j w w₄) := by
  simp only [sm3Tt2, sm3Ss1, abcd, efgh, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2,
    vword_ofVWords_3, hx, tRot, roundW_4, roundW_5, roundW_6, roundW_7, p0]
  rw [add_right_comm (v[0].rotateLeft 12) ((T j).rotateLeft (j % 32)) v[4]]
  by_cases h : j < 16
  · simp only [gg, h, ite_true, show ¬ 16 ≤ j by omega_using [h], decide_false, Bool.false_eq_true,
      ite_false, BitVec.xor_comm v[6]]
  · simp only [gg, h, ite_false, show 16 ≤ j by omega_using [h], decide_true, ite_true]

/-! ## The constants -/

/-- `shl #1`, then `sri #31` into it, of a lane `t`. -/
def rot1 (t : Word) : Word := (t <<< 1 &&& ~~~(BitVec.allOnes 32 >>> 31)) ||| t >>> 31

theorem tnext : ∀ j < 64, j ≠ 15 → rot1 (tRot j) = tRot (j + 1) := by decide

/-! ## The message expansion -/

/-- `ext vd, vn, vm, #(4 k)`: the lanes of `vn` from `k`, then those of `vm`. -/
def extW (k : Nat) (n m : BitVec 128) : BitVec 128 := ((m ++ n) >>> (4 * k * 8)).extractLsb' 0 128

theorem vword_extW (k : Nat) (n m : BitVec 128) {e : Nat} (he : e < 4) :
    vword (extW k n m) e = if e + k < 4 then vword n (e + k) else vword m (e + k - 4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [vword, extW, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hj,
    decide_true, Bool.true_and, Nat.zero_add, show 32 * e + j < 128 by omega_using [he, hj]]
  by_cases h : e + k < 4
  · have h' : 4 * k * 8 + (32 * e + j) < 128 := by omega_using [h, hj]
    simp only [h, h', ↓reduceIte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    exact congrArg n.getLsbD (by omega_using [])
  · have h' : ¬ 4 * k * 8 + (32 * e + j) < 128 := by omega_using [h, hj]
    simp only [h, h', ↓reduceIte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    exact congrArg m.getLsbD (by omega_using [h])

theorem rotl_xor (x y : Word) (k : Nat) : (x ^^^ y).rotateLeft k = x.rotateLeft k ^^^ y.rotateLeft k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor]
  split <;> simp_all

theorem p1_xor (x y : Word) : p1 (x ^^^ y) = p1 x ^^^ p1 y := by
  simp only [p1, rotl_xor, ac]

/-- One of the first three words, as SM3PARTW1 and SM3PARTW2 order it. -/
theorem lane_eq (x y z c r : Word) : p1 (y ^^^ x ^^^ z) ^^^ (c ^^^ r) = p1 (x ^^^ y ^^^ z) ^^^ r ^^^ c := by
  simp only [ac]

/-- The last word: SM3PARTW1 makes it from the first word before SM3PARTW2
has completed that one, and SM3PARTW2 adds what was missing. -/
theorem last_eq (x y a b d r u₁ u₂ : Word) :
    p1 (y ^^^ x ^^^ (p1 (b ^^^ a ^^^ d)).rotateLeft 15) ^^^ (u₁ ^^^ u₂) ^^^ p1 ((y ^^^ r).rotateLeft 15) =
      p1 (x ^^^ y ^^^ (p1 (a ^^^ b ^^^ d) ^^^ r ^^^ y).rotateLeft 15) ^^^ u₂ ^^^ u₁ := by
  simp only [rotl_xor, p1_xor, ac]

theorem partW1_eq (vd vn vm : BitVec 128) :
    sm3PartW1 vd vn vm = ofVWords
      (p1 (vword (vd ^^^ vn) 0 ^^^ (vword vm 1).rotateLeft 15))
      (p1 (vword (vd ^^^ vn) 1 ^^^ (vword vm 2).rotateLeft 15))
      (p1 (vword (vd ^^^ vn) 2 ^^^ (vword vm 3).rotateLeft 15))
      (p1 (vword (vd ^^^ vn) 3 ^^^
        (p1 (vword (vd ^^^ vn) 0 ^^^ (vword vm 1).rotateLeft 15)).rotateLeft 15)) := rfl

/-- `tmp` of SM3PARTW2. -/
def partTmp (vn vm : BitVec 128) : BitVec 128 :=
  vn ^^^ ofVWords ((vword vm 0).rotateLeft 7) ((vword vm 1).rotateLeft 7)
    ((vword vm 2).rotateLeft 7) ((vword vm 3).rotateLeft 7)

theorem partW2_eq (vd vn vm : BitVec 128) :
    sm3PartW2 vd vn vm = ofVWords (vword (vd ^^^ partTmp vn vm) 0) (vword (vd ^^^ partTmp vn vm) 1)
      (vword (vd ^^^ partTmp vn vm) 2)
      (vword (vd ^^^ partTmp vn vm) 3 ^^^ p1 ((vword (partTmp vn vm) 0).rotateLeft 15)) := rfl

theorem W_ge' (M : Block) (t : Nat) :
    W M (t + 16) = p1 (W M t ^^^ W M (t + 7) ^^^ (W M (t + 13)).rotateLeft 15) ^^^
      (W M (t + 3)).rotateLeft 7 ^^^ W M (t + 10) := by
  rw [W_ge M (by omega_using [])]
  simp only [show t + 16 - 16 = t by omega_using [], show t + 16 - 9 = t + 7 by omega_using [],
    show t + 16 - 3 = t + 13 by omega_using [], show t + 16 - 13 = t + 3 by omega_using [],
    show t + 16 - 6 = t + 10 by omega_using []]

theorem expand_eq (M : Block) (n : Nat) :
    sm3PartW2 (sm3PartW1 (extW 3 (quad M (n + 1)) (quad M (n + 2))) (quad M n) (quad M (n + 3)))
      (extW 2 (quad M (n + 2)) (quad M (n + 3))) (extW 3 (quad M n) (quad M (n + 1))) =
      quad M (n + 4) := by
  have w0 := W_ge' M (4 * n)
  have w1 := W_ge' M (4 * n + 1)
  have w2 := W_ge' M (4 * n + 2)
  have w3 := W_ge' M (4 * n + 3)
  simp only [show 4 * n + 16 = 4 * (n + 4) by omega_using [],
    show 4 * n + 1 + 16 = 4 * (n + 4) + 1 by omega_using [],
    show 4 * n + 2 + 16 = 4 * (n + 4) + 2 by omega_using [],
    show 4 * n + 3 + 16 = 4 * (n + 4) + 3 by omega_using [],
    show 4 * n + 7 = 4 * (n + 1) + 3 by omega_using [], show 4 * n + 1 + 7 = 4 * (n + 2) by omega_using [],
    show 4 * n + 2 + 7 = 4 * (n + 2) + 1 by omega_using [],
    show 4 * n + 3 + 7 = 4 * (n + 2) + 2 by omega_using [],
    show 4 * n + 13 = 4 * (n + 3) + 1 by omega_using [],
    show 4 * n + 1 + 13 = 4 * (n + 3) + 2 by omega_using [],
    show 4 * n + 2 + 13 = 4 * (n + 3) + 3 by omega_using [],
    show 4 * n + 1 + 3 = 4 * (n + 1) by omega_using [], show 4 * n + 2 + 3 = 4 * (n + 1) + 1 by omega_using [],
    show 4 * n + 3 + 3 = 4 * (n + 1) + 2 by omega_using [],
    show 4 * n + 1 + 10 = 4 * (n + 2) + 3 by omega_using [],
    show 4 * n + 2 + 10 = 4 * (n + 3) by omega_using []] at w0 w1 w2 w3
  conv => rhs; rw [quad, w0, w1, w2, w3, w0]
  simp only [partW2_eq, partW1_eq, vword_xor, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2,
    vword_ofVWords_3, vword_extW, partTmp,
    vword_quad, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, Nat.lt_add_one, Nat.add_zero]
  exact congr (congr (congr (congrArg ofVWords (lane_eq ..)) (lane_eq ..)) (lane_eq ..)) (last_eq ..)

/-! ## The order of the words -/

/-- `ext v, v, v, #8`: the two halves swapped. -/
def swap8 (x : BitVec 128) : BitVec 128 := ((x ++ x) >>> (8 * 8)).extractLsb' 0 128

/-- `rev64 .4s` and `ext #8` reverse the four words. -/
theorem vword_flip (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (swap8 (VRevOp.rev64s.eval x)) e = vword x (3 - e) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hb : (8 * ((4 * ((e + 2) % 4) + j / 8) / 8) + ((4 * ((e + 2) % 4) + j / 8) % 8 + 4) % 8) =
      4 * (3 - e) + j / 8 := by omega_using [he, hj]
  have hs : ∀ y : BitVec 128, (vword (swap8 y) e).getLsbD j = y.getLsbD (32 * ((e + 2) % 4) + j) := fun y => by
    simp only [vword, swap8, BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, hj,
      decide_true, Bool.true_and, Nat.zero_add, show 32 * e + j < 128 by omega_using [he, hj]]
    by_cases h : e < 2
    · rw [ite_eq_left (by omega_using [h, hj])]
      exact congrArg y.getLsbD (by omega_using [h])
    · rw [ite_eq_right (by omega_using [h, hj])]
      exact congrArg y.getLsbD (by omega_using [h, he])
  rw [hs]
  simp only [VRevOp.eval]
  rw [show 32 * ((e + 2) % 4) + j = 8 * (4 * ((e + 2) % 4) + j / 8) + j % 8 by omega_using [],
    getLsbD_ofVBytes _ (by omega_using [hj]) (by omega_using []), hb]
  simp only [vbyte, vword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    show j % 8 < 8 by omega_using []]
  exact congrArg x.getLsbD (by omega_using [he])

theorem flip_eq (a b c d : Word) : swap8 (VRevOp.rev64s.eval (ofVWords a b c d)) = ofVWords d c b a :=
  vec_ext fun e he => by
    rw [vword_flip _ he]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_using [he]) with rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceSub, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3]

/-! ## The feed-forward -/

theorem xor_abcd (v H : HashValue) : abcd v ^^^ abcd H = abcd (Vector.zipWith (· ^^^ ·) v H) :=
  vec_ext fun e he => by
    rw [vword_xor]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_using [he]) with rfl | rfl | rfl | rfl <;>
      simp only [abcd, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3,
        Vector.getElem_zipWith]

theorem xor_efgh (v H : HashValue) : efgh v ^^^ efgh H = efgh (Vector.zipWith (· ^^^ ·) v H) :=
  vec_ext fun e he => by
    rw [vword_xor]
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_using [he]) with rfl | rfl | rfl | rfl <;>
      simp only [efgh, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3,
        Vector.getElem_zipWith]

end VG.Proof.Sm3.AArch64.Sm4
