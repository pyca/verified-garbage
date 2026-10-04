import VerifiedGarbage.Spec.Aes

/-!
# The inverse cipher's rounds, independently of any representation

What the proofs of the inverse cipher on every target use, whatever holds
the states: the bits of the products by the coefficients of InvMixColumns
(`mulBits`), its linearity (FIPS 197 §5.3.5, for the equivalent inverse
cipher), and the inverse cipher's middle rounds as `invCipher` folds them.
-/

namespace VG.Proof.Aes

open VG VG.Spec.Aes

private theorem getD_eq' {α : Type} {n : Nat} (xs : Vector α n) {i : Nat} (h : i < n) (d : α) :
    xs.getD i d = xs[i] := by
  simp [Vector.getD, Array.getD, h]

private theorem byte_ext' {x y : Byte} (h : ∀ j < 8, x.getLsbD j = y.getLsbD j) : x = y :=
  BitVec.eq_of_getLsbD_eq fun j hj => h j hj

/-! ## InvMixColumns -/

/-- Bit `j` of `{c} • a`, for the coefficients `c` of InvMixColumns, is the
XOR of these bits of `a`. -/
def mulBits (c j : Nat) : List Nat :=
  match c, j with
  | 0x0e, 0 => [5, 6, 7] | 0x0e, 1 => [0, 5] | 0x0e, 2 => [0, 1, 6] | 0x0e, 3 => [0, 1, 2, 5, 6]
  | 0x0e, 4 => [1, 2, 3, 5] | 0x0e, 5 => [2, 3, 4, 6] | 0x0e, 6 => [3, 4, 5, 7] | 0x0e, _ => [4, 5, 6]
  | 0x0b, 0 => [0, 5, 7] | 0x0b, 1 => [0, 1, 5, 6, 7] | 0x0b, 2 => [1, 2, 6, 7] | 0x0b, 3 => [0, 2, 3, 5]
  | 0x0b, 4 => [1, 3, 4, 5, 6, 7] | 0x0b, 5 => [2, 4, 5, 6, 7] | 0x0b, 6 => [3, 5, 6, 7] | 0x0b, _ => [4, 6, 7]
  | 0x0d, 0 => [0, 5, 6] | 0x0d, 1 => [1, 5, 7] | 0x0d, 2 => [0, 2, 6] | 0x0d, 3 => [0, 1, 3, 5, 6, 7]
  | 0x0d, 4 => [1, 2, 4, 5, 7] | 0x0d, 5 => [2, 3, 5, 6] | 0x0d, 6 => [3, 4, 6, 7] | 0x0d, _ => [4, 5, 7]
  | _, 0 => [0, 5] | _, 1 => [1, 5, 6] | _, 2 => [2, 6, 7] | _, 3 => [0, 3, 5, 7]
  | _, 4 => [1, 4, 5, 6] | _, 5 => [2, 5, 6, 7] | _, 6 => [3, 6, 7] | _, _ => [4, 7]

/-- The XOR of the bits `ts` of `a`. -/
def bitsXor (a : Byte) (ts : List Nat) : Bool := ts.foldr (fun t b => a.getLsbD t ^^ b) false

/-- `mulBits` is right, on all 256 bytes. -/
theorem mulBits_ok (c : Nat) (hc : c = 0x0e ∨ c = 0x0b ∨ c = 0x0d ∨ c = 0x09) :
    ∀ a : Fin 256, ∀ j < 8,
      (mul (BitVec.ofNat 8 c) (BitVec.ofNat 8 a.1)).getLsbD j =
        bitsXor (BitVec.ofNat 8 a.1) (mulBits c j) := by
  rcases hc with rfl | rfl | rfl | rfl <;> decide +kernel

theorem mul_bit {c : Nat} (hc : c = 0x0e ∨ c = 0x0b ∨ c = 0x0d ∨ c = 0x09) (a : Byte) {j : Nat}
    (hj : j < 8) : (mul (BitVec.ofNat 8 c) a).getLsbD j = bitsXor a (mulBits c j) := by
  have := mulBits_ok c hc ⟨a.toNat, a.isLt⟩ j hj
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using this

theorem mul0e_bit (a : Byte) {j : Nat} (hj : j < 8) :
    (mul 0x0e a).getLsbD j = bitsXor a (mulBits 0x0e j) := mul_bit (by decide) a hj
theorem mul0b_bit (a : Byte) {j : Nat} (hj : j < 8) :
    (mul 0x0b a).getLsbD j = bitsXor a (mulBits 0x0b j) := mul_bit (by decide) a hj
theorem mul0d_bit (a : Byte) {j : Nat} (hj : j < 8) :
    (mul 0x0d a).getLsbD j = bitsXor a (mulBits 0x0d j) := mul_bit (by decide) a hj
theorem mul09_bit (a : Byte) {j : Nat} (hj : j < 8) :
    (mul 0x09 a).getLsbD j = bitsXor a (mulBits 0x09 j) := mul_bit (by decide) a hj

theorem mulBits_lt : ∀ c ∈ [0x0e, 0x0b, 0x0d, 0x09], ∀ j < 8, ∀ t ∈ mulBits c j, t < 8 := by
  decide

/-- Bit `j` of InvMixColumns at position `p`: the bits `mulBits c j` of the
byte `k` rows down, for the coefficients `c` of rows `k = 0 … 3`. -/
def invMcWords (j : Nat) : List (Nat × Nat) :=
  [(0x0e, 0), (0x0b, 1), (0x0d, 2), (0x09, 3)].flatMap fun ck => (mulBits ck.1 j).map (·, ck.2)

theorem bitsXor_xor (a b : Byte) (ts : List Nat) :
    bitsXor (a ^^^ b) ts = (bitsXor a ts ^^ bitsXor b ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [bitsXor, List.foldr_cons, BitVec.getLsbD_xor] at ih ⊢
    rw [ih]
    cases a.getLsbD t <;> cases b.getLsbD t <;> simp

/-- Multiplication by each coefficient of InvMixColumns distributes over XOR. -/
theorem mul_xor {c : Nat} (hc : c = 0x0e ∨ c = 0x0b ∨ c = 0x0d ∨ c = 0x09) (a b : Byte) :
    mul (BitVec.ofNat 8 c) (a ^^^ b) = mul (BitVec.ofNat 8 c) a ^^^ mul (BitVec.ofNat 8 c) b :=
  byte_ext' fun j hj => by
    rw [BitVec.getLsbD_xor, mul_bit hc _ hj, mul_bit hc _ hj, mul_bit hc _ hj, bitsXor_xor]

/-- A round key as a state. -/
def rkState (rk : List Byte) : State := Vector.ofFn fun i => rk.getD i.1 0

/-- InvMixColumns is linear: of a state XOR a round key, it is the XOR of
theirs (FIPS 197 §5.3.5). -/
theorem invMixColumns_addRoundKey (x : State) (rk : List Byte) {i : Nat} (hi : i < 16) :
    (invMixColumns (addRoundKey x rk)).getD i 0 =
      (invMixColumns x).getD i 0 ^^^ (invMixColumns (rkState rk)).getD i 0 := by
  have hr : ∀ k, (i % 4 + k) % 4 + 4 * (i / 4) < 16 := fun k => by omega
  simp only [invMixColumns, getD_eq' _ hi, Vector.getElem_ofFn, addRoundKey, rkState,
    getD_eq' _ (hr _)]
  rw [show (0x0e : Byte) = BitVec.ofNat 8 0x0e from rfl, show (0x0b : Byte) = BitVec.ofNat 8 0x0b from rfl,
    show (0x0d : Byte) = BitVec.ofNat 8 0x0d from rfl, show (0x09 : Byte) = BitVec.ofNat 8 0x09 from rfl,
    mul_xor (by decide), mul_xor (by decide), mul_xor (by decide), mul_xor (by decide)]
  ac_rfl

/-! ## The inverse cipher's rounds -/

/-- Middle round `j` of the specification's inverse cipher (with round key
`R − 1 − j`). -/
def irnd (R : Nat) (w : List Byte) (j : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  invMixColumns (addRoundKey (invSubBytes (invShiftRows x)) (roundKey w (R - 1 - j)))

/-- The first `m` middle rounds, as `invCipher` folds them. -/
def invMid (R : Nat) (w : List Byte) (m : Nat) (x : Spec.Aes.State) : Spec.Aes.State :=
  (List.range m).foldl (fun s j => irnd R w j s) x

theorem invMid_succ (R : Nat) (w : List Byte) (m : Nat) (x : Spec.Aes.State) :
    invMid R w (m + 1) x = irnd R w m (invMid R w m x) := by
  simp [invMid, List.range_succ, List.foldl_append]

theorem invCipher_eq (R : Nat) (w : List Byte) (x : Spec.Aes.State) :
    invCipher R w x = addRoundKey (invSubBytes (invShiftRows (invMid R w (R - 1)
      (addRoundKey x (roundKey w R))))) (roundKey w 0) := rfl

end VG.Proof.Aes
