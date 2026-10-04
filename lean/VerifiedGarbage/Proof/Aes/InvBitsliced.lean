import VerifiedGarbage.Proof.Aes.Bitsliced

/-!
# Bitsliced AES: the inverse round transformations

As `Bitsliced.lean` does for the cipher: the lemmas turning what each
layer of the inverse cipher's code does to the bits into the transformation
of FIPS 197 §5.3 it computes on the states, and what the layers compute
on input words given as atoms, which the targets' proofs check their code
against. Nothing here depends on the target.
-/

namespace VG.Proof.Aes

open VG VG.Bitslice VG.Spec.Aes

theorem bs_invSubBytes {Q Q' : Nat → BitVec 64} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = (invSbox (bsByte Q p)).getLsbD j) (hr : BsRel Q S) :
    BsRel Q' fun b => invSubBytes (S b) := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = invSbox (bsByte Q (pos b i)) :=
    byte_ext fun j hj => by rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi)]
  rw [this, hr b hb i hi, getD_eq _ hi, getD_eq _ hi]
  simp only [invSubBytes, Vector.getElem_map]

/-- InvShiftRows: position `16r + 4c + b` from `16r + 4((c − r) mod 4) + b`. -/
def invSrSrc (p : Nat) : Nat := 16 * (p / 16) + 4 * ((p / 4 % 4 + 4 - p / 16) % 4) + p % 4

theorem invSrSrc_pos : ∀ b < 4, ∀ i < 16,
    invSrSrc (pos b i) = pos b (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4)) := by
  decide

theorem bs_invShiftRows {Q Q' : Nat → BitVec 64} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = (Q j).getLsbD (invSrSrc p)) (hr : BsRel Q S) :
    BsRel Q' fun b => invShiftRows (S b) := by
  intro b hb i hi
  have : bsByte Q' (pos b i) = bsByte Q (pos b (i % 4 + 4 * ((i / 4 + 4 - i % 4) % 4))) :=
    byte_ext fun j hj => by
      rw [getLsbD_bsByte _ _ hj, getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi),
        invSrSrc_pos b hb i hi]
  rw [this, hr b hb _ (by omega), getD_eq _ hi]
  simp only [invShiftRows, Vector.getElem_ofFn]

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

/-- The bits `(w, k)` of `invMcWords`: bit `w` of the byte `k` rows down. -/
def invMcTerms (j p : Nat) : List (Nat × Nat) := (invMcWords j).map fun wk => (wk.1, down p wk.2)

theorem termsXor_append (Q : Nat → BitVec 64) (l₁ l₂ : List (Nat × Nat)) :
    termsXor Q (l₁ ++ l₂) = (termsXor Q l₁ ^^ termsXor Q l₂) := by
  induction l₁ with
  | nil => simp [termsXor]
  | cons wt l ih =>
    simp only [termsXor, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, Bool.xor_assoc]

/-- The bits `ts` of the byte at `p`, read from the words when they hold it. -/
theorem termsXor_row {Q : Nat → BitVec 64} {p : Nat} {a : Byte}
    (ha : ∀ w < 8, (Q w).getLsbD p = a.getLsbD w) {ts : List Nat} (hts : ∀ t ∈ ts, t < 8) :
    termsXor Q (ts.map fun t => (t, p)) = bitsXor a ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, termsXor, List.foldr_cons, bitsXor] at ih ⊢
    rw [ha t (hts t (by simp)), ih fun u hu => hts u (by simp [hu])]

theorem invMcTerms_eq (j p : Nat) : invMcTerms j p =
    (mulBits 0x0e j).map (fun t => (t, down p 0)) ++ ((mulBits 0x0b j).map (fun t => (t, down p 1)) ++
      ((mulBits 0x0d j).map (fun t => (t, down p 2)) ++ (mulBits 0x09 j).map (fun t => (t, down p 3)))) := by
  simp [invMcTerms, invMcWords, List.map_map, Function.comp_def]

theorem bs_invMixColumns {Q Q' : Nat → BitVec 64} {S : Nat → State}
    (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = termsXor Q (invMcTerms j p)) (hr : BsRel Q S) :
    BsRel Q' fun b => invMixColumns (S b) := by
  intro b hb i hi
  refine byte_ext fun j hj => ?_
  have hbit : ∀ k < 4, ∀ w < 8, (Q w).getLsbD (down (pos b i) k) =
      ((S b).getD ((i % 4 + k) % 4 + 4 * (i / 4)) 0).getLsbD w := fun k hk w hw => by
    rw [down_pos b hb i hi k hk, ← hr b hb _ (by omega), getLsbD_bsByte _ _ hw]
  have hlt := fun c hc => mulBits_lt c hc j hj
  rw [getLsbD_bsByte _ _ hj, h j hj _ (pos_lt hb hi), getD_eq _ hi, invMcTerms_eq,
    termsXor_append, termsXor_append, termsXor_append,
    termsXor_row (hbit 0 (by decide)) (hlt 0x0e (by decide)),
    termsXor_row (hbit 1 (by decide)) (hlt 0x0b (by decide)),
    termsXor_row (hbit 2 (by decide)) (hlt 0x0d (by decide)),
    termsXor_row (hbit 3 (by decide)) (hlt 0x09 (by decide))]
  simp only [invMixColumns, Vector.getElem_ofFn, BitVec.getLsbD_xor]
  rw [mul0e_bit _ hj, mul0b_bit _ hj, mul0d_bit _ hj, mul09_bit _ hj]
  simp only [Bool.xor_assoc, Nat.add_zero]

/-! ## As atoms -/

def invSrG (j p : Nat) : List Nat := [64 * j + invSrSrc p]

/-- InvMixColumns: the bits `invMcTerms`, as atoms. -/
def invMcG (j p : Nat) : List Nat := (invMcTerms j p).map fun wt => 64 * wt.1 + wt.2

end VG.Proof.Aes
