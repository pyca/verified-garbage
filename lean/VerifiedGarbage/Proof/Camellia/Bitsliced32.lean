module
public import VerifiedGarbage.Proof.Camellia.Bytes
public import VerifiedGarbage.Proof.Framework.Bitslice.Table

import VerifiedGarbage.Proof.Camellia.Bitsliced

/-!
# Bitsliced Camellia on 32-bit planes

The layout of the 32-bit targets (`Impl/Camellia/Arm/Layers.lean`): eight
blocks at a time, each 64-bit half of a block (`D1` or `D2`) held in
sixteen 32-bit planes, its left word (bytes 0–3, from the most
significant) in planes 0–7 and its right word (bytes 4–7) in planes 8–15:
bit `8 i + b` of plane `8 w + j` is bit `j` of the half's byte `4 w + i`
in block `b` (`HalfRel`).

The lemmas here turn what each layer of the code does to the bits (as its
proof states it) into the function of RFC 3713 it computes on the halves:
a round (`round_rel`), FL and FLINV (`fl_rel`, `flinv_rel`). Nothing here
depends on the target.
-/

@[expose] public section

namespace VG.Proof.Camellia.W32

open VG VG.Spec.Camellia VG.Bitslice
open VG.Proof.Aes (byte_ext)
open VG.Proof.Camellia (rotl1_bit rotl7_bit rowBits pRow_lt)

/-! ## The layout -/

/-- The byte formed by bit `p` of the eight planes. -/
def bsByte (Q : Nat → BitVec 32) (p : Nat) : Byte := ofBits 8 fun k => (Q k).getLsbD p

theorem getLsbD_bsByte (Q : Nat → BitVec 32) (p : Nat) {k : Nat} (hk : k < 8) :
    (bsByte Q p).getLsbD k = (Q k).getLsbD p := by
  rw [bsByte, getLsbD_ofBits]; simp [hk]

/-- The planes `Q` hold the halves `d b` of the eight blocks. -/
def HalfRel (Q : Nat → BitVec 32) (d : Nat → BitVec 64) : Prop :=
  ∀ b < 8, ∀ c < 8, ∀ j < 8, (Q (8 * (c / 4) + j)).getLsbD (8 * (c % 4) + b) = (byteOf (d b) c).getLsbD j

theorem HalfRel.congr {Q Q' : Nat → BitVec 32} {d : Nat → BitVec 64} (h : HalfRel Q d)
    (he : ∀ j < 16, Q' j = Q j) : HalfRel Q' d := fun b hb c hc j hj => by
  rw [he _ (by omega)]; exact h b hb c hc j hj

theorem HalfRel.congr_right {Q : Nat → BitVec 32} {d d' : Nat → BitVec 64} (h : HalfRel Q d)
    (he : ∀ b < 8, d' b = d b) : HalfRel Q d' := fun b hb c hc j hj => by
  rw [he b hb]; exact h b hb c hc j hj

/-- Bit `p` of plane `8 w + j` (for `p < 32`) is bit `56 - 8 c + j` of the
half, `c = 4 w + p / 8` its byte. -/
theorem half_bit {Q : Nat → BitVec 32} {d : Nat → BitVec 64} (h : HalfRel Q d) {w j p : Nat}
    (hw : w < 2) (hj : j < 8) (hp : p < 32) :
    (Q (8 * w + j)).getLsbD p = (d (p % 8)).getLsbD (56 - 8 * (4 * w + p / 8) + j) := by
  have := h (p % 8) (by omega) (4 * w + p / 8) (by omega) j hj
  rw [show (4 * w + p / 8) / 4 = w by omega, show 8 * ((4 * w + p / 8) % 4) + p % 8 = p by omega,
    getLsbD_byteOf _ (by omega) hj] at this
  exact this

/-- XORing a subkey into the planes of a half. -/
theorem HalfRel.xor {Q K Q' : Nat → BitVec 32} {d k : Nat → BitVec 64} (hq : HalfRel Q d)
    (hk : HalfRel K k) (h : ∀ j < 16, ∀ p < 32, (Q' j).getLsbD p = ((Q j).getLsbD p ^^ (K j).getLsbD p)) :
    HalfRel Q' (fun b => d b ^^^ k b) := fun b hb c hc j hj => by
  rw [h _ (by omega) _ (by omega), hq b hb c hc j hj, hk b hb c hc j hj, byteOf_xor,
    BitVec.getLsbD_xor]

/-! ## A round

The S-boxes of the bytes `c` of a half: `SBOX4`'s input (bytes 3 and 6) is
rotated left by a bit, `SBOX2`'s output (bytes 1 and 4) left and `SBOX3`'s
(bytes 2 and 5) right. -/

/-- The plane that input selection takes for plane `j` in byte `c`. -/
def inSrc (c j : Nat) : Nat := if c = 3 ∨ c = 6 then (j + 7) % 8 else j

/-- The plane that output selection takes for plane `j` in byte `c`. -/
def outSrc (c j : Nat) : Nat :=
  if c = 1 ∨ c = 4 then (j + 7) % 8 else if c = 2 ∨ c = 5 then (j + 1) % 8 else j

theorem inSrc_lt {c j : Nat} (hj : j < 8) : inSrc c j < 8 := by
  simp only [inSrc]; split <;> omega

theorem outSrc_lt {c j : Nat} (hj : j < 8) : outSrc c j < 8 := by
  simp only [outSrc]; split <;> (try split) <;> omega

/-- The S-box bytes: input bit `inSrc` and output bit `outSrc` of `SBOX1`
make the S-box of byte `c`. -/
theorem sbox_sel {x : Byte} {c j : Nat} (hc : c < 8) (hj : j < 8) :
    (sbox1 (ofBits 8 fun j' => x.getLsbD (inSrc c j'))).getLsbD (outSrc c j) = (sboxAt c x).getLsbD j := by
  have hin : (ofBits 8 fun j' => x.getLsbD (inSrc c j')) = if c = 3 ∨ c = 6 then x.rotateLeft 1 else x := by
    refine byte_ext fun j' hj' => ?_
    rw [getLsbD_ofBits]
    simp only [inSrc, hj', decide_true, Bool.true_and]
    split
    · rw [rotl1_bit _ hj']
    · rfl
  rw [hin]
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [outSrc, sboxAt, sbox2, sbox3, sbox4, rotl1_bit _ hj, rotl7_bit _ hj]

/-- The selected output of the S-boxes, for byte `c` of plane `j` at
position `b`: the left word's (already selected, in `YL`) or the right
word's (`SR`, selected here). -/
def ySel (YL SR : Nat → BitVec 32) (j b c : Nat) : Bool :=
  if c < 4 then (YL j).getLsbD (8 * c + b) else (SR (outSrc c j)).getLsbD (8 * (c - 4) + b)

/-- The XOR of the selected outputs along a row of the P-function. -/
def rowSel (YL SR : Nat → BitVec 32) (j b : Nat) (l : List Nat) : Bool :=
  l.foldr (fun c acc => ySel YL SR j b c ^^ acc) false

theorem rowSel_eq {YL SR : Nat → BitVec 32} {t : Nat → Byte} {j b : Nat} {l : List Nat}
    (hl : ∀ c ∈ l, ySel YL SR j b c = (t c).getLsbD j) : rowSel YL SR j b l = xorRow t l j := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [rowSel, xorRow, List.foldr_cons] at ih ⊢
    rw [hl i List.mem_cons_self, ih fun i' hi' => hl i' (List.mem_cons_of_mem _ hi')]

/-- A round: from the half `d1` in the planes `Q`, the subkey `k` in `K` and
the other half `d2` in `R`, the code computes `XL` and `XR` (the subkey XOR
and input selection of the left and right words), `SL` and `SR` (`SBOX1`),
`YL` (the left word's output selection), and XORs the P-function of the
selected outputs into `R`: `R'` holds `d2 ^ F(d1, k)`. -/
theorem round_rel {Q K R XL SL YL XR SR R' : Nat → BitVec 32} {d1 d2 : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel Q d1) (hK : HalfRel K fun _ => k) (hR : HalfRel R d2)
    (hXL : ∀ j < 8, ∀ p < 32,
      (XL j).getLsbD p = ((Q (inSrc (p / 8) j)).getLsbD p ^^ (K (inSrc (p / 8) j)).getLsbD p))
    (hSL : ∀ j < 8, ∀ p < 32, (SL j).getLsbD p = (sbox1 (bsByte XL p)).getLsbD j)
    (hYL : ∀ j < 8, ∀ p < 32, (YL j).getLsbD p = (SL (outSrc (p / 8) j)).getLsbD p)
    (hXR : ∀ j < 8, ∀ p < 32, (XR j).getLsbD p =
      ((Q (8 + inSrc (4 + p / 8) j)).getLsbD p ^^ (K (8 + inSrc (4 + p / 8) j)).getLsbD p))
    (hSR : ∀ j < 8, ∀ p < 32, (SR j).getLsbD p = (sbox1 (bsByte XR p)).getLsbD j)
    (hR' : ∀ w < 2, ∀ j < 8, ∀ p < 32, (R' (8 * w + j)).getLsbD p =
      ((R (8 * w + j)).getLsbD p ^^ rowSel YL SR j (p % 8) (pRow (4 * w + p / 8)))) :
    HalfRel R' fun b => d2 b ^^^ f (d1 b) k := by
  intro b hb c hc j hj
  have hp : 8 * (c % 4) + b < 32 := by omega
  have := hR' (c / 4) (by omega) j hj _ hp
  rw [this, hR b hb c hc j hj, byteOf_xor, BitVec.getLsbD_xor, getLsbD_byteOf_f _ _ hc hj]
  congr 1
  rw [show (8 * (c % 4) + b) % 8 = b by omega, show 4 * (c / 4) + (8 * (c % 4) + b) / 8 = c by omega]
  refine rowSel_eq fun i hi => ?_
  have hi8 := pRow_lt hi
  -- The S-box input byte of byte `i` of the half, at position `8 (i % 4) + b`.
  have hx : ∀ X : Nat → BitVec 32, (∀ j' < 8, (X j').getLsbD (8 * (i % 4) + b) =
      ((Q (8 * (i / 4) + inSrc i j')).getLsbD (8 * (i % 4) + b) ^^
        (K (8 * (i / 4) + inSrc i j')).getLsbD (8 * (i % 4) + b))) →
      bsByte X (8 * (i % 4) + b) = ofBits 8 fun j' => (byteOf (d1 b ^^^ k) i).getLsbD (inSrc i j') := by
    intro X hX
    refine byte_ext fun j' hj' => ?_
    have hs := inSrc_lt (c := i) hj'
    rw [getLsbD_bsByte _ _ hj', getLsbD_ofBits]
    simp only [hj', decide_true, Bool.true_and]
    rw [hX j' hj', hQ b hb i hi8 _ hs, hK b hb i hi8 _ hs, byteOf_xor, BitVec.getLsbD_xor]
  have ho := outSrc_lt (c := i) hj
  simp only [ySel]
  split
  · rename_i hi4
    rw [hYL j hj _ (by omega), show (8 * i + b) / 8 = i by omega, hSL _ ho _ (by omega)]
    rw [show 8 * i + b = 8 * (i % 4) + b by omega, hx XL fun j' hj' => by
      rw [hXL j' hj' _ (by omega), show (8 * (i % 4) + b) / 8 = i by omega,
        show i / 4 = 0 by omega, Nat.mul_zero, Nat.zero_add]]
    exact sbox_sel hi8 hj
  · rename_i hi4
    rw [hSR _ ho _ (by omega)]
    rw [show 8 * (i - 4) + b = 8 * (i % 4) + b by omega, hx XR fun j' hj' => by
      rw [hXR j' hj' _ (by omega), show 4 + (8 * (i % 4) + b) / 8 = i by omega,
        show i / 4 = 1 by omega, Nat.mul_one]]
    exact sbox_sel hi8 hj

/-! ## FL and FLINV

`x2 ^= (x1 & k1) <<< 1` (`RotStep`): plane `j` of the right word takes the
AND of plane `j - 1` of the left word and the subkey's (for `j ≥ 1`), or of
plane 7 a byte up, cyclically (for `j = 0`, the bit the rotation moves to
the next byte). `x1 ^= x2 | k2` (`OrStep`): plane `j` of the left word
takes the OR of the right word's and the subkey's plane `j`. -/

/-- The position the rotation step reads for position `p` of plane `j`. -/
def rotPos (j p : Nat) : Nat := if j = 0 then (p + 8) % 32 else p

def RotStep (Q K Q' : Nat → BitVec 32) : Prop :=
  (∀ j < 8, Q' j = Q j) ∧ ∀ j < 8, ∀ p < 32, (Q' (8 + j)).getLsbD p = ((Q (8 + j)).getLsbD p ^^
    ((Q ((j + 7) % 8)).getLsbD (rotPos j p) && (K ((j + 7) % 8)).getLsbD (rotPos j p)))

def OrStep (Q K Q' : Nat → BitVec 32) : Prop :=
  (∀ j < 8, Q' (8 + j) = Q (8 + j)) ∧ ∀ j < 8, ∀ p < 32, (Q' j).getLsbD p = ((Q j).getLsbD p ^^
    ((Q (8 + j)).getLsbD p || (K (8 + j)).getLsbD p))

/-- The rotation step, in the right word, is `x2 ^ (x1 & k1) <<< 1`: bit `n < 32`. -/
theorem rot_bit {Q K Q' : Nat → BitVec 32} {d : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel Q d) (hK : HalfRel K fun _ => k) (hr : RotStep Q K Q') {j p : Nat}
    (hj : j < 8) (hp : p < 32) :
    (Q' (8 + j)).getLsbD p = ((d (p % 8)).getLsbD (24 - 8 * (p / 8) + j) ^^
      ((d (p % 8)).getLsbD (32 + (24 - 8 * (p / 8) + j + 31) % 32) &&
        k.getLsbD (32 + (24 - 8 * (p / 8) + j + 31) % 32))) := by
  have h8 := half_bit hQ (w := 1) (by omega) hj hp
  rw [hr.2 j hj p hp, show 8 * 1 + j = 8 + j by omega] at *
  rw [h8, show 56 - 8 * (4 * 1 + p / 8) + j = 24 - 8 * (p / 8) + j by omega]
  congr 1
  have hj7 : (j + 7) % 8 < 8 := Nat.mod_lt _ (by omega)
  have hrp : rotPos j p < 32 := by simp only [rotPos]; split <;> omega
  have e1 := half_bit hQ (w := 0) (by omega) hj7 hrp
  have e2 := half_bit hK (w := 0) (by omega) hj7 hrp
  simp only [Nat.mul_zero, Nat.zero_add] at e1 e2
  rw [e1, e2]
  have hb : rotPos j p % 8 = p % 8 := by simp only [rotPos]; split <;> omega
  rw [hb]
  have : 56 - 8 * (4 * 0 + rotPos j p / 8) + (j + 7) % 8 = 32 + (24 - 8 * (p / 8) + j + 31) % 32 := by
    simp only [rotPos]; split <;> omega
  rw [show 4 * 0 = 0 from rfl, Nat.zero_add] at this
  rw [this]

/-- `HalfRel` from the bits of each plane. -/
theorem HalfRel.of_bits {Q : Nat → BitVec 32} {d : Nat → BitVec 64}
    (h : ∀ w < 2, ∀ j < 8, ∀ p < 32,
      (Q (8 * w + j)).getLsbD p = (d (p % 8)).getLsbD (56 - 8 * (4 * w + p / 8) + j)) :
    HalfRel Q d := by
  intro b hb c hc j hj
  have := h (c / 4) (by omega) j hj (8 * (c % 4) + b) (by omega)
  rw [this, getLsbD_byteOf _ hc hj, show (8 * (c % 4) + b) % 8 = b by omega,
    show 4 * (c / 4) + (8 * (c % 4) + b) / 8 = c by omega]

theorem fl_rel {Q K Q₁ Q₂ : Nat → BitVec 32} {d : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel Q d) (hK : HalfRel K fun _ => k) (h₁ : RotStep Q K Q₁) (h₂ : OrStep Q₁ K Q₂) :
    HalfRel Q₂ fun b => fl (d b) k := by
  -- The right word, after the first step.
  have hr : ∀ j < 8, ∀ p < 32,
      (Q₁ (8 + j)).getLsbD p = (fl (d (p % 8)) k).getLsbD (24 - 8 * (p / 8) + j) := by
    intro j hj p hp
    rw [rot_bit hQ hK h₁ hj hp, getLsbD_fl_lo _ _ (by omega)]
  refine HalfRel.of_bits fun w hw j hj p hp => ?_
  rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
  · have e1 := half_bit hQ (w := 0) (by omega) hj hp
    have e2 := half_bit hK (w := 1) (by omega) hj hp
    simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at e1 e2 ⊢
    rw [show 8 + j = 8 + j from rfl] at e2
    rw [h₂.2 j hj p hp, h₁.1 j hj, hr j hj p hp, e1, e2,
      getLsbD_fl_hi (d (p % 8)) k (n := 56 - 8 * (p / 8) + j) (by omega) (by omega),
      show 56 - 8 * (p / 8) + j - 32 = 24 - 8 * (p / 8) + j by omega,
      show 56 - 8 * (4 + p / 8) + j = 24 - 8 * (p / 8) + j by omega]
  · simp only [Nat.mul_one]
    rw [h₂.1 j hj, hr j hj p hp, show 56 - 8 * (4 * 1 + p / 8) + j = 24 - 8 * (p / 8) + j by omega]

theorem flinv_rel {Q K Q₁ Q₂ : Nat → BitVec 32} {d : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel Q d) (hK : HalfRel K fun _ => k) (h₁ : OrStep Q K Q₁) (h₂ : RotStep Q₁ K Q₂) :
    HalfRel Q₂ fun b => flinv (d b) k := by
  -- After the first step, the left word is `y1 ^ (y2 | k2)`, the right `y2`.
  let Y : Nat → BitVec 64 := fun b => ((flinv (d b) k) >>> 32).setWidth 32 ++ (d b).setWidth 32
  have hYhi : ∀ b, ∀ n, 32 ≤ n → n < 64 → (Y b).getLsbD n = (flinv (d b) k).getLsbD n := by
    intro b n h1 h2
    simp only [Y, BitVec.getLsbD_append, show ¬ n < 32 by omega, ite_false,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, show n - 32 < 32 by omega, decide_true,
      Bool.true_and]
    congr 1; omega
  have hYlo : ∀ b, ∀ n, n < 32 → (Y b).getLsbD n = (d b).getLsbD n := by
    intro b n h1
    simp only [Y, BitVec.getLsbD_append, h1, ite_true, BitVec.getLsbD_setWidth, decide_true,
      Bool.true_and]
  have h₁r : HalfRel Q₁ Y := by
    refine HalfRel.of_bits fun w hw j hj p hp => ?_
    rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
    · have e1 := half_bit hQ (w := 0) (by omega) hj hp
      have e2 := half_bit hQ (w := 1) (by omega) hj hp
      have e3 := half_bit hK (w := 1) (by omega) hj hp
      simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at e1 e2 e3 ⊢
      rw [h₁.2 j hj p hp, e1, e2, e3, hYhi _ _ (by omega) (by omega),
        getLsbD_flinv_hi (d (p % 8)) k (n := 56 - 8 * (p / 8) + j) (by omega) (by omega),
        show 56 - 8 * (p / 8) + j - 32 = 56 - 8 * (4 + p / 8) + j by omega]
    · have e2 := half_bit hQ (w := 1) (by omega) hj hp
      simp only [Nat.mul_one] at e2 ⊢
      rw [h₁.1 j hj, e2, hYlo _ _ (by omega)]
  refine HalfRel.of_bits fun w hw j hj p hp => ?_
  rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
  · have e1 := half_bit h₁r (w := 0) (by omega) hj hp
    simp only [Nat.mul_zero, Nat.zero_add] at e1 ⊢
    rw [h₂.1 j hj, e1, hYhi _ _ (by omega) (by omega)]
  · simp only [Nat.mul_one]
    rw [rot_bit h₁r hK h₂ hj hp, hYlo _ _ (by omega), hYhi _ _ (by omega) (by omega),
      show 56 - 8 * (4 + p / 8) + j = 24 - 8 * (p / 8) + j by omega,
      getLsbD_flinv_lo (d (p % 8)) k (n := 24 - 8 * (p / 8) + j) (by omega)]

end VG.Proof.Camellia.W32
