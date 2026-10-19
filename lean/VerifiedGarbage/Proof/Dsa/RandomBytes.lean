module
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Spec.Dsa.Random

import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The sampler's byte arithmetic, for any target

What the randomized signers compute from the bytes of q and of a draw,
independent of the instructions that compute it: the scan of q for its
significant bytes (`scanNext`, `scanAfter`), the mask of the leading byte
(`maskValue`), the masked draw (`copiedList`), which decodes to the
specification's candidate (`copied_candidate`), and its acceptance
(`acceptsOf`).
-/

@[expose] public section

namespace VG.Proof.Dsa

open VG

/-! ## The scan of q -/

/-- The scan's pair after its byte `b`, with `remaining` bytes from it on. -/
def scanNext (found : Nat × Byte) (remaining : Nat) (b : Byte) : Nat × Byte :=
  if found.1 = 0 ∧ b ≠ 0 then (remaining, b) else found

/-- The scan's result from `found`, with `bs` to read. -/
def scanFinish (found : Nat × Byte) (bs : List Byte) : Nat × Byte :=
  if found.1 = 0 then significant bs else found

theorem scanFinish_step (found : Nat × Byte) (b : Byte) (bs : List Byte) :
    scanFinish (scanNext found (bs.length + 1) b) bs = scanFinish found (b :: bs) := by
  by_cases hf : found.1 = 0
  · by_cases hb : b = 0
    · have h1 : scanNext found (bs.length + 1) b = found := by simp [scanNext, hb]
      rw [h1]
      simp only [scanFinish, hf, ite_true, significant, hb]
    · have h1 : scanNext found (bs.length + 1) b = (bs.length + 1, b) := by
        simp only [scanNext, hf, ne_eq, hb, not_false_eq_true, and_self, ite_true]
      rw [h1]
      simp only [scanFinish, hf, ite_true, significant, hb, ite_false, Nat.add_one_ne_zero]
  · have h1 : scanNext found (bs.length + 1) b = found := by simp [scanNext, hf]
    rw [h1]
    simp only [scanFinish, hf, ite_false]

theorem scanFinish_nil {found : Nat × Byte} (hz : found.1 = 0 → found.2 = 0) :
    scanFinish found [] = found := by
  unfold scanFinish
  split
  · rename_i h
    exact Prod.ext h.symm (hz h).symm
  · rfl

/-- The scan's pair after the first `j` bytes of `bs`. -/
def scanAfter (bs : List Byte) : Nat → Nat × Byte
  | 0 => (0, 0)
  | j + 1 => scanNext (scanAfter bs j) (bs.length - j) (bs.getD j 0)

theorem scanAfter_bound (bs : List Byte) (hl : bs.length < 2 ^ 32) :
    ∀ j, (scanAfter bs j).1 < 2 ^ 32 ∧ ((scanAfter bs j).1 = 0 → (scanAfter bs j).2 = 0)
  | 0 => ⟨by simp [scanAfter], fun _ => rfl⟩
  | j + 1 => by
    have ih := scanAfter_bound bs hl j
    unfold scanAfter scanNext
    split
    · rename_i hc
      refine ⟨by simp only; omega, fun e => ?_⟩
      simp only at e
      exfalso; apply hc.2
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    · exact ih

/-- After all of `bs`, the scan is `significant bs`. -/
theorem scanAfter_finish (bs : List Byte) (hl : bs.length < 2 ^ 32) :
    ∀ j ≤ bs.length, scanFinish (scanAfter bs j) (bs.drop j) = significant bs
  | 0, _ => by simp [scanAfter, scanFinish]
  | j + 1, hj => by
    have ih := scanAfter_finish bs hl j (by omega)
    have hd : bs.drop j = bs[j] :: bs.drop (j + 1) := List.drop_eq_getElem_cons (by omega)
    rw [hd, ← scanFinish_step] at ih
    have hl' : (bs.drop (j + 1)).length + 1 = bs.length - j := by rw [List.length_drop]; omega
    rw [hl', show bs[j] = bs.getD j 0 by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl] at ih
    exact ih

theorem scanAfter_length (bs : List Byte) (hl : bs.length < 2 ^ 32) :
    scanAfter bs bs.length = significant bs := by
  have := scanAfter_finish bs hl bs.length (Nat.le_refl _)
  rwa [List.drop_length, scanFinish_nil (scanAfter_bound bs hl _).2] at this

/-! ## The mask of the leading byte -/

/-- The mask that keeps the significant bits of the leading byte `n`. -/
def maskValue (n : Nat) : BitVec 32 :=
  if n < 2 then 1 else if n < 4 then 3 else if n < 8 then 7 else
  if n < 16 then 15 else if n < 32 then 31 else if n < 64 then 63 else
  if n < 128 then 127 else 255

/-- The selected mask keeps exactly the significant bits of a nonzero byte. -/
theorem maskValue_eq (n : Nat) (hpos : 0 < n) (hbound : n < 256) :
    maskValue n = BitVec.ofNat 32 (2 ^ (n.log2 + 1) - 1) := by
  have key : ∀ k, 2 ^ k ≤ n → n < 2 ^ (k + 1) → n.log2 = k := fun k h₁ h₂ =>
    (Nat.log2_eq_iff (by omega)).mpr ⟨h₁, h₂⟩
  unfold maskValue
  split
  · rw [key 0 (show 1 ≤ n by omega) (by omega)]; rfl
  split
  · rw [key 1 (by omega) (by omega)]; rfl
  split
  · rw [key 2 (by omega) (by omega)]; rfl
  split
  · rw [key 3 (by omega) (by omega)]; rfl
  split
  · rw [key 4 (by omega) (by omega)]; rfl
  split
  · rw [key 5 (by omega) (by omega)]; rfl
  split
  · rw [key 6 (by omega) (by omega)]; rfl
  · rw [key 7 (by omega) (by omega)]; rfl

/-! ## The candidate -/

/-- What the nonce's byte `i` from the draw's place becomes: the first byte
masked. -/
def copied (bs : List Byte) (mask : BitVec 32) (i : Nat) : Byte :=
  if i = 0 then ((bs.getD 0 0).setWidth 32 &&& mask).setWidth 8 else bs.getD i 0

/-- The candidate's bytes. -/
def copiedList (bs : List Byte) (mask : BitVec 32) (w : Nat) : List Byte :=
  (List.range w).map (copied bs mask)

theorem copiedList_length (bs : List Byte) (mask : BitVec 32) (w : Nat) : (copiedList bs mask w).length = w := by
  simp [copiedList]

theorem copiedList_getD (bs : List Byte) (mask : BitVec 32) {w i : Nat} (hi : i < w) :
    (copiedList bs mask w).getD i 0 = copied bs mask i := by
  simp [copiedList, List.getD_eq_getElem?_getD, hi]

theorem copiedList_eq {b : Byte} {bs : List Byte} (mask : BitVec 32) :
    copiedList (b :: bs) mask (bs.length + 1) = ((b.setWidth 32 &&& mask).setWidth 8) :: bs := by
  apply List.ext_getElem
  · simp [copiedList]
  · intro i h₁ h₂
    simp only [copiedList, List.getElem_map, List.getElem_range, copied]
    cases i with
    | zero => simp
    | succ i =>
      simp only [Nat.add_one_ne_zero, ite_false, List.getElem_cons_succ]
      simp only [List.length_cons] at h₂
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < bs.length by omega)]

/-- The leading byte's mask, as `random_candidate_mask` states it. -/
theorem masked_head (qb : List Byte) (b : Byte) (hpos : 0 < (significant qb).1) :
    (b.setWidth 32 &&& maskValue (significant qb).2.toNat).setWidth 8 =
      b &&& BitVec.ofNat 8 (2 ^ ((significant qb).2.toNat.log2 + 1) - 1) := by
  have hb : 0 < (significant qb).2.toNat := by
    have hn := significant_nonzero qb
    have hz : (significant qb).2.toNat ≠ 0 := by
      intro he
      have h0 : (significant qb).1 = 0 := hn.mpr (BitVec.eq_of_toNat_eq he)
      omega
    omega
  rw [maskValue_eq _ hb (significant qb).2.isLt, BitVec.setWidth_and,
    BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, BitVec.setWidth_ofNat_of_le (by decide)]

/-- The copied bytes decode to the candidate. -/
theorem copied_candidate (qb : List Byte) {bs : List Byte} (hl : bs.length = (significant qb).1)
    (hpos : 0 < (significant qb).1) :
    Spec.Dsa.decodeBE (copiedList bs (maskValue (significant qb).2.toNat) (significant qb).1) =
      Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qb) bs := by
  obtain ⟨b, tl, rfl⟩ : ∃ b tl, bs = b :: tl := by
    cases bs with
    | nil => simp at hl; omega
    | cons b tl => exact ⟨b, tl, rfl⟩
  have hw : tl.length + 1 = (significant qb).1 := by simpa using hl
  rw [← hw, copiedList_eq, masked_head qb b hpos, random_candidate_mask _ b tl hw]

/-- q's significant bytes. -/
abbrev qSigOf (qb : List Byte) : List Byte := qb.drop (qb.length - (significant qb).1)

theorem qSigOf_length (qb : List Byte) : (qSigOf qb).length = (significant qb).1 := by
  have := significant_fits qb
  simp only [qSigOf, List.length_drop]; omega

/-- Whether the candidate `cs` is accepted: nonzero and below q. -/
def acceptsOf (qb cs : List Byte) : Bool :=
  decide (0 < Spec.Dsa.decodeBE cs ∧ Spec.Dsa.decodeBE cs < Spec.Dsa.decodeBE (qSigOf qb))

theorem accepts_candidate (qb : List Byte) {bs : List Byte} (hl : bs.length = (significant qb).1)
    (hpos : 0 < (significant qb).1) :
    acceptsOf qb (copiedList bs (maskValue (significant qb).2.toNat) (significant qb).1) =
      decide (0 < Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qb) bs ∧
        Spec.Dsa.Random.candidate (Spec.Dsa.decodeBE qb) bs < Spec.Dsa.decodeBE qb) := by
  rw [acceptsOf, copied_candidate qb hl hpos, random_significant_drop]

theorem decode_padding (bs : List Byte) (n : Nat) :
    Spec.Dsa.decodeBE (List.replicate n 0 ++ bs) = Spec.Dsa.decodeBE bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, decodeBE_zero_cons]
    exact ih

/-! ## Words -/

/-- The borrow out of `a - (b + c)`, by its sign bit. -/
theorem borrow_bit {a x : Nat} (ha : a < 256) (hx : x ≤ 256) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 x) >>> 31 = BitVec.ofNat 32 (if a < x then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := a) (by omega), Nat.mod_eq_of_lt (a := x) (by omega), Nat.shiftRight_eq_div_pow]
  split <;> rw [BitVec.toNat_ofNat] <;> omega

theorem toNat_setWidth8 (b : Byte) : (b.setWidth 32).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide : 2 ^ 8 ≤ 2 ^ 32))]

theorem setWidth8_ofNat (b : Byte) : b.setWidth 32 = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq; rw [toNat_setWidth8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem byte_setWidth (b : Byte) : (b.setWidth 32).setWidth 8 = b := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

end VG.Proof.Dsa
