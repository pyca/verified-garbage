module

public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InRange
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.Encoding

/-!
# The copied draw is the specification's candidate (x86)

The bytes `copy` leaves at the draw's place (`copiedList`) decode to the
candidate of FIPS 186-4's rejection sampling, `inRange` accepts exactly the
candidates in `[1, q)`, and the whole `q_len`-byte scalar, with its zero
padding, encodes the candidate.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom

/-- q, as the specification reads it. -/
abbrev rq (s₀ : State) : Nat := Spec.Dsa.decodeBE (rQBytes s₀)

theorem qSig_decode (s₀ : State) : Spec.Dsa.decodeBE (qSig s₀) = rq s₀ :=
  VG.Proof.Dsa.random_significant_drop _

theorem rWidth_eq (s₀ : State) : Spec.Dsa.Random.drawBytes (rq s₀) = rWidth s₀ :=
  VG.Proof.Dsa.random_drawBytes_scan _

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
theorem masked_head (s₀ : State) (b : Byte) (hpos : 0 < rWidth s₀) :
    (b.setWidth 32 &&& maskValue (rLead s₀).toNat).setWidth 8 =
      b &&& BitVec.ofNat 8 (2 ^ ((rLead s₀).toNat.log2 + 1) - 1) := by
  have hb : 0 < (rLead s₀).toNat := by
    have hn := VG.Proof.Dsa.significant_nonzero (rQBytes s₀)
    have hz : (rLead s₀).toNat ≠ 0 := by
      intro he
      have h0 : rWidth s₀ = 0 := hn.mpr (BitVec.eq_of_toNat_eq he)
      omega
    omega
  have hlog : (rLead s₀).toNat.log2 + 1 ≤ 8 := by
    have h := (Nat.log2_lt (by omega)).mpr (rLead s₀).isLt
    omega
  rw [maskValue_eq _ hb (rLead s₀).isLt, BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (by decide),
    BitVec.setWidth_eq, BitVec.setWidth_ofNat_of_le (by decide)]

/-- The copied bytes decode to the candidate. -/
theorem copied_candidate (s₀ : State) {bs : List Byte} (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀) :
    Spec.Dsa.decodeBE (copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)) =
      Spec.Dsa.Random.candidate (rq s₀) bs := by
  obtain ⟨b, tl, rfl⟩ : ∃ b tl, bs = b :: tl := by
    cases bs with
    | nil => simp at hl; omega
    | cons b tl => exact ⟨b, tl, rfl⟩
  have hw : tl.length + 1 = rWidth s₀ := by simpa using hl
  rw [← hw, copiedList_eq, masked_head s₀ b hpos, VG.Proof.Dsa.random_candidate_mask _ b tl hw]

theorem accepts_candidate (s₀ : State) {bs : List Byte} (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀) :
    accepts s₀ (copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)) =
      decide (0 < Spec.Dsa.Random.candidate (rq s₀) bs ∧ Spec.Dsa.Random.candidate (rq s₀) bs < rq s₀) := by
  rw [accepts, copied_candidate s₀ hl hpos, qSig_decode]

theorem decode_padding (bs : List Byte) (n : Nat) :
    Spec.Dsa.decodeBE (List.replicate n 0 ++ bs) = Spec.Dsa.decodeBE bs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, VG.Proof.Dsa.decodeBE_zero_cons]
    exact ih

/-- The whole scalar, its padding and the candidate's bytes, encodes the candidate. -/
theorem nonce_encodes {s₀ : State} (A : KeyABI s₀) {m : Mem} {bs : List Byte}
    (hl : bs.length = rWidth s₀) (hpos : 0 < rWidth s₀)
    (hpad : ∀ i < (rQBytes s₀).length - rWidth s₀, m (off (rBase s₀) (oNonce + i)) = 0)
    (hc : ∀ i < rWidth s₀, m (off (rBase s₀) (drawPlace s₀ + i)) = copied bs (maskValue (rLead s₀).toNat) i) :
    Spec.Rsa.bytesAt m (off (rBase s₀) oNonce) (rQBytes s₀).length =
      Spec.Dsa.encodeBE (rQBytes s₀).length (Spec.Dsa.Random.candidate (rq s₀) bs) := by
  have hfit : rWidth s₀ ≤ (rQBytes s₀).length := VG.Proof.Dsa.significant_fits (rQBytes s₀)
  have hql := rQBytes_le A
  let cs := copiedList bs (maskValue (rLead s₀).toNat) (rWidth s₀)
  let pad := (rQBytes s₀).length - rWidth s₀
  let padded := List.replicate pad (0 : Byte) ++ cs
  have hpLen : padded.length = (rQBytes s₀).length := by
    simp only [padded, cs, List.length_append, List.length_replicate, copiedList_length]; omega
  have hpBytes : Spec.Rsa.bytesAt m (off (rBase s₀) oNonce) (rQBytes s₀).length = padded := by
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range, hpLen]
    · intro i hi hj
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      have he : off (rBase s₀) oNonce + BitVec.ofNat 64 i = off (rBase s₀) (oNonce + i) := by
        simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
      rw [he]
      by_cases hip : i < pad
      · rw [hpad i hip]
        simp only [padded, List.getElem_append_left (as := List.replicate pad (0 : Byte)) (bs := cs)
          (i := i) (by simpa only [List.length_replicate] using hip), List.getElem_replicate]
      · have hk : i - pad < rWidth s₀ := by simp only [hpLen] at hj; omega
        rw [show oNonce + i = drawPlace s₀ + (i - pad) by unfold drawPlace; omega, hc _ hk]
        simp only [padded, List.getElem_append_right (as := List.replicate pad (0 : Byte)) (bs := cs) (i := i)
          (by simpa only [List.length_replicate] using Nat.le_of_not_lt hip), List.length_replicate]
        simp only [cs, copiedList, List.getElem_map, List.getElem_range]
  rw [hpBytes, ← hpLen, ← copied_candidate s₀ hl hpos, ← decode_padding cs pad,
    VG.Proof.Dsa.encodeBE_decodeBE]

end VG.Proof.Dsa.X86.KeyRandom
