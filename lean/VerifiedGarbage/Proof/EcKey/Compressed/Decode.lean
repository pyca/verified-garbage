module

public import VerifiedGarbage.Impl.EcKey.Compressed
public import VerifiedGarbage.Proof.EcKey.Compressed.Root

/-! # The functional decoder meets the merged SEC 1 relation

Soundness uses the explicit square and parity checks. Completeness uses
the curve's proven root interface, so no valid encoding can be rejected
merely because a particular candidate was not found.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed

open Spec.Weierstrass Spec.EcKey VG.Impl.EcKey.Compressed

/-- The parser and final candidate checks in the form the assembly proves. -/
theorem decode_checked_eq {C : Curve} (root : Fe C → Fe C) {bs : List Byte}
    (hlen : bs.length = C.len + 1) {tag : Byte} (hb : bs.head? = some tag)
    {x : Nat} (hx : ofBytes (bs.drop 1) = x) :
    decode C root bs =
      let xf := Fin.ofNat C.p x
      let rhs := xf * xf * xf + Fin.ofNat C.p C.a * xf + Fin.ofNat C.p C.b
      let y := chooseRoot (root rhs) (tag.toNat % 2)
      if ((tag = 2 ∨ tag = 3) ∧ x < C.p) ∧ (y * y = rhs ∧ y.val % 2 = tag.toNat % 2) then
        some (.affine xf y) else none := by
  unfold decode
  simp only [hlen, ite_true, hb, hx]
  by_cases ht : tag = 2 ∨ tag = 3
  · simp only [ht, ite_true, true_and]
    by_cases hxp : x < C.p
    · simp only [hxp, dite_true, true_and]
      have he : (⟨x, hxp⟩ : Fe C) = Fin.ofNat C.p x := by
        apply Fin.ext
        simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hxp]
      rw [he]
      simp only [recoverRoot, chooseRoot]
      split <;> split <;> rfl
    · simp only [hxp, dite_false, false_and, ite_false]
  · simp only [ht, ite_false, false_and]

/-- Every returned point satisfies the exact compressed encoding relation. -/
theorem decode_sound {C : Curve} {root : Fe C → Fe C} {bs : List Byte} {Q : Point C}
    (h : decode C root bs = some Q) : matchesCompressedPublicKey C bs Q := by
  unfold decode at h
  split at h
  next hlen =>
    split at h
    · contradiction
    next tag htag =>
      split at h
      next hlead =>
        dsimp only at h
        split at h
        next hx =>
          simp only [Option.map_eq_some_iff] at h
          obtain ⟨y, hy, rfl⟩ := h
          obtain ⟨hsq, hpar⟩ := recoverRoot_some hy
          refine ⟨hlen, ?_, rfl, ?_⟩
          · rw [htag]
            rcases hlead with rfl | rfl
            · change y.val % 2 = 0 at hpar
              rw [hpar]
              rfl
            · change y.val % 2 = 1 at hpar
              rw [hpar]
              rfl
          · exact decide_eq_true hsq
        · contradiction
      · contradiction
  · contradiction

/-- Every matching finite point causes the decoder to return a point. -/
theorem decode_complete {C : Curve} {root : Fe C → Fe C} (hf : RootFacts root)
    {bs : List Byte} {Q : Point C} (h : matchesCompressedPublicKey C bs Q) :
    ∃ R, decode C root bs = some R := by
  cases Q with
  | infinity => exact False.elim h
  | affine x y =>
    obtain ⟨hlen, htag, hx, hcurve⟩ := h
    have hpar : (BitVec.ofNat 8 (2 + y.val % 2)).toNat % 2 = y.val % 2 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 + y.val % 2 < 256 by omega)]
      omega
    have hlead : (BitVec.ofNat 8 (2 + y.val % 2) : Byte) = 2 ∨
        (BitVec.ofNat 8 (2 + y.val % 2) : Byte) = 3 := by
      rcases Nat.mod_two_eq_zero_or_one y.val with he | he
      · exact Or.inl (by rw [he]; rfl)
      · exact Or.inr (by rw [he]; rfl)
    have hsq : y * y = x * x * x + Fin.ofNat C.p C.a * x + Fin.ofNat C.p C.b :=
      of_decide_eq_true hcurve
    have hr := recoverRoot_complete hf ⟨y, hsq, (rfl : y.val % 2 = y.val % 2)⟩
    obtain ⟨r, hr⟩ := hr
    simp only [decode, hlen, ↓reduceIte, htag, hlead, hx, x.isLt, hpar, dite_true]
    rw [hr]
    exact ⟨.affine x r, rfl⟩

/-- Rejection has exactly the meaning required by the decompression API. -/
theorem decode_none_iff {C : Curve} {root : Fe C → Fe C} (hf : RootFacts root) (bs : List Byte) :
    decode C root bs = none ↔ ¬ ∃ Q, matchesCompressedPublicKey C bs Q := by
  constructor
  · intro h ⟨Q, hQ⟩
    obtain ⟨R, hR⟩ := decode_complete hf hQ
    rw [h] at hR
    contradiction
  · intro h
    cases he : decode C root bs with
    | none => rfl
    | some Q => exact False.elim (h ⟨Q, decode_sound he⟩)

end VG.Proof.EcKey.Compressed
