module

public import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Random

/-! # The domain check and key derivation as the checks the implementations make

Both implementations check the domain's shape (supported bit lengths, odd p
and q) and then its algebra, as the signer does; derivation checks x's range
and y's, and y's order follows from g's. -/

@[expose] public section

namespace VG.Proof.Dsa
open VG

/-- y^q = 1 for y = g^x when g^q = 1. -/
theorem powMod_order_of_generator {g x q p : Nat} (hp : 1 < p) (hg : Spec.Dsa.powMod g q p = 1) :
    Spec.Dsa.powMod (Spec.Dsa.powMod g x p) q p = 1 := by
  rw [powMod_eq] at hg
  rw [powMod_eq, powMod_eq, ← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul, Nat.pow_mod, hg,
    Nat.one_pow, Nat.mod_eq_of_lt hp]

theorem paramsBytes_eq (pLen qLen : Nat) (params : List Byte) :
    Spec.Dsa.paramsBytes pLen qLen params = ⟨Spec.Dsa.decodeBE (params.take pLen),
      Spec.Dsa.decodeBE ((params.drop pLen).take qLen),
      Spec.Dsa.decodeBE ((params.drop (pLen + qLen)).take pLen)⟩ := rfl

theorem encodeParams_paramsBytes {pLen qLen : Nat} {params : List Byte}
    (h : params.length = 2 * pLen + qLen) :
    Spec.Dsa.encodeParams pLen qLen (Spec.Dsa.paramsBytes pLen qLen params) = params := by
  have h1 : (params.take pLen).length = pLen := by simp only [List.length_take]; omega
  have h2 : ((params.drop pLen).take qLen).length = qLen := by
    simp only [List.length_take, List.length_drop]; omega
  have h3 : ((params.drop (pLen + qLen)).take pLen).length = pLen := by
    simp only [List.length_take, List.length_drop]; omega
  have e (bs : List Byte) (n : Nat) (h : bs.length = n) : Spec.Dsa.encodeBE n (Spec.Dsa.decodeBE bs) = bs :=
    h ▸ encodeBE_decodeBE bs
  rw [paramsBytes_eq, Spec.Dsa.encodeParams]
  dsimp only
  rw [e _ _ h1, e _ _ h2, e _ _ h3]
  rw [List.take_of_length_le (l := params.drop (pLen + qLen)) (by simp only [List.length_drop]; omega),
    ← List.drop_drop, List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- The checks of a domain both functions make: the shape's, then the
signer's on g (`signingKeyAccepted` with y = g). -/
theorem checkParametersBytes_eq {pLen qLen : Nat} {params : List Byte}
    (hl : Spec.Dsa.lengthsValid pLen qLen) (hpl : params.length = 2 * pLen + qLen) :
    let a := Spec.Dsa.paramsBytes pLen qLen params
    Spec.Dsa.checkParametersBytes pLen qLen params =
      (decide (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength a.p) (Spec.Dsa.bitLength a.q) ∧
        a.p % 2 = 1 ∧ a.q % 2 = 1) &&
      (decide (Spec.Dsa.powMod a.g a.q a.p = 1) && (decide ((a.p - 1) % a.q = 0) &&
        (decide (1 < a.g ∧ a.g < a.p) && (decide (1 < a.g ∧ a.g < a.p) && true))))) := by
  intro a
  unfold Spec.Dsa.checkParametersBytes
  simp only [hl, hpl, decide_true, beq_self_eq_true, Bool.true_and, Bool.and_true, Bool.and_self]
  apply Bool.eq_iff_iff.mpr
  simp only [Spec.Dsa.parametersValid, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨hs, hp, hq, _, hd, hg1, hg2, hgq⟩
    exact ⟨⟨hs, hp, hq⟩, hgq, hd, hg1, hg2⟩
  · rintro ⟨⟨hs, hp, hq⟩, hgq, hd, hg1, hg2⟩
    exact ⟨hs, hp, hq, (supported_bounds hs).2.2, hd, hg1, hg2, hgq⟩

theorem derive_checks (pLen qLen : Nat) (a : Spec.Dsa.Params) (n : Nat) (out : List Byte)
    (henc : Spec.Dsa.encodePrivateKey pLen qLen ⟨a, Spec.Dsa.powMod a.g n a.p, some n⟩ = out) :
    (if (!(decide (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength a.p) (Spec.Dsa.bitLength a.q) ∧
          a.p % 2 = 1 ∧ a.q % 2 = 1) &&
        (decide (Spec.Dsa.powMod a.g a.q a.p = 1) &&
          (decide ((a.p - 1) % a.q = 0) && decide (1 < a.g ∧ a.g < a.p))))) = true then none else
      match Spec.Dsa.generate a [n] with
      | none => none
      | some key => if Spec.Dsa.keyValid key then some (Spec.Dsa.encodePrivateKey pLen qLen key) else none) =
    if (decide (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength a.p) (Spec.Dsa.bitLength a.q) ∧
          a.p % 2 = 1 ∧ a.q % 2 = 1) &&
        (decide (Spec.Dsa.powMod a.g a.q a.p = 1) && (decide ((a.p - 1) % a.q = 0) &&
          (decide (1 < Spec.Dsa.powMod a.g n a.p ∧ Spec.Dsa.powMod a.g n a.p < a.p) &&
            (decide (1 < a.g ∧ a.g < a.p) && decide (0 < n ∧ n < a.q)))))) = true
    then some out else none := by
  have key : Spec.Dsa.generate a [n] =
      if 0 < n ∧ n < a.q then some ⟨a, Spec.Dsa.powMod a.g n a.p, some n⟩ else none := by
    unfold Spec.Dsa.generate Spec.Dsa.sampleScalar
    by_cases h : 0 < n ∧ n < a.q <;> simp [h]
  rw [key]
  by_cases hs : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength a.p) (Spec.Dsa.bitLength a.q) ∧
      a.p % 2 = 1 ∧ a.q % 2 = 1
  rotate_left
  · simp only [hs, decide_false, Bool.false_and, Bool.not_false, reduceIte]
    rfl
  by_cases hgq : Spec.Dsa.powMod a.g a.q a.p = 1
  rotate_left
  · simp only [hgq, decide_false, Bool.false_and, Bool.and_false, Bool.not_false, reduceIte]
    rfl
  by_cases hd : (a.p - 1) % a.q = 0
  rotate_left
  · simp only [hd, decide_false, Bool.false_and, Bool.and_false, Bool.not_false, reduceIte]
    rfl
  by_cases hg : 1 < a.g ∧ a.g < a.p
  rotate_left
  · simp only [hg, decide_false, Bool.false_and, Bool.and_false, Bool.not_false, reduceIte]
    rfl
  by_cases hx : 0 < n ∧ n < a.q
  rotate_left
  · simp only [hs, hgq, hd, hg, hx, and_self, decide_true, decide_false, Bool.true_and, Bool.and_false,
      Bool.not_true, Bool.false_eq_true, reduceIte, ite_self]
  have hyq := powMod_order_of_generator (x := n) (supported_bounds hs.1).1 hgq
  have hkv : Spec.Dsa.keyValid ⟨a, Spec.Dsa.powMod a.g n a.p, some n⟩ =
      decide (1 < Spec.Dsa.powMod a.g n a.p ∧ Spec.Dsa.powMod a.g n a.p < a.p) := by
    simp only [Spec.Dsa.keyValid, hyq, hx.1, hx.2, decide_true, beq_self_eq_true, Bool.and_true,
      Bool.decide_and]
  simp only [hs, hgq, hd, hg, hx, and_self, decide_true, Bool.true_and, Bool.and_true, Bool.not_true,
    Bool.false_eq_true, reduceIte, hkv, henc]

/-- Key derivation's checks as the implementations make them: the
domain's shape, then the signer's checks of the key (with y = g^x), after
x's range. The key is the domain as given, then y and x. -/
theorem deriveKeyBytes_eq {pLen qLen : Nat} {params x : List Byte}
    (hl : Spec.Dsa.lengthsValid pLen qLen) (hpl : params.length = 2 * pLen + qLen)
    (hxl : x.length = qLen) :
    let a := Spec.Dsa.paramsBytes pLen qLen params
    let y := Spec.Dsa.powMod a.g (Spec.Dsa.decodeBE x) a.p
    Spec.Dsa.deriveKeyBytes pLen qLen params x =
      if decide (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength a.p) (Spec.Dsa.bitLength a.q) ∧
          a.p % 2 = 1 ∧ a.q % 2 = 1) &&
        (decide (Spec.Dsa.powMod a.g a.q a.p = 1) && (decide ((a.p - 1) % a.q = 0) &&
          (decide (1 < y ∧ y < a.p) && (decide (1 < a.g ∧ a.g < a.p) &&
            (decide (0 < Spec.Dsa.decodeBE x ∧ Spec.Dsa.decodeBE x < a.q) && true)))))
      then some (params ++ Spec.Dsa.encodeBE pLen y ++ x) else none := by
  intro a y
  have henc : Spec.Dsa.encodePrivateKey pLen qLen ⟨a, y, some (Spec.Dsa.decodeBE x)⟩ =
      params ++ Spec.Dsa.encodeBE pLen y ++ x := by
    unfold Spec.Dsa.encodePrivateKey
    simp only [Option.getD_some]
    rw [encodeParams_paramsBytes hpl, ← hxl, encodeBE_decodeBE]
  unfold Spec.Dsa.deriveKeyBytes
  rw [checkParametersBytes_eq hl hpl]
  simp only [hxl, bne_self_eq_false, Bool.or_false, Bool.and_true, Bool.and_self]
  exact derive_checks pLen qLen a _ _ henc

/-- Key generation as the wrapper computes it: the domain check, sampling,
and derivation from the accepted draw. -/
theorem generateKeyBytes_eq {pLen qLen : Nat} {params rand : List Byte}
    (hl : Spec.Dsa.lengthsValid pLen qLen) (hpl : params.length = 2 * pLen + qLen) :
    Spec.Dsa.generateKeyBytes pLen qLen params rand =
      if Spec.Dsa.checkParametersBytes pLen qLen params then
        match (Spec.Dsa.Random.sample (Spec.Dsa.paramsBytes pLen qLen params).q 128 rand).scalar with
        | none => ⟨none,
            if (Spec.Dsa.Random.sample (Spec.Dsa.paramsBytes pLen qLen params).q 128 rand).trace.getLast?
              == some 2 then 2 else 0,
            (Spec.Dsa.Random.sample (Spec.Dsa.paramsBytes pLen qLen params).q 128 rand).used,
            (Spec.Dsa.Random.sample (Spec.Dsa.paramsBytes pLen qLen params).q 128 rand).trace⟩
        | some x =>
          let res := Spec.Dsa.deriveKeyBytes pLen qLen params (Spec.Dsa.encodeBE qLen x)
          ⟨res, Spec.Dsa.signStatus res,
            (Spec.Dsa.Random.sample (Spec.Dsa.paramsBytes pLen qLen params).q 128 rand).used,
            (Spec.Dsa.Random.sample (Spec.Dsa.paramsBytes pLen qLen params).q 128 rand).trace ++
              [if res.isSome then 5 else 6]⟩
      else ⟨none, 0, 0, [4]⟩ := by
  unfold Spec.Dsa.generateKeyBytes Spec.Dsa.checkParametersBytes
  simp only [hl, hpl, decide_true, Bool.not_true, bne_self_eq_false, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte, beq_self_eq_true, Bool.true_and]
  by_cases hv : Spec.Dsa.parametersValid (Spec.Dsa.paramsBytes pLen qLen params)
  rotate_left
  · simp only [hv, decide_false, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
  simp only [hv, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  generalize hd : Spec.Dsa.Random.sample (Spec.Dsa.paramsBytes pLen qLen params).q 128 rand = draw
  cases hx : draw.scalar with
  | none => rfl
  | some x =>
    have hr := VG.Proof.Dsa.Random.sample_range _ _ _ _ (hd ▸ hx)
    have hq : (Spec.Dsa.paramsBytes pLen qLen params).q < 256 ^ qLen := by
      have := decodeBE_lt ((params.drop pLen).take qLen)
      rwa [show ((params.drop pLen).take qLen).length = qLen by
        simp only [List.length_take, List.length_drop]; omega] at this
    have hdec : Spec.Dsa.decodeBE (Spec.Dsa.encodeBE qLen x) = x := decodeBE_encodeBE (by omega)
    unfold Spec.Dsa.deriveKeyBytes Spec.Dsa.checkParametersBytes
    simp only [hl, hpl, hv, decide_true, beq_self_eq_true, Bool.and_self, Bool.not_true,
      encodeBE_length, bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hdec]
    cases Spec.Dsa.generate (Spec.Dsa.paramsBytes pLen qLen params) [x] with
    | none => rfl
    | some key => cases hk : Spec.Dsa.keyValid key <;> simp [hk, Spec.Dsa.signStatus]

end VG.Proof.Dsa
