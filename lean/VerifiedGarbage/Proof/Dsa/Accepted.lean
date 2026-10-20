module

import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.SignVerify
public import VerifiedGarbage.Spec.Dsa.SignVerify

/-! # DSA acceptance, on any target

The shapes of supported domains (`shapeValid`: supported bit lengths of `p`
and `q`, both odd) and the algebraic checks of public keys (`publicChecks`),
which the implementations evaluate as masks, agree with the specification's
predicates (`publicChecks_spec`, `privateChecks_spec`); a rejected shape
fails both packed-byte specifications, and the packed-byte signing and
verification results are the formulas the implementations compute
(`signBytes_compute`, `verifyBytes_compute`).
-/

@[expose] public section
namespace VG.Proof.Dsa
open VG

def shapeValid (p q : Nat) : Prop :=
  Spec.Dsa.supportedSizes (Spec.Dsa.bitLength p) (Spec.Dsa.bitLength q) ∧ (q % 2 = 1 ∧ p % 2 = 1)

instance (p q : Nat) : Decidable (shapeValid p q) := inferInstanceAs (Decidable (_ ∧ _))

def publicChecks (p q g y : Nat) : Prop :=
  ((1 < g ∧ g < p) ∧ (1 < y ∧ y < p)) ∧ (p - 1) % q = 0 ∧ g ^ q % p = 1 ∧ y ^ q % p = 1

instance (p q g y : Nat) : Decidable (publicChecks p q g y) := by
  unfold publicChecks
  infer_instance

theorem publicChecks_spec {p q g y : Nat} (H : shapeValid p q) :
    publicChecks p q g y ↔
      Spec.Dsa.parametersValid ⟨p, q, g⟩ ∧ Spec.Dsa.keyValid ⟨⟨p, q, g⟩, y, none⟩ = true := by
  have B := supported_bounds H.1
  simp only [publicChecks, Spec.Dsa.parametersValid, Spec.Dsa.keyValid, VG.Proof.Dsa.powMod_eq,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_true]
  constructor
  · rintro ⟨⟨G, Y⟩, D, GP, YP⟩
    exact ⟨⟨H.1, H.2.2, H.2.1, B.2.2, D, G.1, G.2, GP⟩, ⟨Y.1, Y.2⟩, YP⟩
  · rintro ⟨P, ⟨Ylo, Yhi⟩, YP⟩
    exact ⟨⟨⟨P.2.2.2.2.2.1, P.2.2.2.2.2.2.1⟩, Ylo, Yhi⟩, P.2.2.2.2.1, P.2.2.2.2.2.2.2, YP⟩

theorem privateChecks_spec {p q g y x : Nat} (H : shapeValid p q) :
    (publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ g ^ x % p = y) ↔
      Spec.Dsa.parametersValid ⟨p, q, g⟩ ∧ Spec.Dsa.keyValid ⟨⟨p, q, g⟩, y, some x⟩ = true := by
  rw [publicChecks_spec H]
  simp only [Spec.Dsa.keyValid, VG.Proof.Dsa.powMod_eq, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, and_true]
  simp only [and_assoc]

theorem parametersValid_shape {p q g : Nat} (H : Spec.Dsa.parametersValid ⟨p, q, g⟩) : shapeValid p q :=
  ⟨H.1, H.2.2.1, H.2.1⟩

theorem signBytes_invalid_shape {pLen qLen : Nat} {key nonce digest : List Byte}
    (H : ¬ shapeValid (Spec.Dsa.privateKeyBytes pLen qLen key).params.p
      (Spec.Dsa.privateKeyBytes pLen qLen key).params.q) :
    Spec.Dsa.signBytes pLen qLen key nonce digest = none := by
  have invalid : ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes pLen qLen key).params :=
    fun P => H (parametersValid_shape P)
  unfold Spec.Dsa.signBytes
  split
  · rfl
  · simp only [invalid, decide_false, Bool.not_false, ↓reduceIte]

theorem verifyBytes_invalid_shape {pLen qLen : Nat} {key signature digest : List Byte}
    (H : ¬ shapeValid (Spec.Dsa.publicKeyBytes pLen qLen key).params.p
      (Spec.Dsa.publicKeyBytes pLen qLen key).params.q) :
    Spec.Dsa.verifyBytes pLen qLen key signature digest = false := by
  have invalid : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes pLen qLen key).params :=
    fun P => H (parametersValid_shape P)
  unfold Spec.Dsa.verifyBytes
  split
  · rfl
  · simp only [invalid, decide_false, Bool.false_and]

theorem signBytes_compute {pLen qLen p q g y x k n : Nat} {key nonce digest : List Byte}
    (widths : Spec.Dsa.lengthsValid pLen qLen) (shape : shapeValid p q)
    (keyLen : key.length = 3 * pLen + 2 * qLen) (nonceLen : nonce.length = qLen)
    (keyValue : Spec.Dsa.privateKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, some x⟩)
    (nonceValue : Spec.Dsa.decodeBE nonce = k) (qBits : Spec.Dsa.bitLength q = 8 * n) :
    let rv := g ^ k % p % q
    let sv := k ^ (q - 2) % q * ((Spec.Dsa.decodeBE (digest.take n) % q + x * rv % q) % q) % q
    Spec.Dsa.signBytes pLen qLen key nonce digest =
      if publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧
          g ^ x % p = y ∧ rv ≠ 0 ∧ sv ≠ 0
      then some (Spec.Dsa.encodeBE qLen rv ++ Spec.Dsa.encodeBE qLen sv) else none := by
  dsimp only
  let K : Spec.Dsa.Key := ⟨⟨p, q, g⟩, y, some x⟩
  let rv := g ^ k % p % q
  let sv := k ^ (q - 2) % q * ((Spec.Dsa.decodeBE (digest.take n) % q + x * rv % q) % q) % q
  have reduced := VG.Proof.Dsa.signWithNonce_reduced K digest k x n rfl qBits
  simp only [K, ← VG.Proof.Dsa.powMod_rsa, VG.Proof.Dsa.powMod_eq] at reduced
  have accepted :
      (publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧ g ^ x % p = y ∧ rv ≠ 0 ∧ sv ≠ 0) ↔
      (Spec.Dsa.parametersValid K.params ∧ Spec.Dsa.keyValid K = true ∧ (0 < k ∧ k < q) ∧ rv ≠ 0 ∧ sv ≠ 0) := by
    have H := privateChecks_spec (g := g) (y := y) (x := x) shape
    change (publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ g ^ x % p = y) ↔
      (Spec.Dsa.parametersValid K.params ∧ Spec.Dsa.keyValid K = true) at H
    constructor
    · rintro ⟨A, X, N, P, R, S⟩
      have T := H.mp ⟨A, X, P⟩
      exact ⟨T.1, T.2, N, R, S⟩
    · rintro ⟨A, X, N, R, S⟩
      have T := H.mpr ⟨A, X⟩
      exact ⟨T.1, T.2.1, N, T.2.2, R, S⟩
  change Spec.Dsa.signBytes pLen qLen key nonce digest =
    if publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧ g ^ x % p = y ∧ rv ≠ 0 ∧ sv ≠ 0
      then some (Spec.Dsa.encodeBE qLen rv ++ Spec.Dsa.encodeBE qLen sv) else none
  simp only [accepted]
  unfold Spec.Dsa.signBytes
  simp only [widths, decide_true, Bool.not_true, keyLen, nonceLen, bne_self_eq_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, keyValue, nonceValue]
  rw [reduced]
  change (if !decide (Spec.Dsa.parametersValid K.params) then none else
    (if !Spec.Dsa.keyValid K || !(0 < k && k < q) then none else
      if rv == 0 || sv == 0 then none else some (⟨rv, sv⟩ : Spec.Dsa.Signature)) >>= fun sig =>
        some (Spec.Dsa.encodeBE qLen sig.r ++ Spec.Dsa.encodeBE qLen sig.s)) = _
  by_cases P : Spec.Dsa.parametersValid K.params <;>
    cases V : Spec.Dsa.keyValid K <;>
    by_cases N : 0 < k ∧ k < q <;> by_cases R : rv = 0 <;> by_cases S : sv = 0 <;>
    simp_all [← Bool.decide_and]

theorem verifyBytes_compute {pLen qLen p q g y rv sv n : Nat} {key signature digest : List Byte}
    (widths : Spec.Dsa.lengthsValid pLen qLen) (shape : shapeValid p q)
    (keyLen : key.length = 3 * pLen + qLen) (sigLen : signature.length = 2 * qLen)
    (keyValue : Spec.Dsa.publicKeyBytes pLen qLen key = ⟨⟨p, q, g⟩, y, none⟩)
    (rValue : Spec.Dsa.decodeBE (signature.take qLen) = rv)
    (sValue : Spec.Dsa.decodeBE (signature.drop qLen) = sv)
    (qBits : Spec.Dsa.bitLength q = 8 * n) :
    let computed := (g ^ (Spec.Dsa.decodeBE (digest.take n) % q * (sv ^ (q - 2) % q) % q) % p *
      (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q
    Spec.Dsa.verifyBytes pLen qLen key signature digest =
      decide (publicChecks p q g y ∧ (0 < rv ∧ rv < q) ∧ (0 < sv ∧ sv < q) ∧ computed = rv) := by
  dsimp only
  let K : Spec.Dsa.Key := ⟨⟨p, q, g⟩, y, none⟩
  let computed := (g ^ (Spec.Dsa.decodeBE (digest.take n) % q * (sv ^ (q - 2) % q) % q) % p *
      (y ^ (rv * (sv ^ (q - 2) % q) % q) % p) % p) % q
  have reduced := VG.Proof.Dsa.verify_reduced K ⟨rv, sv⟩ digest n qBits
  simp only [K, ← VG.Proof.Dsa.powMod_rsa, VG.Proof.Dsa.powMod_eq] at reduced
  simp only [publicChecks_spec shape]
  unfold Spec.Dsa.verifyBytes
  simp only [widths, decide_true, Bool.not_true, keyLen, sigLen, bne_self_eq_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, keyValue, rValue, sValue]
  rw [reduced]
  change (decide (Spec.Dsa.parametersValid K.params) &&
    (if !Spec.Dsa.keyValid K || !(0 < rv && rv < q && 0 < sv && sv < q) then false else computed == rv)) =
      decide ((Spec.Dsa.parametersValid K.params ∧ Spec.Dsa.keyValid K = true) ∧
        (0 < rv ∧ rv < q) ∧ (0 < sv ∧ sv < q) ∧ computed = rv)
  by_cases P : Spec.Dsa.parametersValid K.params <;> cases V : Spec.Dsa.keyValid K <;>
    by_cases R : 0 < rv ∧ rv < q <;> by_cases S : 0 < sv ∧ sv < q <;> by_cases E : computed = rv <;>
    simp_all [← Bool.decide_and, and_assoc]

end VG.Proof.Dsa
