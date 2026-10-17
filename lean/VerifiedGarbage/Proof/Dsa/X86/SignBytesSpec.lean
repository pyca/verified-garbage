module

public import VerifiedGarbage.Proof.Dsa.X86.AcceptedSpec
public import VerifiedGarbage.Proof.Dsa.SignVerify

/-! # Connecting the x86 signing formulas to the packed-byte contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG

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

end VG.Proof.Dsa.X86
