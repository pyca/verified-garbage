module

public import VerifiedGarbage.Spec.Dsa.SignVerify

/-! # Supplied-nonce signing under a precondition on the packed key

Not trusted: the contract of an internal function, which only verified
code (the randomized wrapper) calls. -/

@[expose] public section

namespace VG.Proof.Dsa

open VG.Spec.Rsa (bytesAt) in
/-- `signContract` under an extra precondition `valid` on the exact packed
key bytes: with `fun _ _ _ => true` it is `signContract`, with
`validatePrivateKeyBytes` the contract of a signing attempt for a validated
private key. Its result and leakage are `signContract`'s. -/
def signContractWith (valid : Nat → Nat → List Byte → Bool) {M : ISA} (A : Abi M) (stack : Nat := 0) :
    Contract M :=
  Spec.Dsa.signSig.contract A
    (pre := fun _out outLen key keyLen pLen _nonce qLen _digest _digestLen _scratch scratchLen m =>
      Spec.Dsa.lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 2 * qLen.toNat ∧
        keyLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        Spec.Dsa.scratchWords pLen.toNat ≤ scratchLen.toNat ∧
        valid pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat) = true)
    (post := fun out outLen key keyLen pLen nonce qLen digest digestLen _scratch _scratchLen m m' r =>
      let res := Spec.Dsa.signBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m nonce qLen.toNat) (bytesAt m digest digestLen.toNat)
      r.toNat = Spec.Dsa.signStatus res ∧
        bytesAt m' out outLen.toNat = res.getD (List.replicate outLen.toNat 0))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen key keyLen pLen nonce qLen digest digestLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      Spec.Dsa.publicBytesLeak pLen.toNat qLen.toNat kb ++
        [Spec.Dsa.signStatus (Spec.Dsa.signBytes pLen.toNat qLen.toNat kb
          (bytesAt m nonce qLen.toNat) (bytesAt m digest digestLen.toNat))])

end VG.Proof.Dsa
