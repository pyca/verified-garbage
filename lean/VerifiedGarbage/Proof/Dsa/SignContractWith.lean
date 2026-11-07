module

public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Spec.Dsa.SignVerify

/-! # Signing contracts that only proofs use

Not trusted. `signContractWith` is the contract of an internal function,
supplied-nonce signing under a precondition on the packed key, which only
verified code (the randomized wrapper) calls. `randomSignCheckedContract`
is the contract the randomized wrappers' generic proofs are stated against:
randomized signing of any key, which checks the key itself. No function is
emitted with it; each target's `vg_dsa_sign_random_prevalidated` is proven
against `Spec.Dsa.randomSignPrevalidatedContract`, which is it under the
validated-key precondition. -/

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

open VG.Spec.Rsa (bytesAt wordsAt) in
/-- Randomized signing of any packed key with its full checks: the result
and leakage of `Spec.Dsa.randomSignPrevalidatedContract`, whose
precondition adds that the key validates. -/
def randomSignCheckedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.Dsa.randomSignSig.contract A
    (pre := fun _out outLen _used _key keyLen pLen qLen _digest _digestLen
        _rand _randLen _scratch scratchLen _ =>
      Spec.Dsa.lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 2 * qLen.toNat ∧
        keyLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        Spec.Dsa.randomSignScratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen used key keyLen pLen qLen digest digestLen
        rand randLen _scratch _scratchLen m m' r =>
      let res := Spec.Dsa.randomSignBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m digest digestLen.toNat) (bytesAt m rand randLen.toNat)
      r.toNat = res.status ∧
        bytesAt m' out outLen.toNat = res.signature.getD (List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 = [BitVec.ofNat 64 res.used])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used key keyLen pLen qLen digest digestLen
        rand randLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      let res := Spec.Dsa.randomSignBytes pLen.toNat qLen.toNat kb
        (bytesAt m digest digestLen.toNat) (bytesAt m rand randLen.toNat)
      Spec.Dsa.publicBytesLeak pLen.toNat qLen.toNat kb ++ [res.status, res.used] ++ res.trace)

end VG.Proof.Dsa
