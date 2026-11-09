module

public import VerifiedGarbage.Spec.Dsa.Derive

/-!
# DSA operations on previously checked, immutable domain parameters (trusted)

An owner may check p||q||g once (`checkParametersBytes`), then reuse
that result across keys and operations while the exact parameter bytes
remain immutable. These contracts bind that assumption to the actual input
bytes, rather than to a boolean, pointer identity, or previous scratch contents.

Results, output zeroing, bounded sampling, consumption and timing guarantees
are exactly those of the fully checked APIs. Public-key membership, private-key
consistency, scalar ranges and signature checks remain the operation's job.
Domain primality and fresh independent randomness remain caller obligations.
No memory layout for cached Montgomery arithmetic is introduced here.

Review this specification separately from implementations that depend on it.
-/

@[expose] public section
namespace VG.Spec.Dsa
open VG.Spec.Rsa (bytesAt wordsAt)

/-- The fully checked result and leakage, with validity of the exact domain bytes as a precondition. -/
def signDomainCheckedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signSig.contract A
    (pre := fun _out outLen key keyLen pLen _nonce qLen _digest _digestLen _scratch scratchLen m =>
      lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 2 * qLen.toNat ∧
        keyLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat ∧
        checkParametersBytes pLen.toNat qLen.toNat (bytesAt m key (2 * pLen.toNat + qLen.toNat)) = true)
    (post := fun out outLen key keyLen pLen nonce qLen digest digestLen _scratch _scratchLen m m' r =>
      let res := signBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m nonce qLen.toNat) (bytesAt m digest digestLen.toNat)
      r.toNat = signStatus res ∧
        bytesAt m' out outLen.toNat = res.getD (List.replicate outLen.toNat 0))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen key keyLen pLen nonce qLen digest digestLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      publicBytesLeak pLen.toNat qLen.toNat kb ++
        [signStatus (signBytes pLen.toNat qLen.toNat kb
          (bytesAt m nonce qLen.toNat) (bytesAt m digest digestLen.toNat))])

/-- The fully checked result and leakage, with validity of the exact domain bytes as a precondition. -/
def verifyDomainCheckedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifySig.contract A
    (pre := fun key keyLen pLen qLen _signature signatureLen _digest _digestLen _scratch scratchLen m =>
      lengthsValid pLen.toNat qLen.toNat ∧ keyLen.toNat = 3 * pLen.toNat + qLen.toNat ∧
        signatureLen.toNat = 2 * qLen.toNat ∧ scratchWords pLen.toNat ≤ scratchLen.toNat ∧
        checkParametersBytes pLen.toNat qLen.toNat (bytesAt m key (2 * pLen.toNat + qLen.toNat)) = true)
    (post := fun key keyLen pLen qLen signature signatureLen digest digestLen _scratch _scratchLen m _m' r =>
      r.toNat = if verifyBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m signature signatureLen.toNat) (bytesAt m digest digestLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun key keyLen pLen qLen signature signatureLen digest digestLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      publicBytesLeak pLen.toNat qLen.toNat kb ++
        [if verifyBytes pLen.toNat qLen.toNat kb (bytesAt m signature signatureLen.toNat)
          (bytesAt m digest digestLen.toNat) then 1 else 0])

/-- The fully checked result and leakage, with validity of the exact domain bytes as a precondition. -/
def generateKeyDomainCheckedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  generateKeySig.contract A
    (pre := fun _out outLen _used params paramsLen pLen qLen _rand _randLen _scratch scratchLen m =>
      lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        paramsLen.toNat = 2 * pLen.toNat + qLen.toNat ∧
        generationScratchWords pLen.toNat ≤ scratchLen.toNat ∧
        checkParametersBytes pLen.toNat qLen.toNat (bytesAt m params paramsLen.toNat) = true)
    (post := fun out outLen used params paramsLen pLen qLen rand randLen _scratch _scratchLen m m' r =>
      let res := generateKeyBytes pLen.toNat qLen.toNat (bytesAt m params paramsLen.toNat)
        (bytesAt m rand randLen.toNat)
      r.toNat = res.status ∧
        bytesAt m' out outLen.toNat = res.key.getD (List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 = [BitVec.ofNat 64 res.used])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used params paramsLen pLen qLen rand randLen _scratch _scratchLen m =>
      let pb := bytesAt m params paramsLen.toNat
      let res := generateKeyBytes pLen.toNat qLen.toNat pb (bytesAt m rand randLen.toNat)
      pb.map (·.toNat) ++ [res.status, res.used] ++ res.trace)

/-- The fully checked result and leakage, with validity of the exact domain bytes as a precondition. -/
def deriveKeyDomainCheckedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  deriveKeySig.contract A
    (pre := fun _out outLen params paramsLen pLen _x qLen _scratch scratchLen m =>
      lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        paramsLen.toNat = 2 * pLen.toNat + qLen.toNat ∧ scratchWords pLen.toNat ≤ scratchLen.toNat ∧
        checkParametersBytes pLen.toNat qLen.toNat (bytesAt m params paramsLen.toNat) = true)
    (post := fun out outLen params paramsLen pLen x qLen _scratch _scratchLen m m' r =>
      let res := deriveKeyBytes pLen.toNat qLen.toNat (bytesAt m params paramsLen.toNat)
        (bytesAt m x qLen.toNat)
      r.toNat = signStatus res ∧
        bytesAt m' out outLen.toNat = res.getD (List.replicate outLen.toNat 0))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen params paramsLen pLen x qLen _scratch _scratchLen m =>
      let pb := bytesAt m params paramsLen.toNat
      pb.map (·.toNat) ++
        [signStatus (deriveKeyBytes pLen.toNat qLen.toNat pb (bytesAt m x qLen.toNat))])

end VG.Spec.Dsa
