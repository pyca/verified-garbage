module

public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.RandomSign

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
def randomSignDomainCheckedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  randomSignSig.contract A
    (pre := fun _out outLen _used key keyLen pLen qLen _digest _digestLen
        _rand _randLen _scratch scratchLen m =>
      lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 2 * qLen.toNat ∧
        keyLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        randomSignScratchWords pLen.toNat ≤ scratchLen.toNat ∧
        checkParametersBytes pLen.toNat qLen.toNat (bytesAt m key (2 * pLen.toNat + qLen.toNat)) = true)
    (post := fun out outLen used key keyLen pLen qLen digest digestLen
        rand randLen _scratch _scratchLen m m' r =>
      let res := randomSignBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m digest digestLen.toNat) (bytesAt m rand randLen.toNat)
      r.toNat = res.status ∧
        bytesAt m' out outLen.toNat = res.signature.getD (List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 = [BitVec.ofNat 64 res.used])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used key keyLen pLen qLen digest digestLen
        rand randLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      let res := randomSignBytes pLen.toNat qLen.toNat kb
        (bytesAt m digest digestLen.toNat) (bytesAt m rand randLen.toNat)
      publicBytesLeak pLen.toNat qLen.toNat kb ++ [res.status, res.used] ++ res.trace)

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

def signDomainCheckedApi : Api where
  module := "dsa"
  name := "vg_dsa_sign_domain_checked"
  sig := signSig
  writeArgs := true
  contracts := some fun A stack => signDomainCheckedContract A stack
  summary := "One DSA signing attempt on a prehashed digest, with a previously checked domain. \
    Returns exactly the fully checked API's result, with the same failure zeroing, \
    sampling and timing guarantees. Contract: `VG.Spec.Dsa.signDomainCheckedContract`."
  safety := ["(p_len, q_len) must be (128,20), (256,20), (256,28), (256,32), or (384,32).",
    "key_len must be 3*p_len + 2*q_len; out_len must be 2*q_len.",
    "scratch_len must be at least 16*p_len words. Scratch may contain secrets on return.",
    "The exact p||q||g bytes supplied to this operation must satisfy \
    checkParametersBytes p_len q_len params = true. For a packed key these are its first \
    2*p_len+q_len bytes. A successful check of those bytes establishes this only \
    while they remain unchanged. A cached flag or old scratch contents alone do \
    not establish the precondition. Primality remains the caller's responsibility."]

def verifyDomainCheckedApi : Api := { verifyApi with
  name := "vg_dsa_verify_domain_checked"
  contracts := some fun A stack => verifyDomainCheckedContract A stack
  summary := "DSA verification with a previously checked domain; the public value and signature are still checked. \
    Returns exactly the fully checked API's result, with the same failure zeroing, \
    sampling and timing guarantees. Contract: `VG.Spec.Dsa.verifyDomainCheckedContract`."
  safety := verifyApi.safety ++ ["The exact p||q||g bytes supplied to this operation must satisfy \
    checkParametersBytes p_len q_len params = true. For a packed key these are its first \
    2*p_len+q_len bytes. A successful check of those bytes establishes this only \
    while they remain unchanged. A cached flag or old scratch contents alone do \
    not establish the precondition. Primality remains the caller's responsibility."] }

def randomSignDomainCheckedApi : Api := { randomSignApi with
  name := "vg_dsa_sign_random_domain_checked"
  contracts := some fun A stack => randomSignDomainCheckedContract A stack
  summary := "Bounded randomized DSA signing with a previously checked domain. \
    Returns exactly the fully checked API's result, with the same failure zeroing, \
    sampling and timing guarantees. Contract: `VG.Spec.Dsa.randomSignDomainCheckedContract`."
  safety := randomSignApi.safety ++ ["The exact p||q||g bytes supplied to this operation must satisfy \
    checkParametersBytes p_len q_len params = true. For a packed key these are its first \
    2*p_len+q_len bytes. A successful check of those bytes establishes this only \
    while they remain unchanged. A cached flag or old scratch contents alone do \
    not establish the precondition. Primality remains the caller's responsibility."] }

def generateKeyDomainCheckedApi : Api := { generateKeyApi with
  name := "vg_dsa_generate_key_domain_checked"
  contracts := some fun A stack => generateKeyDomainCheckedContract A stack
  summary := "Bounded DSA key generation with a previously checked domain. \
    Returns exactly the fully checked API's result, with the same failure zeroing, \
    sampling and timing guarantees. Contract: `VG.Spec.Dsa.generateKeyDomainCheckedContract`."
  safety := generateKeyApi.safety ++ ["The exact p||q||g bytes supplied to this operation must satisfy \
    checkParametersBytes p_len q_len params = true. For a packed key these are its first \
    2*p_len+q_len bytes. A successful check of those bytes establishes this only \
    while they remain unchanged. A cached flag or old scratch contents alone do \
    not establish the precondition. Primality remains the caller's responsibility."] }

def deriveKeyDomainCheckedApi : Api := { deriveKeyApi with
  name := "vg_dsa_derive_key_domain_checked"
  contracts := some fun A stack => deriveKeyDomainCheckedContract A stack
  summary := "DSA key derivation from a supplied scalar with a previously checked domain. \
    Returns exactly the fully checked API's result, with the same failure zeroing, \
    sampling and timing guarantees. Contract: `VG.Spec.Dsa.deriveKeyDomainCheckedContract`."
  safety := deriveKeyApi.safety ++ ["The exact p||q||g bytes supplied to this operation must satisfy \
    checkParametersBytes p_len q_len params = true. For a packed key these are its first \
    2*p_len+q_len bytes. A successful check of those bytes establishes this only \
    while they remain unchanged. A cached flag or old scratch contents alone do \
    not establish the precondition. Primality remains the caller's responsibility."] }

end VG.Spec.Dsa
