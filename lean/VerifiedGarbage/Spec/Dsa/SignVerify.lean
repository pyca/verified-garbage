module

public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# DSA signing and verification contracts (trusted)

The key is a packed big-endian buffer: p (p_len bytes), q (q_len),
g (p_len), y (p_len), and, for signing only, x (q_len). The nonce is
q_len bytes; a signature is r followed by s, q_len bytes each. There is no
DER encoding. The Rust wrapper owns buffers, supplies independent random
nonces, and retries a failed signing attempt with fresh randomness.

Only supported byte lengths and scratch capacity are preconditions. Values
are checked by the operations, including the domain's algebraic consistency;
no contract assumes or asserts exact primality. Imported parameters require
caller assurance of domain validity, as in Spec/Dsa.lean.

`signContract` is one signing attempt with a supplied nonce. The Rust API
does not offer it: `vg_dsa_sign_random` (`RandomSign.lean`) runs it with
nonces drawn from its tape, and the domain-checked contracts
(`DomainChecked.lean`) are stated as it.

The domain and public key may affect timing. The digest, private scalar and
nonce may not, except for the success/failure result of a signing attempt.
Verification may reveal its Boolean result, but not otherwise its digest or
signature. These contracts describe individual bounded attempts, not the
randomness/retry loop. Scratch may contain secrets and must be destroyed by
the wrapper. Stack-argument writes follow the existing RSA contracts.
-/

@[expose] public section

namespace VG.Spec.Dsa

open VG.Spec.Rsa (bytesAt)

/-- The least working space, in `u64`s, for a `p` of `pLen` octets. -/
def scratchWords (pLen : Nat) : Nat := 16 * pLen

/-- Supported external widths, in bytes. (2048,160) and (2048,224) are import-only. -/
def lengthsValid (pLen qLen : Nat) : Prop :=
  (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ (qLen = 20 ∨ qLen = 28 ∨ qLen = 32)) ∨
    (pLen = 384 ∧ qLen = 32)

instance (pLen qLen : Nat) : Decidable (lengthsValid pLen qLen) := by
  unfold lengthsValid
  infer_instance

/-- Decode a packed public key; trailing private bytes are not consulted. -/
def publicKeyBytes (pLen qLen : Nat) (key : List Byte) : Key :=
  ⟨⟨decodeBE (key.take pLen), decodeBE ((key.drop pLen).take qLen),
    decodeBE ((key.drop (pLen + qLen)).take pLen)⟩,
    decodeBE ((key.drop (2 * pLen + qLen)).take pLen), none⟩

/-- Decode the private scalar after the public components. -/
def privateKeyBytes (pLen qLen : Nat) (key : List Byte) : Key :=
  { publicKeyBytes pLen qLen key with
    x := some (decodeBE ((key.drop (3 * pLen + qLen)).take qLen)) }

/-- A signing attempt on packed bytes. Malformed lengths, inconsistent
parameters/keys and invalid nonces fail. Success returns fixed-width r||s. -/
def signBytes (pLen qLen : Nat) (key nonce digest : List Byte) : Option (List Byte) := do
  if !(lengthsValid pLen qLen) || key.length != 3 * pLen + 2 * qLen ||
      nonce.length != qLen then none else do
    let k := privateKeyBytes pLen qLen key
    if !parametersValid k.params then none else do
      let sig ← signWithNonce k digest (decodeBE nonce)
      return encodeBE qLen sig.r ++ encodeBE qLen sig.s

/-- Verification on packed bytes. Invalid lengths or domain consistency
fail; verify checks the public key and the signature scalar ranges. -/
def verifyBytes (pLen qLen : Nat) (key signature digest : List Byte) : Bool :=
  if !(lengthsValid pLen qLen) || key.length != 3 * pLen + qLen ||
      signature.length != 2 * qLen then false else
    let k := publicKeyBytes pLen qLen key
    decide (parametersValid k.params) &&
      verify k ⟨decodeBE (signature.take qLen), decodeBE (signature.drop qLen)⟩ digest

/-- Signing returns either a retry/failure (0) or a signature (1). -/
def signStatus (res : Option (List Byte)) : Nat := if res.isSome then 1 else 0

/-- The public portion of a packed key is the only key material declassified. -/
def publicBytesLeak (pLen qLen : Nat) (key : List Byte) : List Nat :=
  (key.take (3 * pLen + qLen)).map (·.toNat)

/-- One nonce attempt, with a packed private key and fixed-width r||s output. -/
def signSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("key", .slice false .u8 "key_len"),
    ("p_len", .int .usize true), ("nonce", .slice false .u8 "q_len"),
    ("digest", .slice false .u8 "digest_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

def signContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  signSig.contract A
    (pre := fun _out outLen _key keyLen pLen _nonce qLen _digest _digestLen _scratch scratchLen _ =>
      lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 2 * qLen.toNat ∧
        keyLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        scratchWords pLen.toNat ≤ scratchLen.toNat)
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

/-- Verify with a packed public key; the signature is fixed-width r||s. -/
def verifySig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("p_len", .int .usize true),
    ("q_len", .int .usize true), ("signature", .slice false .u8 "signature_len"),
    ("digest", .slice false .u8 "digest_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

def verifyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  verifySig.contract A
    (pre := fun _key keyLen pLen qLen _signature signatureLen _digest _digestLen _scratch scratchLen _ =>
      lengthsValid pLen.toNat qLen.toNat ∧ keyLen.toNat = 3 * pLen.toNat + qLen.toNat ∧
        signatureLen.toNat = 2 * qLen.toNat ∧ scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun key keyLen pLen qLen signature signatureLen digest digestLen _scratch _scratchLen m _m' r =>
      r.toNat = if verifyBytes pLen.toNat qLen.toNat (bytesAt m key keyLen.toNat)
        (bytesAt m signature signatureLen.toNat) (bytesAt m digest digestLen.toNat) then 1 else 0)
    (writeArgs := true) (stack := stack)
    (leak := some fun key keyLen pLen qLen signature signatureLen digest digestLen _scratch _scratchLen m =>
      let kb := bytesAt m key keyLen.toNat
      publicBytesLeak pLen.toNat qLen.toNat kb ++
        [if verifyBytes pLen.toNat qLen.toNat kb (bytesAt m signature signatureLen.toNat)
          (bytesAt m digest digestLen.toNat) then 1 else 0])

def verifyApi : Api where
  module := "dsa"
  name := "vg_dsa_verify"
  sig := verifySig
  writeArgs := true
  contracts := some fun A stack => verifyContract A stack
  summary := "DSA verification of a prehashed digest. The key is big-endian p||q||g||y \
    with widths p_len, q_len, p_len, p_len; signature is r||s with q_len bytes each. \
    Returns 1 if verification succeeds, otherwise 0. Checks algebraic consistency, \
    not primality; caller must assure domain validity. Timing may depend on \
    p,q,g,y and the result, not otherwise on signature or digest. \
    Contract: `VG.Spec.Dsa.verifyContract`."
  safety := ["(p_len, q_len) must be (128,20), (256,20), (256,28), (256,32), or (384,32).",
    "key_len must be 3*p_len + q_len; signature_len must be 2*q_len.",
    "scratch_len must be at least 16*p_len words. Scratch contents are unspecified on return."]

end VG.Spec.Dsa
