module

public import VerifiedGarbage.Spec.Gcm.Bitsliced
public import VerifiedGarbage.Spec.Gcm.Powers8

/-!
# AES-GCM seal from contiguous plaintext

**Trusted.** Both pointers span the same number of bytes. The paired parameter
admits one writable region when they are identical and otherwise requires two
disjoint regions. The plaintext in the encryption equation is always the
source in the entry memory, including when the call overwrites that memory.
-/

@[expose] public section
namespace VG.Spec.Gcm

/-- The prepared form extends the key context from 32 to 129 words. -/
def sealContiguousSig (ctxWords : Nat := 32) : Sig where
  params := [("ctx", .array false .u64 ctxWords), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .inOutSlice .u8 "dst" "len"), ("tag", .array true .u8 16)]

/-- GCM-AE (NIST SP 800-38D §7.1), reading the source before encryption and
returning the ciphertext and full tag in the exit memory. -/
def sealContiguousPost (pb : Nat) : (sealContiguousSig 32).Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src dst len tag m m' _ =>
    ∀ key, KeyRounds m ctx rounds.toNat key →
      aesGcmEncrypt key 16 (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m src len.toNat)
          (Aes.bytesAt m aad aadLen.toNat) =
        (Aes.bytesAt m' dst len.toNat, Aes.bytesAt m' tag 16)

def sealContiguousContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (sealContiguousSig 32).contract A
    (pre := fun ctx rounds nonce nl aad al _src dst len tag =>
      sealPre A.ptrBits ctx rounds nonce nl aad al dst len tag)
    (post := sealContiguousPost A.ptrBits) (writeArgs := true) (stack := stack)

def sealContiguousApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_contiguous"
  sig := sealContiguousSig 32
  writeArgs := true
  contracts := some fun A stack => sealContiguousContract A stack
  summary := "AES-GCM authenticated encryption (NIST SP 800-38D §7.1), with the key context, \
    public rounds, IV and additional data of `vg_aes_gcm_seal`. Encrypts the initial `len` bytes \
    at `src` into `dst` and writes the 16-byte tag to `tag`. As for `vg_aes_gcm_seal`, callers \
    must use a fresh nonce for each encryption under a key and enforce the GCM input length \
    limits (§5.2.1.1). Only pointers, lengths and the \
    round count may affect timing. Contract: `VG.Spec.Gcm.sealContiguousContract`."
  safety := sealApi.safety

def sealContiguousPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (sealContiguousSig 129).contract A
    (pre := fun ctx rounds nonce nl aad al _src dst len tag =>
      sealPreparedPre A.ptrBits ctx rounds nonce nl aad al dst len tag)
    (post := sealContiguousPost A.ptrBits) (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds nonce nl aad al _src dst len tag =>
      sealPreparedLeak A.ptrBits ctx rounds nonce nl aad al dst len tag)

def sealContiguousPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_contiguous_prepared"
  sig := sealContiguousSig 129
  writeArgs := true
  contracts := some fun A stack => sealContiguousPreparedContract A stack
  summary := preparedSummary sealContiguousApi.name "sealContiguousPreparedContract"
  safety := sealContiguousApi.safety ++ [preparedSafety]

/-- The separate key-dependent buffers use the existing powers or bitsliced layout. -/
def sealContiguousAuxSig (param : String × Param) : Sig where
  params := (sealContiguousSig 32).params ++ [param]

def sealContiguousWithPowersContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (sealContiguousAuxSig withPowersParam).contract A
    (pre := fun ctx rounds nonce nl aad al _src dst len tag =>
      sealWithPowersPre A.ptrBits ctx rounds nonce nl aad al dst len tag)
    (post := fun ctx rounds nonce nl aad al src dst len tag _pw =>
      sealContiguousPost A.ptrBits ctx rounds nonce nl aad al src dst len tag)
    (writeArgs := true) (stack := stack)

def sealContiguousWithPowersApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_contiguous_with_powers"
  sig := sealContiguousAuxSig withPowersParam
  writeArgs := true
  contracts := some fun A stack => sealContiguousWithPowersContract A stack
  summary := withPowersSummary sealContiguousApi.name "sealContiguousWithPowersContract"
  safety := sealContiguousApi.safety ++ [withPowersSafety]

def sealContiguousBitslicedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (sealContiguousAuxSig bitslicedParam).contract A
    (pre := fun ctx rounds nonce nl aad al _src dst len tag =>
      sealBitslicedPre A.ptrBits ctx rounds nonce nl aad al dst len tag)
    (post := fun ctx rounds nonce nl aad al src dst len tag _bk =>
      sealContiguousPost A.ptrBits ctx rounds nonce nl aad al src dst len tag)
    (writeArgs := true) (stack := stack)

def sealContiguousBitslicedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_contiguous_bitsliced"
  sig := sealContiguousAuxSig bitslicedParam
  writeArgs := true
  contracts := some fun A stack => sealContiguousBitslicedContract A stack
  summary := bitslicedSummary sealContiguousApi.name "sealContiguousBitslicedContract"
  safety := sealContiguousApi.safety ++ [bitslicedSafety]

end VG.Spec.Gcm
