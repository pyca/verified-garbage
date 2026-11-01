module

public import VerifiedGarbage.Spec.Gcm.Prepared

/-!
# AES-GCM with sixteen prepared GHASH powers

**Trusted.** The 1024-byte prepared key context of `Spec/Gcm/Prepared.lean`,
for implementations that read only its first sixteen powers: the first 256
bytes are the existing key context (`KeyRepr`), and bytes 256 through 511
hold the first 8 pairs of `PreparedPowersRepr`, pair `k` being
`preparedPower(H^(2k+2))` then `preparedPower(H^(2k+1))`, each stored
little-endian. Bytes 512 through 1023 are not read, and
`vg_aes_gcm_prepare16` does not write them. This is a storage convention, not
a change to GCM's field arithmetic (NIST SP 800-38D §6.3).

A context `vg_aes_gcm_prepare` wrote (`PreparedPowersRepr`) satisfies
`PreparedPowers16Repr` too, so these APIs also take it; a context
`vg_aes_gcm_prepare16` wrote must never be passed to a `*_prepared` or
`*_precomputed` API, which may read all 48 powers. The signatures are those of
the `*_prepared` APIs (a 1024-byte context), and these APIs have the existing
GCM postconditions, memory bounds, disjointness and secrecy guarantees; only
the precondition on the powers is weaker, so they have distinct names. The
APIs that read only the first 256 bytes (stream initialization, AAD, finish
and verify) remain usable. Existing specifications and contracts are
unchanged.
-/

@[expose] public section

namespace VG.Spec.Gcm

/-- The first 8 pairs of `PreparedPowersRepr`: pair `k`, at byte `256 + 32 k`,
contains the encoded `H^(2k+2)` then `H^(2k+1)`, each as a little-endian
128-bit word. The 8 pairs occupy bytes 256 through 511. -/
def PreparedPowers16Repr (m : Mem) (p : Addr) : Prop :=
  ∀ k < 8,
    m.readW (p + BitVec.ofNat 64 (256 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 2)) ∧
    m.readW (p + BitVec.ofNat 64 (272 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 1))

/-! ## The key context -/

/-- Keeps the first 256 bytes, and writes the first 16 prepared powers of the
hash subkey in its bytes 240–255 (`ctxH`). With those bytes a key context
(`KeyRepr`, as `vg_aes_gcm_init` writes it), the result is a 16-power
prepared key context of the same key (`KeyRepr` and `PreparedPowers16Repr`). -/
def prepare16Post (pb : Nat) : prepareSig.Post pb := fun ctx m m' _ =>
  Aes.bytesAt m' ctx 256 = Aes.bytesAt m ctx 256 ∧ PreparedPowers16Repr m' ctx

/-- No precondition: the powers are those of whatever hash subkey the
context holds. -/
def prepare16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  prepareSig.contract A (post := prepare16Post A.ptrBits) (writeArgs := true) (stack := stack)

/-- Prepares the first 16 powers of a key context in place on any target,
without the key. -/
def prepare16Api : Api where
  module := "gcm"
  name := "vg_aes_gcm_prepare16"
  sig := prepareSig
  writeArgs := true
  contracts := some fun A stack => prepare16Contract A stack
  summary := "Makes the 1024-byte `*ctx`, whose first 256 bytes are a key context of \
    `vg_aes_gcm_init`, a 16-power prepared key context of the same key, in place: keeps its \
    first 256 bytes and, at byte `256 + 32*k`, for `k` from 0 to 7, stores \
    `preparedPower(H^(2*k+2))` and then `preparedPower(H^(2*k+1))`, as two little-endian \
    128-bit words, `H` being the hash subkey in its bytes 240–255. Use only the \
    `*_prepared16` APIs, or APIs that read the first 256 bytes, with this format. \
    Contract: `VG.Spec.Gcm.prepare16Contract`: the first 256 bytes are kept and the context \
    satisfies `PreparedPowers16Repr`. Constant time: only the pointer may affect timing, not \
    the hash subkey."
  safety := []

/-- Prepared-context validity, in addition to each API's existing safety requirements. -/
def prepared16Safety : String :=
  "`*ctx` must have the prepared format written by `vg_aes_gcm_prepare16` or \
  `vg_aes_gcm_prepare` (not the format of `vg_aes_gcm_init_precomputed`)."

/-- Common documentation for the 16-power prepared APIs. -/
def prepared16Summary (name contract : String) : String :=
  "`" ++ name ++ "` with a 1024-byte context from `vg_aes_gcm_prepare16` (or " ++
  "`vg_aes_gcm_prepare`). Computes the same result, using the AES key schedule and hash " ++
  "subkey in its first 256 bytes, and may read the first 16 prepared powers (bytes 256 " ++
  "through 511). The powers remain secret; all other memory, aliasing and constant-time " ++
  "requirements are unchanged. Contract: `VG.Spec.Gcm." ++ contract ++ "`."

/-! ## Preconditions -/

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def sealPrepared16Pre (pb : Nat) : Curry (sealPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowers16Repr m ctx

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def openPrepared16Pre (pb : Nat) : Curry (openPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowers16Repr m ctx

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def streamCryptPrepared16Pre (pb : Nat) : Curry (streamCryptPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _data _len m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowers16Repr m ctx

/-- The existing round-count and length requirements, plus 16 prepared powers. -/
def sealGatherPrepared16Pre (pb : Nat) : Curry (sealGatherPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PreparedPowers16Repr m ctx

/-! ## Contracts and APIs -/

/-- The unchanged `sealContract` postcondition with 16 prepared powers. -/
def sealPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedSig.contract A (pre := sealPrepared16Pre A.ptrBits)
    (post := sealPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_prepared16` on every target. -/
def sealPrepared16Api : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_prepared16"
  sig := sealPreparedSig
  writeArgs := true
  contracts := some fun A stack => sealPrepared16Contract A stack
  summary := prepared16Summary "vg_aes_gcm_seal" "sealPrepared16Contract"
  safety := sealApi.safety ++ [prepared16Safety]

/-- The unchanged `openContract` postcondition with 16 prepared powers. -/
def openPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedSig.contract A (pre := openPrepared16Pre A.ptrBits)
    (post := openPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- `vg_aes_gcm_open_prepared16` on every target. -/
def openPrepared16Api : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_prepared16"
  sig := openPreparedSig
  writeArgs := true
  contracts := some fun A stack => openPrepared16Contract A stack
  summary := prepared16Summary "vg_aes_gcm_open" "openPrepared16Contract"
  safety := openApi.safety ++ [prepared16Safety]

/-- The unchanged `streamEncryptContract` postcondition with 16 prepared powers. -/
def streamEncryptPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPrepared16Pre A.ptrBits)
    (post := streamEncryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_encrypt_prepared16` on every target. -/
def streamEncryptPrepared16Api : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_encrypt_prepared16"
  sig := streamCryptPreparedSig
  writeArgs := true
  contracts := some fun A stack => streamEncryptPrepared16Contract A stack
  summary := prepared16Summary "vg_aes_gcm_stream_encrypt" "streamEncryptPrepared16Contract"
  safety := streamEncryptApi.safety ++ [prepared16Safety]

/-- The unchanged `streamDecryptContract` postcondition with 16 prepared powers. -/
def streamDecryptPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPrepared16Pre A.ptrBits)
    (post := streamDecryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_decrypt_prepared16` on every target. -/
def streamDecryptPrepared16Api : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_decrypt_prepared16"
  sig := streamCryptPreparedSig
  writeArgs := true
  contracts := some fun A stack => streamDecryptPrepared16Contract A stack
  summary := prepared16Summary "vg_aes_gcm_stream_decrypt" "streamDecryptPrepared16Contract"
  safety := streamDecryptApi.safety ++ [prepared16Safety]

/-- The unchanged `sealGatherContract` postcondition with 16 prepared powers. -/
def sealGatherPrepared16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedSig.contract A (pre := sealGatherPrepared16Pre A.ptrBits)
    (post := sealGatherPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_prepared16` on every target. -/
def sealGatherPrepared16Api : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather_prepared16"
  sig := sealGatherPreparedSig
  writeArgs := true
  contracts := some fun A stack => sealGatherPrepared16Contract A stack
  summary := prepared16Summary "vg_aes_gcm_seal_gather" "sealGatherPrepared16Contract"
  safety := sealGatherApi.safety ++ [prepared16Safety]

end VG.Spec.Gcm
