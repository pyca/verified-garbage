import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# AES-GCM with prepared GHASH powers

**Trusted.** A separate 1024-byte key-context format for implementations that
consume powers directly in a carry-less multiplication representation.
The first 256 bytes are the existing `KeyRepr`; the remaining 768 bytes hold
24 pairs, with the even power first and the odd power second, each encoded
by `preparedPower` and stored little-endian. This is a storage convention,
not a change to GCM's field arithmetic (NIST SP 800-38D §6.3).

These APIs have the existing GCM postconditions, memory bounds, disjointness
and secrecy guarantees. Their prepared-power precondition differs from
`PowersRepr`, so they have distinct names: a prepared context must never be
passed to a `*_precomputed` API, or vice versa. The APIs that read only the
first 256 bytes (stream initialization, AAD, finish and verify) remain usable.
Existing specifications and contracts are unchanged.
-/

namespace VG.Spec.Gcm

/-- A storage encoding of a GHASH power. Shift the 128-bit block left by one
bit, discarding overflow, and XOR `0xc2000000000000000000000000000001` if
its most significant bit was set. The numeric value uses GCM's `Block`
convention; `PreparedPowersRepr` specifies its little-endian storage.
The operation is specified explicitly so implementations must prove their
conversion and multiplication steps against the unchanged GCM postconditions. -/
def preparedPower (v : Block) : Block :=
  (v <<< 1) ^^^ (if v.getMsbD 0 then 0xc2000000000000000000000000000001 else 0)

/-- Pair `k` contains the encoded `H^(2k+2)` then `H^(2k+1)`, each as a
little-endian 128-bit word. The 24 pairs occupy bytes 256 through 1023. -/
def PreparedPowersRepr (m : Mem) (p : Addr) : Prop :=
  ∀ k < 24,
    m.readW (p + BitVec.ofNat 64 (256 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 2)) ∧
    m.readW (p + BitVec.ofNat 64 (272 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 1))

/-- The existing 1024-byte key-setup signature, with a distinct context format. -/
abbrev initPreparedSig := initPrecomputedSig

/-- Writes the AES key schedule and hash subkey, and all 48 prepared powers. -/
def initPreparedPost (pb : Nat) : initPreparedSig.Post pb := fun key keyLen ctx m m' _ =>
  KeyRepr m' ctx (Aes.bytesAt m key keyLen.toNat) ∧ PreparedPowersRepr m' ctx

/-- Key lengths, memory access and public arguments are those of key setup. -/
def initPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initPreparedSig.contract A (pre := initPre A.ptrBits)
    (post := initPreparedPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- Writes the prepared key context on any target. -/
def initPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_init_prepared"
  sig := initPreparedSig
  writeArgs := true
  contracts := some fun A stack => initPreparedContract A stack
  summary := "Writes a 1024-byte AES-GCM key context. The first 256 bytes are the key schedule \
    and hash subkey of `vg_aes_gcm_init`. At byte `256 + 32*k`, for `k` from 0 to 23, \
    stores `preparedPower(H^(2*k+2))` and then `preparedPower(H^(2*k+1))`, as two \
    little-endian 128-bit words. The encoding is `VG.Spec.Gcm.preparedPower`; the \
    context satisfies `KeyRepr` and `PreparedPowersRepr`. Use only the `*_prepared` \
    APIs, or APIs that read the first 256 bytes, with this format. Only the pointers \
    and key length are public. Contract: `VG.Spec.Gcm.initPreparedContract`."
  safety := initPrecomputedApi.safety

/-- Prepared-context validity, in addition to each API's existing safety requirements. -/
def preparedSafety : String :=
  "`*ctx` must have the prepared format written by `vg_aes_gcm_init_prepared` (not the format of `vg_aes_gcm_init_precomputed`)."

/-- Common documentation for the prepared APIs. -/
def preparedSummary (name contract : String) : String :=
  "`" ++ name ++ "` with a 1024-byte context from `vg_aes_gcm_init_prepared`. " ++
  "Computes the same result, using the AES key schedule and hash subkey in its first " ++
  "256 bytes, and may read the 48 prepared powers. The powers remain secret; all " ++
  "other memory, aliasing and constant-time requirements are unchanged. Contract: `VG.Spec.Gcm." ++
  contract ++ "`."

/-- The existing signature with a prepared 1024-byte context. -/
abbrev cryptBlocksPreparedSig := cryptBlocksPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def cryptBlocksPreparedPre (pb : Nat) : Curry (cryptBlocksPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _counter _y _data _n _scratch m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowersRepr m ctx

/-- The existing signature with a prepared 1024-byte context. -/
abbrev sealPreparedSig := sealPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def sealPreparedPre (pb : Nat) : Curry (sealPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowersRepr m ctx

/-- The existing signature with a prepared 1024-byte context. -/
abbrev openPreparedSig := openPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def openPreparedPre (pb : Nat) : Curry (openPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowersRepr m ctx

/-- The existing signature with a prepared 1024-byte context. -/
abbrev streamCryptPreparedSig := streamCryptPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def streamCryptPreparedPre (pb : Nat) : Curry (streamCryptPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _data _len m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedPowersRepr m ctx

/-- The existing signature with a prepared 1024-byte context. -/
abbrev encryptBlocksToPreparedSig := encryptBlocksToPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def encryptBlocksToPreparedPre (pb : Nat) : Curry (encryptBlocksToPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _counter _y _src n _dst dstN _scratch m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstN = n ∧ PreparedPowersRepr m ctx

/-- The existing signature with a prepared 1024-byte context. -/
abbrev streamEncryptToPreparedSig := streamEncryptToPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def streamEncryptToPreparedPre (pb : Nat) : Curry (streamEncryptToPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _src len _dst dstLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen = len ∧ PreparedPowersRepr m ctx

/-- The existing signature with a prepared 1024-byte context. -/
abbrev sealGatherPreparedSig := sealGatherPrecomputedSig

/-- The existing round-count and length requirements, plus the prepared powers. -/
def sealGatherPreparedPre (pb : Nat) : Curry (sealGatherPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PreparedPowersRepr m ctx

/-- The unchanged `encryptBlocksContract` postcondition with prepared powers. -/
def encryptBlocksPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksPreparedSig.contract A (pre := cryptBlocksPreparedPre A.ptrBits)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

/-- `vg_aes_gcm_encrypt_blocks_prepared` on every target. -/
def encryptBlocksPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_encrypt_blocks_prepared"
  sig := cryptBlocksPreparedSig
  contracts := some fun A stack => encryptBlocksPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_encrypt_blocks" "encryptBlocksPreparedContract"
  safety := encryptBlocksApi.safety ++ [preparedSafety]

/-- The unchanged `decryptBlocksContract` postcondition with prepared powers. -/
def decryptBlocksPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksPreparedSig.contract A (pre := cryptBlocksPreparedPre A.ptrBits)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := blocksAt m data n.toNat
      blocksAt m' data n.toNat = ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

/-- `vg_aes_gcm_decrypt_blocks_prepared` on every target. -/
def decryptBlocksPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_decrypt_blocks_prepared"
  sig := cryptBlocksPreparedSig
  contracts := some fun A stack => decryptBlocksPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_decrypt_blocks" "decryptBlocksPreparedContract"
  safety := decryptBlocksApi.safety ++ [preparedSafety]

/-- The unchanged `sealContract` postcondition with prepared powers. -/
def sealPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedSig.contract A (pre := sealPreparedPre A.ptrBits)
    (post := sealPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_prepared` on every target. -/
def sealPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_prepared"
  sig := sealPreparedSig
  writeArgs := true
  contracts := some fun A stack => sealPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_seal" "sealPreparedContract"
  safety := sealApi.safety ++ [preparedSafety]

/-- The unchanged `openContract` postcondition with prepared powers. -/
def openPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedSig.contract A (pre := openPreparedPre A.ptrBits)
    (post := openPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- `vg_aes_gcm_open_prepared` on every target. -/
def openPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_prepared"
  sig := openPreparedSig
  writeArgs := true
  contracts := some fun A stack => openPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_open" "openPreparedContract"
  safety := openApi.safety ++ [preparedSafety]

/-- The unchanged `streamEncryptContract` postcondition with prepared powers. -/
def streamEncryptPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := streamEncryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_encrypt_prepared` on every target. -/
def streamEncryptPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_encrypt_prepared"
  sig := streamCryptPreparedSig
  writeArgs := true
  contracts := some fun A stack => streamEncryptPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_stream_encrypt" "streamEncryptPreparedContract"
  safety := streamEncryptApi.safety ++ [preparedSafety]

/-- The unchanged `streamDecryptContract` postcondition with prepared powers. -/
def streamDecryptPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := streamDecryptPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_decrypt_prepared` on every target. -/
def streamDecryptPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_decrypt_prepared"
  sig := streamCryptPreparedSig
  writeArgs := true
  contracts := some fun A stack => streamDecryptPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_stream_decrypt" "streamDecryptPreparedContract"
  safety := streamDecryptApi.safety ++ [preparedSafety]

/-- The unchanged `encryptBlocksToContract` postcondition with prepared powers. -/
def encryptBlocksToPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptBlocksToPreparedSig.contract A (pre := encryptBlocksToPreparedPre A.ptrBits)
    (post := encryptBlocksToPost A.ptrBits)
    (stack := stack)

/-- `vg_aes_gcm_encrypt_blocks_to_prepared` on every target. -/
def encryptBlocksToPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_encrypt_blocks_to_prepared"
  sig := encryptBlocksToPreparedSig
  contracts := some fun A stack => encryptBlocksToPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_encrypt_blocks_to" "encryptBlocksToPreparedContract"
  safety := encryptBlocksToApi.safety ++ [preparedSafety]

/-- The unchanged `streamEncryptToContract` postcondition with prepared powers. -/
def streamEncryptToPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamEncryptToPreparedSig.contract A (pre := streamEncryptToPreparedPre A.ptrBits)
    (post := streamEncryptToPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_encrypt_to_prepared` on every target. -/
def streamEncryptToPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_encrypt_to_prepared"
  sig := streamEncryptToPreparedSig
  writeArgs := true
  contracts := some fun A stack => streamEncryptToPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_stream_encrypt_to" "streamEncryptToPreparedContract"
  safety := streamEncryptToApi.safety ++ [preparedSafety]

/-- The unchanged `sealGatherContract` postcondition with prepared powers. -/
def sealGatherPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedSig.contract A (pre := sealGatherPreparedPre A.ptrBits)
    (post := sealGatherPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_prepared` on every target. -/
def sealGatherPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather_prepared"
  sig := sealGatherPreparedSig
  writeArgs := true
  contracts := some fun A stack => sealGatherPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_seal_gather" "sealGatherPreparedContract"
  safety := sealGatherApi.safety ++ [preparedSafety]

end VG.Spec.Gcm
