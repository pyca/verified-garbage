module

public import VerifiedGarbage.Spec.Gcm.OutOfPlace

/-!
# AES-GCM with prepared GHASH powers

**Trusted.** A separate 1032-byte key-context format for implementations that
consume powers directly in a carry-less multiplication representation.
The first 256 bytes are the existing `KeyRepr`; the next 768 bytes hold up
to 24 pairs, with the even power first and the odd power second, each
encoded by `preparedPower` and stored little-endian; the 64-bit word at byte
1024 counts the powers present (`PreparedRepr`): 48 (24 pairs), 16 (the
first 8 pairs, bytes 256 through 511) or 0, so that a `prepare` computes only
the powers its CPU's functions read. This is a storage convention, not a
change to GCM's field arithmetic (NIST SP 800-38D §6.3).

These APIs have the existing GCM postconditions, memory bounds, disjointness
and secrecy guarantees. Their prepared-power precondition differs from
`PowersRepr`, so they have distinct names: a prepared context must never be
passed to a `*_precomputed` API, or vice versa. The APIs that read only the
first 256 bytes (stream initialization, AAD, finish and verify) remain usable.
The functions on a prepared context may leak how many of its powers are
present (`flagLeak`), which says only which code ran, nothing of the key.
Existing specifications and contracts are unchanged.
-/

@[expose] public section

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

/-- The first 8 pairs of `PreparedPowersRepr`, bytes 256 through 511: the
first 16 powers. -/
def PreparedPowers16Repr (m : Mem) (p : Addr) : Prop :=
  ∀ k < 8,
    m.readW (p + BitVec.ofNat 64 (256 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 2)) ∧
    m.readW (p + BitVec.ofNat 64 (272 + 32 * k)) 128 =
      preparedPower (hpow (ctxH m p) (2 * k + 1))

/-- The count of powers of the prepared key context at `p`: the 64-bit word
at byte 1024. -/
def powerCount (m : Mem) (p : Addr) : Nat := (m.readW (p + 1024) 64).toNat

/-- A prepared key context: if its count is at least 16, the first 16 powers
are present (`PreparedPowers16Repr`), and if it is at least 48, all 48
(`PreparedPowersRepr`). -/
def PreparedRepr (m : Mem) (p : Addr) : Prop :=
  (16 ≤ powerCount m p → PreparedPowers16Repr m p) ∧
    (48 ≤ powerCount m p → PreparedPowersRepr m p)

/-- What a function on the prepared key context at `p` may leak of it: which
of the counts that tell its functions apart it has (at least 48, at least 16,
or fewer). -/
def flagLeak (m : Mem) (p : Addr) : Nat :=
  if 48 ≤ powerCount m p then 2 else if 16 ≤ powerCount m p then 1 else 0

/-- A 1032-byte context, whose first 256 bytes are a key context. -/
def prepareSig : Sig where
  params := [("ctx", .array true .u64 129)]

/-- Keeps the first 256 bytes, and makes the context a prepared key context of
the hash subkey in its bytes 240–255 (`ctxH`): writes 48, 16 or none of its
prepared powers, and their count. With those bytes a key context
(`KeyRepr`, as `vg_aes_gcm_init` writes it), the result is the prepared key
context of the same key (`KeyRepr` and `PreparedRepr`). -/
def preparePost (pb : Nat) : prepareSig.Post pb := fun ctx m m' _ =>
  Aes.bytesAt m' ctx 256 = Aes.bytesAt m ctx 256 ∧ PreparedRepr m' ctx

/-- No precondition: the powers are those of whatever hash subkey the
context holds. -/
def prepareContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  prepareSig.contract A (post := preparePost A.ptrBits) (writeArgs := true) (stack := stack)

/-- Prepares a key context in place on any target, without the key. -/
def prepareApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_prepare"
  sig := prepareSig
  writeArgs := true
  contracts := some fun A stack => prepareContract A stack
  summary := "Makes the 1032-byte `*ctx`, whose first 256 bytes are a key context of \
    `vg_aes_gcm_init`, the prepared key context of the same key, in place: keeps its first \
    256 bytes, at byte `256 + 32*k`, for `k` from 0 to `n/2 - 1`, stores \
    `preparedPower(H^(2*k+2))` and then `preparedPower(H^(2*k+1))`, as two little-endian \
    128-bit words, `H` being the hash subkey in its bytes 240–255, and stores `n` in the \
    64-bit word at byte 1024, `n` being 48, 16 or 0, as the implementation's other \
    functions read. Use only the \
    `*_prepared` APIs, or APIs that read the first 256 bytes, with this format. \
    Contract: `VG.Spec.Gcm.prepareContract`: the first 256 bytes are kept and the context \
    satisfies `PreparedRepr`. Constant time: only the pointer may affect timing, not \
    the hash subkey."
  safety := []

/-- `vg_aes_gcm_wipe_prepared(ctx: *mut [u64; 129])`. -/
def wipePreparedSig : Sig where
  params := [("ctx", .array true .u64 129)]

/-- How many bytes of the prepared key context at `p` hold secrets: the key
context and the powers its count says are present, 48 (1024 bytes in all),
16 (512) or none (256). -/
def wipePreparedLen (m : Mem) (p : Addr) : Nat :=
  if 48 ≤ powerCount m p then 1024 else if 16 ≤ powerCount m p then 512 else 256

/-- Zeroes the first `wipePreparedLen` bytes, as the count was on entry. -/
def wipePreparedPost (pb : Nat) : wipePreparedSig.Post pb := fun ctx m m' _ =>
  Aes.bytesAt m' ctx (wipePreparedLen m ctx) = List.replicate (wipePreparedLen m ctx) 0

/-- What `wipe` may leak: `flagLeak`. -/
def wipePreparedLeak (pb : Nat) : Curry (wipePreparedSig.words pb) (Mem → List Nat) :=
  fun ctx m => [flagLeak m ctx]

/-- No precondition: the count says how much to zero, whatever it is. -/
def wipePreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  wipePreparedSig.contract A (post := wipePreparedPost A.ptrBits) (writeArgs := true)
    (stack := stack) (leak := some (wipePreparedLeak A.ptrBits))

/-- Wipes a prepared key context on any target. -/
def wipePreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_wipe_prepared"
  sig := wipePreparedSig
  writeArgs := true
  contracts := some fun A stack => wipePreparedContract A stack
  summary := "Wipes the 1032-byte `*ctx`, a prepared key context of `vg_aes_gcm_prepare`: \
    sets to zero the key context and the powers its count (the 64-bit word at byte 1024) \
    says are present: its first 1024 bytes if the count is at least 48, 512 if it is at \
    least 16, and 256 otherwise (the bytes after them were not written). \
    Contract: `VG.Spec.Gcm.wipePreparedContract`. Constant time: only the pointer and \
    which of those the count is may affect timing, not the bytes wiped."
  safety := []

/-- Prepared-context validity, in addition to each API's existing safety requirements. -/
def preparedSafety : String :=
  "`*ctx` must have the prepared format written by `vg_aes_gcm_prepare` (not the format of `vg_aes_gcm_init_precomputed`)."

/-- Common documentation for the prepared APIs. -/
def preparedSummary (name contract : String) : String :=
  "`" ++ name ++ "` with a 1032-byte context from `vg_aes_gcm_prepare`. " ++
  "Computes the same result, using the AES key schedule and hash subkey in its first " ++
  "256 bytes, and may read the prepared powers its count says are present. The powers remain " ++
  "secret; how many are present may affect timing; all other memory, aliasing and " ++
  "constant-time requirements are unchanged. Contract: `VG.Spec.Gcm." ++ contract ++ "`."

/-- The existing signature with a prepared 1032-byte context. -/
def sealPreparedSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16)]

/-- The existing round-count and length requirements, on a prepared key context. -/
def sealPreparedPre (pb : Nat) : Curry (sealPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedRepr m ctx

/-- The existing signature with a prepared 1032-byte context. -/
def openPreparedSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

/-- The existing round-count and length requirements, on a prepared key context. -/
def openPreparedPre (pb : Nat) : Curry (openPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedRepr m ctx

/-- The existing signature with a prepared 1032-byte context. -/
def streamCryptPreparedSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("data", .slice true .u8 "len")]

/-- The existing round-count and length requirements, on a prepared key context. -/
def streamCryptPreparedPre (pb : Nat) : Curry (streamCryptPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _data _len m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      PreparedRepr m ctx

/-- The existing signature with a prepared 1032-byte context. -/
def sealGatherPreparedSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

/-- The existing round-count and length requirements, on a prepared key context. -/
def sealGatherPreparedPre (pb : Nat) : Curry (sealGatherPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PreparedRepr m ctx

/-- The existing signature with a prepared 1032-byte context. -/
def openToPreparedSig : Sig where
  params := [("ctx", .array false .u64 129), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"),
    ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

/-- The existing round-count and length requirements, on a prepared key context. -/
def openToPreparedPre (pb : Nat) : Curry (openToPreparedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src len _dst dstLen _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen.toNat = len.toNat ∧ PreparedRepr m ctx

/-- What `seal` may leak: how many powers are present. -/
def sealPreparedLeak (pb : Nat) : Curry (sealPreparedSig.words pb) (Mem → List Nat) :=
  fun ctx _rounds _nonce _nonceLen _aad _aadLen _data _len _tag m => [flagLeak m ctx]

/-- What `open` may leak: how many powers are present, and `openLeak`. -/
def openPreparedLeak (pb : Nat) : Curry (openPreparedSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m =>
    flagLeak m ctx :: openLeak pb ctx rounds nonce nonceLen aad aadLen data len tag tagLen m

/-- What the streams may leak: how many powers are present. -/
def streamCryptPreparedLeak (pb : Nat) : Curry (streamCryptPreparedSig.words pb) (Mem → List Nat) :=
  fun ctx _rounds _state _aadLen _textLen _data _len m => [flagLeak m ctx]

/-- What `seal_gather` may leak: how many powers are present. -/
def sealGatherPreparedLeak (pb : Nat) : Curry (sealGatherPreparedSig.words pb) (Mem → List Nat) :=
  fun ctx _rounds _nonce _nonceLen _aad _aadLen _src _srcCount _dst _len _tag m => [flagLeak m ctx]

/-- What `open_to` may leak: how many powers are present, and `openToLeak`. -/
def openToPreparedLeak (pb : Nat) : Curry (openToPreparedSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m =>
    flagLeak m ctx :: openToLeak pb ctx rounds nonce nonceLen aad aadLen src len dst dstLen tag tagLen m

/-- The unchanged `sealContract` postcondition on a prepared key context. -/
def sealPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPreparedSig.contract A (pre := sealPreparedPre A.ptrBits)
    (post := sealPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealPreparedLeak A.ptrBits))

/-- `vg_aes_gcm_seal_prepared` on every target. -/
def sealPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_prepared"
  sig := sealPreparedSig
  writeArgs := true
  contracts := some fun A stack => sealPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_seal" "sealPreparedContract"
  safety := sealApi.safety ++ [preparedSafety]

/-- The unchanged `openContract` postcondition on a prepared key context. -/
def openPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPreparedSig.contract A (pre := openPreparedPre A.ptrBits)
    (post := openPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openPreparedLeak A.ptrBits))

/-- `vg_aes_gcm_open_prepared` on every target. -/
def openPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_prepared"
  sig := openPreparedSig
  writeArgs := true
  contracts := some fun A stack => openPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_open" "openPreparedContract"
  safety := openApi.safety ++ [preparedSafety]

/-- The unchanged `streamEncryptContract` postcondition on a prepared key context. -/
def streamEncryptPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := streamEncryptPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptPreparedLeak A.ptrBits))

/-- `vg_aes_gcm_stream_encrypt_prepared` on every target. -/
def streamEncryptPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_encrypt_prepared"
  sig := streamCryptPreparedSig
  writeArgs := true
  contracts := some fun A stack => streamEncryptPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_stream_encrypt" "streamEncryptPreparedContract"
  safety := streamEncryptApi.safety ++ [preparedSafety]

/-- The unchanged `streamDecryptContract` postcondition on a prepared key context. -/
def streamDecryptPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPreparedSig.contract A (pre := streamCryptPreparedPre A.ptrBits)
    (post := streamDecryptPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (streamCryptPreparedLeak A.ptrBits))

/-- `vg_aes_gcm_stream_decrypt_prepared` on every target. -/
def streamDecryptPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_decrypt_prepared"
  sig := streamCryptPreparedSig
  writeArgs := true
  contracts := some fun A stack => streamDecryptPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_stream_decrypt" "streamDecryptPreparedContract"
  safety := streamDecryptApi.safety ++ [preparedSafety]

/-- The unchanged `sealGatherContract` postcondition on a prepared key context. -/
def sealGatherPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPreparedSig.contract A (pre := sealGatherPreparedPre A.ptrBits)
    (post := sealGatherPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (sealGatherPreparedLeak A.ptrBits))

/-- `vg_aes_gcm_seal_gather_prepared` on every target. -/
def sealGatherPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather_prepared"
  sig := sealGatherPreparedSig
  writeArgs := true
  contracts := some fun A stack => sealGatherPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_seal_gather" "sealGatherPreparedContract"
  safety := sealGatherApi.safety ++ [preparedSafety]


/-- The unchanged `openToContract` postcondition on a prepared key context. -/
def openToPreparedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPreparedSig.contract A (pre := openToPreparedPre A.ptrBits)
    (post := openToPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToPreparedLeak A.ptrBits))

/-- `vg_aes_gcm_open_to_prepared` on every target. -/
def openToPreparedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_to_prepared"
  sig := openToPreparedSig
  writeArgs := true
  contracts := some fun A stack => openToPreparedContract A stack
  summary := preparedSummary "vg_aes_gcm_open_to" "openToPreparedContract"
  safety := openToApi.safety ++ [preparedSafety]

end VG.Spec.Gcm
