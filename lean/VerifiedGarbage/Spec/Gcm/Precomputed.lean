import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM with the powers of the hash subkey in the key context

**Trusted** (as every file in `Spec/`). A larger key context, of 1024
bytes, that also holds the powers `H¹ … H⁴⁸` of its hash subkey, so that the
functions hashing many blocks at a time need not compute them on every call:

* `vg_aes_gcm_init_precomputed` writes it: the key context of
  `vg_aes_gcm_init` (`KeyRepr`) in its first 256 bytes, and `Hᵏ` (`hpow`)
  in bytes `256 + 16 (k - 1)` to `256 + 16 k - 1`, for `k` from 1 to 48
  (`PowersRepr`), each a block as GCM writes one (`blockAt`, as `H` is in
  bytes 240–255).
* `vg_aes_gcm_seal_precomputed`, `_open_precomputed`,
  `_stream_encrypt_precomputed`, `_stream_decrypt_precomputed`,
  `_encrypt_blocks_precomputed` and `_decrypt_blocks_precomputed` are
  `vg_aes_gcm_seal`, … with such a key context, which they need to hold the
  powers of its hash subkey (`PowersRepr`, a precondition, as the number of
  rounds is): they compute exactly what those compute (the same
  postconditions, and `open` leaks the same), and may read the powers
  instead of computing them.

The first 256 bytes are those of `vg_aes_gcm_init`'s key context, so the
functions that hash no more than a block at a time (`vg_aes_gcm_stream_init`,
`_stream_aad`, `_stream_finish`, `_stream_verify`) take a pointer to them.
Existing contracts are unchanged.
-/

namespace VG.Spec.Gcm

/-- The multiplicative identity of `GF(2¹²⁸)` (§6.3): the block whose
leftmost bit is 1, which stands for the polynomial 1. -/
def one : Block := 1 <<< 127

/-- `Hᵏ`: `H` multiplied by itself `k` times in `GF(2¹²⁸)` (`mul`, §6.3). -/
def hpow (h : Block) (k : Nat) : Block := Nat.repeat (fun y => mul y h) k one

/-- The key context at `p` holds the powers `H¹ … H⁴⁸` of its hash subkey:
`Hᵏ⁺¹` is the block at `p + 256 + 16 k`. -/
def PowersRepr (m : Mem) (p : Addr) : Prop :=
  ∀ k < 48, blockAt m (p + BitVec.ofNat 64 (256 + 16 * k)) = hpow (ctxH m p) (k + 1)

/-! ## The key context -/

/-- `vg_aes_gcm_init_precomputed(key: *const u8, key_len: usize, ctx: *mut [u64; 128])`. -/
def initPrecomputedSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 128)]

/-- Makes the 1024 bytes at `ctx` the key context of the key at `key`
(`KeyRepr`: its key schedule and its hash subkey `H = CIPH_K(0¹²⁸)`) with
the powers `H¹ … H⁴⁸` (`PowersRepr`). -/
def initPrecomputedPost (pb : Nat) : initPrecomputedSig.Post pb := fun key keyLen ctx m m' _ =>
  KeyRepr m' ctx (Aes.bytesAt m key keyLen.toNat) ∧ PowersRepr m' ctx

/-- For a key of 16, 24 or 32 bytes (`initPre`): `initPrecomputedPost`. -/
def initPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initPrecomputedSig.contract A (pre := initPre A.ptrBits)
    (post := initPrecomputedPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_init_precomputed` on every target. -/
def initPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_init_precomputed"
  sig := initPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => initPrecomputedContract A stack
  summary := "The AES-GCM key setup, with the powers of the hash subkey: writes the key context \
    of the `key_len`-byte AES key at `key` to `*ctx`. Its first 256 bytes are those \
    `vg_aes_gcm_init` writes: the key schedule for `Nr = key_len / 4 + 6` rounds (FIPS 197 \
    §5.2) in the first `16 * (Nr + 1)` bytes, and the hash subkey `H = CIPH_K(0¹²⁸)` (NIST SP \
    800-38D §7.1 step 1) in bytes 240–255; bytes `256 + 16 * (k - 1)` to `256 + 16 * k - 1` \
    hold `Hᵏ`, `H` multiplied by itself `k` times in `GF(2¹²⁸)` (§6.3), for `k` from 1 to 48. \
    The other bytes are unspecified. The `vg_aes_gcm_*_precomputed` functions read it, with \
    `Nr` as their `rounds`; the others read its first 256 bytes.\n\n\
    Contract: `VG.Spec.Gcm.initPrecomputedContract`. The key context is `VG.Spec.Gcm.KeyRepr` \
    with `VG.Spec.Gcm.PowersRepr`. Constant time: only the pointers and `key_len` may affect \
    timing, not the key."
  safety := ["`key_len` must be 16, 24 or 32."]

/-- The documentation of the precondition on the key context. -/
def powersSafety : String :=
  "`*ctx` must hold the powers of its hash subkey, as `vg_aes_gcm_init_precomputed` writes them."

/-! ## Whole blocks -/

/-- `vg_aes_gcm_encrypt_blocks_precomputed(ctx: *const [u64; 128], rounds: usize, counter: *mut [u8; 16], y: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64; 264])`,
and `vg_aes_gcm_decrypt_blocks_precomputed` with the same signature:
`cryptBlocksSig` with the larger key context. -/
def cryptBlocksPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("counter", .array true .u8 16), ("y", .array true .u8 16),
    ("data", .slice true (.array .u8 16) "n"), ("scratch", .array true .u64 264)]

/-- `rounds` is 10, 12 or 14, and the key context at `ctx` holds the powers
of its hash subkey. -/
def cryptBlocksPrecomputedPre (pb : Nat) :
    Curry (cryptBlocksPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _counter _y _data _n _scratch m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PowersRepr m ctx

/-- `encryptBlocksContract`'s postcondition, with the larger key context. -/
def encryptBlocksPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksPrecomputedSig.contract A (pre := cryptBlocksPrecomputedPre A.ptrBits)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) (blocksAt m data n.toNat)
      blocksAt m' data n.toNat = c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

/-- `decryptBlocksContract`'s postcondition, with the larger key context. -/
def decryptBlocksPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  cryptBlocksPrecomputedSig.contract A (pre := cryptBlocksPrecomputedPre A.ptrBits)
    (post := fun ctx rounds counter y data n _scratch m m' _ =>
      let c := blocksAt m data n.toNat
      blocksAt m' data n.toNat = ctr32 (ctxCiph m ctx rounds.toNat) (blockAt m counter) c ∧
        blockAt m' counter = Nat.repeat inc32 n.toNat (blockAt m counter) ∧
        blockAt m' y = ghashFrom (ctxH m ctx) (blockAt m y) c)
    (stack := stack)

/-- `vg_aes_gcm_encrypt_blocks_precomputed` on every target. -/
def encryptBlocksPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_encrypt_blocks_precomputed"
  sig := cryptBlocksPrecomputedSig
  contracts := some fun A stack => encryptBlocksPrecomputedContract A stack
  summary := "`vg_aes_gcm_encrypt_blocks` with a key context of `vg_aes_gcm_init_precomputed`: \
    with the key context `*ctx` that `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, \
    does exactly  what `vg_aes_gcm_encrypt_blocks` does with its first 256 bytes (see \
    `vg_aes_gcm_encrypt_blocks`), and may read the powers of  the hash subkey that it holds \
    instead of computing them. Its constant-time guarantee is  `vg_aes_gcm_encrypt_blocks`'s, \
    the powers being as secret as the rest of the key context.\n\n\
    Contract: `VG.Spec.Gcm.encryptBlocksPrecomputedContract`."
  safety := encryptBlocksApi.safety ++ [powersSafety]

/-- `vg_aes_gcm_decrypt_blocks_precomputed` on every target. -/
def decryptBlocksPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_decrypt_blocks_precomputed"
  sig := cryptBlocksPrecomputedSig
  contracts := some fun A stack => decryptBlocksPrecomputedContract A stack
  summary := "`vg_aes_gcm_decrypt_blocks` with a key context of `vg_aes_gcm_init_precomputed`: \
    with the key context `*ctx` that `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, \
    does exactly  what `vg_aes_gcm_decrypt_blocks` does with its first 256 bytes (see \
    `vg_aes_gcm_decrypt_blocks`), and may read the powers of  the hash subkey that it holds \
    instead of computing them. Its constant-time guarantee is  `vg_aes_gcm_decrypt_blocks`'s, \
    the powers being as secret as the rest of the key context.\n\n\
    Contract: `VG.Spec.Gcm.decryptBlocksPrecomputedContract`."
  safety := decryptBlocksApi.safety ++ [powersSafety]

/-! ## One-shot -/

/-- `vg_aes_gcm_seal_precomputed(ctx: *const [u64; 128], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut [u8; 16])`:
`sealSig` with the larger key context. -/
def sealPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .array true .u8 16)]

/-- `rounds` is 10, 12 or 14, and the key context at `ctx` holds the powers
of its hash subkey. -/
def sealPrecomputedPre (pb : Nat) : Curry (sealPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PowersRepr m ctx

/-- `sealPost`, with the larger key context. -/
def sealPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealPrecomputedSig.contract A (pre := sealPrecomputedPre A.ptrBits)
    (post := sealPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_precomputed` on every target. -/
def sealPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_precomputed"
  sig := sealPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => sealPrecomputedContract A stack
  summary := "`vg_aes_gcm_seal` with a key context of `vg_aes_gcm_init_precomputed`: with the \
    key context `*ctx` that `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, does \
    exactly what `vg_aes_gcm_seal` does with its first 256 bytes (see `vg_aes_gcm_seal`), and \
    may read the powers of  the hash subkey that it holds instead of computing them. Its \
    constant-time guarantee is  `vg_aes_gcm_seal`'s, the powers being as secret as the rest of \
    the key context.\n\n\
    Contract: `VG.Spec.Gcm.sealPrecomputedContract`."
  safety := sealApi.safety ++ [powersSafety]

/-- `vg_aes_gcm_open_precomputed(ctx: *const [u64; 128], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *const u8, tag_len: usize) -> u32`:
`openSig` with the larger key context. -/
def openPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

/-- `rounds` is 10, 12 or 14, and the key context at `ctx` holds the powers
of its hash subkey. -/
def openPrecomputedPre (pb : Nat) : Curry (openPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _data _len _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PowersRepr m ctx

/-- `openPost`, with the larger key context; it may leak what `openContract`
may (`openLeak`). -/
def openPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openPrecomputedSig.contract A (pre := openPrecomputedPre A.ptrBits)
    (post := openPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openLeak A.ptrBits))

/-- `vg_aes_gcm_open_precomputed` on every target. -/
def openPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_precomputed"
  sig := openPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => openPrecomputedContract A stack
  summary := "`vg_aes_gcm_open` with a key context of `vg_aes_gcm_init_precomputed`: with the \
    key context `*ctx` that `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, does \
    exactly what `vg_aes_gcm_open` does with its first 256 bytes (see `vg_aes_gcm_open`), and \
    may read the powers of  the hash subkey that it holds instead of computing them. Its \
    constant-time guarantee is  `vg_aes_gcm_open`'s, the powers being as secret as the rest of \
    the key context.\n\n\
    Contract: `VG.Spec.Gcm.openPrecomputedContract`."
  safety := openApi.safety ++ [powersSafety]

/-! ## Streaming -/

/-- `vg_aes_gcm_stream_encrypt_precomputed(ctx: *const [u64; 128], rounds: usize, state: *mut [u64; 10], aad_len: u64, text_len: u64, data: *mut u8, len: usize)`,
and `vg_aes_gcm_stream_decrypt_precomputed` with the same signature:
`streamCryptSig` with the larger key context. -/
def streamCryptPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("state", .array true .u64 10), ("aad_len", .int .u64 true), ("text_len", .int .u64 true),
    ("data", .slice true .u8 "len")]

/-- `rounds` is 10, 12 or 14, and the key context at `ctx` holds the powers
of its hash subkey. -/
def streamTextPrecomputedPre (pb : Nat) :
    Curry (streamCryptPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _state _aadLen _textLen _data _len m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ PowersRepr m ctx

/-- `streamEncryptPost`, with the larger key context. -/
def streamEncryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedSig.contract A (pre := streamTextPrecomputedPre A.ptrBits)
    (post := streamEncryptPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `streamDecryptPost`, with the larger key context. -/
def streamDecryptPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptPrecomputedSig.contract A (pre := streamTextPrecomputedPre A.ptrBits)
    (post := streamDecryptPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_stream_encrypt_precomputed` on every target. -/
def streamEncryptPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_encrypt_precomputed"
  sig := streamCryptPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => streamEncryptPrecomputedContract A stack
  summary := "`vg_aes_gcm_stream_encrypt` with a key context of `vg_aes_gcm_init_precomputed`: \
    with the key context `*ctx` that `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, \
    does exactly  what `vg_aes_gcm_stream_encrypt` does with its first 256 bytes (see \
    `vg_aes_gcm_stream_encrypt`), and may read the powers of  the hash subkey that it holds \
    instead of computing them. Its constant-time guarantee is  `vg_aes_gcm_stream_encrypt`'s, \
    the powers being as secret as the rest of the key context.\n\n\
    Contract: `VG.Spec.Gcm.streamEncryptPrecomputedContract`."
  safety := streamEncryptApi.safety ++ [powersSafety]

/-- `vg_aes_gcm_stream_decrypt_precomputed` on every target. -/
def streamDecryptPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_stream_decrypt_precomputed"
  sig := streamCryptPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => streamDecryptPrecomputedContract A stack
  summary := "`vg_aes_gcm_stream_decrypt` with a key context of `vg_aes_gcm_init_precomputed`: \
    with the key context `*ctx` that `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, \
    does exactly  what `vg_aes_gcm_stream_decrypt` does with its first 256 bytes (see \
    `vg_aes_gcm_stream_decrypt`), and may read the powers of  the hash subkey that it holds \
    instead of computing them. Its constant-time guarantee is  `vg_aes_gcm_stream_decrypt`'s, \
    the powers being as secret as the rest of the key context.\n\n\
    Contract: `VG.Spec.Gcm.streamDecryptPrecomputedContract`."
  safety := streamDecryptApi.safety ++ [powersSafety]

end VG.Spec.Gcm
