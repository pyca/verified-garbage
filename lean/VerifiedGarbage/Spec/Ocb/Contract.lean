import VerifiedGarbage.Spec.Ocb
import VerifiedGarbage.TCB.Artifact

/-!
# AES-OCB: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of AES-OCB (OCB3), in
terms of `Spec/Ocb.lean`, for any target: `A` is the target's calling
convention. The signatures fix where the arguments are, the memory each
function may access, disjointness, and that the pointers, the lengths, the
number of rounds and the tag length are public (see `TCB/Sig.lean`); the
contracts add the rest. Everything else (keys, key contexts, nonces,
associated data, texts and tags) is secret.

* `vg_aes_ocb_init` writes a key context (`KeyRepr`): the key schedule and
  `L_* = ENCIPHER(K, zeros(128))`. The others read one, with its number of
  rounds, and compute with the ciphers of its key schedule and its `L_*`
  (`ctxCiph`, `ctxInv`, `ctxLstar`): with a context `vg_aes_ocb_init`
  wrote, that is AES-OCB with its key (`encryptWith_ctx`,
  `decryptWith_ctx`).
* `vg_aes_ocb_seal` is `OCB-ENCRYPT` (`encryptWith`): it encrypts the data in
  place and writes the tag of `tag_len` bytes.
* `vg_aes_ocb_open` is `OCB-DECRYPT` (`decryptWith`): given the encrypted
  data in place and the tag, it decrypts, and if the tag is wrong
  overwrites the data with zeros, so that the unauthenticated plaintext is
  never released. Whether the tag is right is public: `open` may leak it (it
  is the result), and nothing else secret.

The lengths are public, and the tag length and the nonce length, which the
algorithm depends on, are preconditions (`lengthsOk`: a tag of 1 to 16
bytes, a nonce of 1 to 15 bytes), which the caller checks; RFC 7253 bounds
no other length (§3.1). `seal` writes the tag to the `tag_len` bytes at
`tag`, and `open` reads the received tag from the `tag_len` bytes at `tag`.
The functions keep their working space on the stack. The postconditions
(and `open`'s leak) are stated for `rounds` of 10, 12 or 14, which the
preconditions require, so that they read only the buffers (the key
context's round keys for those rounds and its `L_*`).

Every contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see `Sig.contract`),
0 for one that uses none; the functions may overwrite their arguments passed
in memory, where the calling convention allows it (`writeArgs`), to pass
arguments to the functions they call.
-/

namespace VG.Spec.Ocb

/-! ## The key context -/

/-- `vg_aes_ocb_init(key: *const u8, key_len: usize, ctx: *mut [u64; 32])`. -/
def initSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 32)]

/-- `init`'s precondition: a key of 16, 24 or 32 bytes. -/
def initPre (pb : Nat) : Curry (initSig.words pb) (Mem → Prop) := fun _key keyLen _ctx _ =>
  keyLen.toNat = 16 ∨ keyLen.toNat = 24 ∨ keyLen.toNat = 32

/-- Makes the 256 bytes at `ctx` the key context of the key at `key`: its key
schedule and `L_* = ENCIPHER(K, zeros(128))`. -/
def initPost (pb : Nat) : initSig.Post pb := fun key keyLen ctx m m' _ =>
  KeyRepr m' ctx (Aes.bytesAt m key keyLen.toNat)

/-- For a key of 16, 24 or 32 bytes at `key`: `initPost`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A (pre := initPre A.ptrBits) (post := initPost A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `vg_aes_ocb_init` on every target. -/
def initApi : Api where
  module := "aes_ocb"
  name := "vg_aes_ocb_init"
  sig := initSig
  writeArgs := true
  contracts := some fun A stack => initContract A stack
  summary := "The AES-OCB key setup (RFC 7253 §4.1): writes the key context of the \
    `key_len`-byte AES key at `key` to `*ctx`: its key schedule for `Nr = key_len / 4 + 6` \
    rounds (FIPS 197 §5.2, as `vg_aes_expand_key` writes it) in the first `16 * (Nr + 1)` \
    bytes, and `L_* = ENCIPHER(K, zeros(128))` in bytes 240–255. The other bytes are \
    unspecified. The other `vg_aes_ocb_*` functions read it, with `Nr` as their `rounds`.\n\n\
    Contract: `VG.Spec.Ocb.initContract`. The key context is `VG.Spec.Ocb.KeyRepr`. Constant \
    time: only the pointers and `key_len` may affect timing, not the key."
  safety := ["`key_len` must be 16, 24 or 32."]

/-! ## Encryption and decryption -/

/-- `vg_aes_ocb_seal(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *mut u8, tag_len: usize)`.
`rounds` and `tag_len` are public. -/
def sealSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice true .u8 "tag_len")]

/-- `vg_aes_ocb_open(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, data: *mut u8, len: usize, tag: *const u8, tag_len: usize) -> u32`.
`rounds` and `tag_len` are public. -/
def openSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("data", .slice true .u8 "len"), ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

/-- `vg_aes_ocb_seal`'s precondition: `rounds` is 10, 12 or 14, the tag is 1
to 16 bytes and the nonce 1 to 15 bytes. -/
def sealPre (pb : Nat) : Curry (sealSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _nonce nonceLen _aad _aadLen _data _len _tag tagLen _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      lengthsOk tagLen.toNat nonceLen.toNat

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`: the `len`
bytes at `data` are encrypted, with the nonce at `nonce` and the `aad_len`
bytes of associated data at `aad` (`encryptWith`), and the tag of `tag_len`
bytes is at `tag`. -/
def sealPost (pb : Nat) : sealSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    encryptWith (ctxCiph m ctx rounds.toNat) (ctxLstar m ctx) tagLen.toNat
        (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m aad aadLen.toNat)
        (Aes.bytesAt m data len.toNat) =
      (Aes.bytesAt m' data len.toNat, Aes.bytesAt m' tag tagLen.toNat)

/-- For `rounds` of 10, 12 or 14, a tag of 1 to 16 bytes and a nonce of 1 to
15 bytes, with the key context at `ctx`: encrypts the `len` bytes at `data`
in place, with the nonce at `nonce` and the `aad_len` bytes of associated
data at `aad` (`encryptWith`), and writes the tag of `tag_len` bytes to
`tag`. -/
def sealContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSig.contract A (pre := sealPre A.ptrBits) (post := sealPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_ocb_seal` on every target. -/
def sealApi : Api where
  module := "aes_ocb"
  name := "vg_aes_ocb_seal"
  sig := sealSig
  writeArgs := true
  contracts := some fun A stack => sealContract A stack
  summary := "AES-OCB authenticated encryption (RFC 7253 §4.2, `OCB-ENCRYPT`, with \
    `TAGLEN = 8 * tag_len`): with the key context `*ctx` that `vg_aes_ocb_init` wrote for \
    `rounds` rounds, encrypts the `len` bytes at `data` in place, under the `nonce_len`-byte \
    nonce at `nonce`, and writes the tag of `tag_len` bytes, of the data and the `aad_len` \
    bytes of associated data at `aad`, to the `tag_len` bytes at `tag`. The RFC's ciphertext \
    is the encrypted data followed by the tag. A nonce must never be used twice with the same \
    key.\n\n\
    Contract: `VG.Spec.Ocb.sealContract`. Constant time: only the pointers, `rounds`, the \
    lengths and `tag_len` may affect timing, not the key context, the nonce, the associated \
    data or the data."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "`tag_len` must be from 1 to 16, and `nonce_len` from 1 to 15 (RFC 7253 §3.1)."]

/-- `vg_aes_ocb_open`'s precondition: `vg_aes_ocb_seal`'s. -/
def openPre (pb : Nat) : Curry (openSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _nonce nonceLen _aad _aadLen _data _len _tag tagLen _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      lengthsOk tagLen.toNat nonceLen.toNat

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
received tag the `tag_len` bytes at `tag`: if the tag is right for the `len`
bytes of encrypted data at `data`, the nonce at `nonce` and the `aad_len`
bytes of associated data at `aad` (`decryptWith`), the result is 1 and the
plaintext is at `data`; otherwise the result is 0 and zeros are at
`data`. -/
def openPost (pb : Nat) : openSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    match decryptWith (ctxCiph m ctx rounds.toNat) (ctxInv m ctx rounds.toNat)
        (ctxLstar m ctx) tagLen.toNat (Aes.bytesAt m nonce nonceLen.toNat)
        (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m data len.toNat)
        (Aes.bytesAt m tag tagLen.toNat) with
    | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat

/-- What `vg_aes_ocb_open` may leak, for `rounds` of 10, 12 or 14: whether it
returns 1 (`decryptWith`'s outcome). -/
def openLeak (pb : Nat) : Curry (openSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen data len tag tagLen m =>
    if ¬(rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) then [] else
    [if (decryptWith (ctxCiph m ctx rounds.toNat) (ctxInv m ctx rounds.toNat)
        (ctxLstar m ctx) tagLen.toNat (Aes.bytesAt m nonce nonceLen.toNat)
        (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m data len.toNat)
        (Aes.bytesAt m tag tagLen.toNat)).isSome
      then 1 else 0]

/-- For `rounds` of 10, 12 or 14, a tag of 1 to 16 bytes and a nonce of 1 to
15 bytes, with the key context at `ctx` and the received tag the `tag_len`
bytes at `tag`: if the tag is right for the `len` bytes of encrypted data at
`data`, the nonce at `nonce` and the `aad_len` bytes of associated data at
`aad` (`decryptWith`), returns 1 and leaves the plaintext at `data`;
otherwise returns 0 and leaves zeros at `data`. May leak which
(`decryptWith`'s outcome). -/
def openContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openSig.contract A (pre := openPre A.ptrBits) (post := openPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (openLeak A.ptrBits))

/-- `vg_aes_ocb_open` on every target. -/
def openApi : Api where
  module := "aes_ocb"
  name := "vg_aes_ocb_open"
  sig := openSig
  writeArgs := true
  contracts := some fun A stack => openContract A stack
  summary := "AES-OCB authenticated decryption (RFC 7253 §4.3, `OCB-DECRYPT`, with \
    `TAGLEN = 8 * tag_len`): with the key context `*ctx` that `vg_aes_ocb_init` wrote for \
    `rounds` rounds and the received tag (the last `tag_len` bytes of the RFC's ciphertext) the \
    `tag_len` bytes at `tag`, decrypts the `len` bytes of encrypted data at `data` in place, \
    under the `nonce_len`-byte nonce at `nonce`, and returns 1 if the tag is that of the data \
    and the `aad_len` bytes of associated data at `aad`; otherwise returns 0 and overwrites the \
    `len` bytes at `data` with zeros. The tags are compared without a branch.\n\n\
    Contract: `VG.Spec.Ocb.openContract`. Constant time but for the result: only the pointers, \
    `rounds`, the lengths, `tag_len` and whether the function returns 1 or 0 may affect timing, \
    not the key context, the nonce, the associated data, the data or the tag."
  safety := [
    "`rounds` must be 10, 12 or 14.",
    "`tag_len` must be from 1 to 16, and `nonce_len` from 1 to 15 (RFC 7253 §3.1)."]

end VG.Spec.Ocb
