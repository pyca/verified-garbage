import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.TCB.Artifact

/-!
# AES-SIV: the contracts, on every target

**Trusted** (as every file in `Spec/`). The contracts of AES-SIV, in terms of
`Spec/Siv.lean`, for any target: `A` is the target's calling convention.
The signatures fix where the arguments are, the memory each function may
access, disjointness, and that the pointers, the lengths and the number of
rounds are public (see `TCB/Sig.lean`); the contracts add the rest.
Everything else (keys, key contexts, associated data, texts and
synthetic IVs) is secret.

The associated data of SIV is a vector of strings (RFC 5297 §2.6; for
nonce-based encryption the nonce is its last component, §3), which S2V
absorbs one component at a time (§2.4):

* `vg_aes_siv_init` writes a key context (`KeyRepr`): the key schedule of
  `K1`, its CMAC subkeys and the key schedule of `K2`. The others read one,
  with its number of rounds, and compute with the CMAC and the cipher it
  holds (`ctxMac`, `ctxCiph`): with a context `vg_aes_siv_init` wrote, that
  is AES-SIV with its key (`ctxMac_eq`, `ctxCiph_eq`).
* `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` are the whole of
  `SIV-ENCRYPT` and `SIV-DECRYPT` (`encryptWith`, `decryptWith`) in one
  call: they take the vector of associated data as a list of slices
  (`Param.slices`, read by `components`), and run S2V over it themselves.
  `encrypt` encrypts the plaintext in place, writing the synthetic IV `V`
  to `siv`. `decrypt` decrypts the ciphertext in place with the synthetic IV
  it is given at `siv`, finishes S2V with the plaintext and compares, and if
  they differ overwrites the plaintext with zeros, so that it is never
  released.
  Whether `V` is right is public: `decrypt` may leak it (it is the result),
  and nothing else secret.

The functions check no length; the RFC limits the associated data to 126
components (§7), which the caller counts. `encrypt` writes the synthetic IV
to the 16 bytes at `siv`, and `decrypt` reads the received one from the 16
bytes at `siv`. The functions keep their working space on the stack. The
postconditions (and `decrypt`'s leak) are stated for `rounds` of 10, 12 or
14, which the preconditions require, so that they read only the buffers
(the round keys and subkeys in the key context for those rounds) and the
components of associated data.

Every contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see `Sig.contract`),
0 for one that uses none; the functions may overwrite their arguments passed
in memory, where the calling convention allows it (`writeArgs`), to pass
arguments to the functions they call.
-/

namespace VG.Spec.Siv

/-! ## The key context -/

/-- `vg_aes_siv_init(key: *const u8, key_len: usize, ctx: *mut [u64; 64])`. -/
def initSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 64)]

/-- `init`'s precondition: a key of 32, 48 or 64 bytes. -/
def initPre (pb : Nat) : Curry (initSig.words pb) (Mem → Prop) :=
  fun _key keyLen _ctx _ => keyLen.toNat = 32 ∨ keyLen.toNat = 48 ∨ keyLen.toNat = 64

/-- Makes the 512 bytes at `ctx` the key context (`KeyRepr`) of the key at
`key`. -/
def initPost (pb : Nat) : initSig.Post pb := fun key keyLen ctx m m' _ =>
  KeyRepr m' ctx (Aes.bytesAt m key keyLen.toNat)

/-- For a key of 32, 48 or 64 bytes at `key`: `initPost`. -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A (pre := initPre A.ptrBits) (post := initPost A.ptrBits) (writeArgs := true)
    (stack := stack)

/-- `vg_aes_siv_init` on every target. -/
def initApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_init"
  sig := initSig
  writeArgs := true
  contracts := some fun A stack => initContract A stack
  summary := "The AES-SIV key setup (RFC 5297 §2.6): writes the key context of the \
    `key_len`-byte key `K = K1 ‖ K2` at `key` (the halves of `key_len / 2` bytes) to `*ctx`: \
    the key schedule of `K1` for `Nr = key_len / 8 + 6` rounds (FIPS 197 §5.2, as \
    `vg_aes_expand_key` writes it) in the first `16 * (Nr + 1)` bytes, its CMAC subkeys \
    (NIST SP 800-38B §6.1) in bytes 240–271, and the key schedule of `K2` in the \
    `16 * (Nr + 1)` bytes from byte 272. The other bytes are unspecified. The other \
    `vg_aes_siv_*` functions read it, with `Nr` as their `rounds`.\n\n\
    Contract: `VG.Spec.Siv.initContract`. The key context is `VG.Spec.Siv.KeyRepr`. Constant \
    time: only the pointers and `key_len` may affect timing, not the key."
  safety := ["`key_len` must be 32, 48 or 64."]

/-! ## Encryption and decryption -/

/-- The components of associated data that the `n` descriptors at `p` list
in the memory `m`, on a target with `ptrBits`-bit pointers: the bytes of
each slice `Sig.listed` gives, in order. -/
def components (ptrBits : Nat) (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (Sig.listed ptrBits m .u8 p n).map fun r => Aes.bytesAt m r.base r.len

/-- `vg_aes_siv_encrypt(ctx: *const [u64; 64], rounds: usize, ads: *const [usize; 2], ads_count: usize, data: *mut u8, len: usize, siv: *mut [u8; 16])`.
`rounds` is public; `ads` lists the components of associated data, and `siv`
receives the synthetic IV. -/
def encryptSig : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("siv", .array true .u8 16)]

/-- `vg_aes_siv_encrypt`'s precondition: `rounds` is 10, 12 or 14. -/
def encryptPre (pb : Nat) : Curry (encryptSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _ads _adsCount _data _len _siv _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
components of associated data `ads` lists (`components`): the `len` bytes of
plaintext at `data` are encrypted (`encryptWith`), and the synthetic IV `V`
is the 16 bytes at `siv`. -/
def encryptPost (pb : Nat) : encryptSig.Post pb :=
  fun ctx rounds ads adsCount data len siv m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    encryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
        (components pb m ads adsCount.toNat) (Aes.bytesAt m data len.toNat) =
      (Aes.bytesAt m' siv 16, Aes.bytesAt m' data len.toNat)

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
components of associated data `ads` lists (`components`): encrypts the `len`
bytes of plaintext at `data` in place (`encryptWith`) and writes the
synthetic IV `V` to `siv`. -/
def encryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptSig.contract A (pre := encryptPre A.ptrBits) (post := encryptPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- `vg_aes_siv_encrypt` on every target. -/
def encryptApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_encrypt"
  sig := encryptSig
  writeArgs := true
  contracts := some fun A stack => encryptContract A stack
  summary := "AES-SIV encryption, `SIV-ENCRYPT` (RFC 5297 §2.6): with the key context `*ctx` \
    that `vg_aes_siv_init` wrote for `rounds` rounds, computes the synthetic IV \
    `V = S2V(K1, AD1, …, ADn, P)` of the `ads_count` components of associated data that \
    `ads` lists (each an address and a length, in bytes; for nonce-based encryption, §3, the \
    nonce is the last) and the `len` bytes of plaintext `P` at `data`, writes it to `*siv`, \
    and encrypts the plaintext in place with AES-CTR under `K2` from `V` with bits 31 and 63 \
    cleared. The RFC's output is `V` followed by the encrypted data.\n\n\
    Contract: `VG.Spec.Siv.encryptContract`. Constant time: only the pointers, `rounds`, \
    `ads_count`, `len` and where the components are (their addresses and lengths) may affect \
    timing, not the key context, the associated data or the plaintext."
  safety := ["`rounds` must be 10, 12 or 14."]

/-- `vg_aes_siv_decrypt(ctx: *const [u64; 64], rounds: usize, ads: *const [usize; 2], ads_count: usize, data: *mut u8, len: usize, siv: *const [u8; 16]) -> u32`.
`rounds` is public; `ads` lists the components of associated data, and `siv`
is the received synthetic IV. -/
def decryptSig : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("siv", .array false .u8 16)]
  ret := some .u32

/-- `vg_aes_siv_decrypt`'s precondition: `rounds` is 10, 12 or 14. -/
def decryptPre (pb : Nat) : Curry (decryptSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _ads _adsCount _data _len _siv _ =>
    rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, the
components of associated data `ads` lists and the received synthetic IV `V`
the 16 bytes at `siv`: if `V` is right for the plaintext of the `len` bytes
of ciphertext at `data` (`decryptWith`), the result is 1 and the plaintext is
at `data`; otherwise the result is 0 and zeros are at `data`. -/
def decryptPost (pb : Nat) : decryptSig.Post pb :=
  fun ctx rounds ads adsCount data len siv m m' r =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    match decryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
        (components pb m ads adsCount.toNat) (Aes.bytesAt m siv 16)
        (Aes.bytesAt m data len.toNat) with
    | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat

/-- What `vg_aes_siv_decrypt` may leak, for `rounds` of 10, 12 or 14: whether
it returns 1 (`decryptWith`'s outcome). -/
def decryptLeak (pb : Nat) : Curry (decryptSig.words pb) (Mem → List Nat) :=
  fun ctx rounds ads adsCount data len siv m =>
    if ¬(rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) then [] else
    [if (decryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
        (components pb m ads adsCount.toNat) (Aes.bytesAt m siv 16)
        (Aes.bytesAt m data len.toNat)).isSome
      then 1 else 0]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, the
components of associated data `ads` lists and the received synthetic IV `V`
the 16 bytes at `siv`: if `V` is right for the plaintext of the `len` bytes
of ciphertext at `data` (`decryptWith`), returns 1 and leaves the plaintext
at `data`; otherwise returns 0 and leaves zeros at `data`. May leak which
(`decryptWith`'s outcome). -/
def decryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptSig.contract A (pre := decryptPre A.ptrBits) (post := decryptPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (decryptLeak A.ptrBits))

/-- `vg_aes_siv_decrypt` on every target. -/
def decryptApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_decrypt"
  sig := decryptSig
  writeArgs := true
  contracts := some fun A stack => decryptContract A stack
  summary := "AES-SIV decryption, `SIV-DECRYPT` (RFC 5297 §2.7): with the key context `*ctx` \
    that `vg_aes_siv_init` wrote for `rounds` rounds and the received synthetic IV `V` at `siv`, \
    decrypts the `len` bytes of ciphertext at `data` in place with \
    AES-CTR under `K2` from `V` with bits 31 and 63 cleared, computes \
    `S2V(K1, AD1, …, ADn, P)` of the `ads_count` components of associated data that `ads` \
    lists (each an address and a length, in bytes) and the plaintext `P`, and returns 1 if it \
    is `V`; otherwise returns 0 and overwrites the `len` bytes at `data` with zeros. The IVs \
    are compared without a branch.\n\n\
    Contract: `VG.Spec.Siv.decryptContract`. Constant time but for the result: only the \
    pointers, `rounds`, `ads_count`, `len`, where the components are (their addresses and \
    lengths) and whether the function returns 1 or 0 may affect timing, not the key context, \
    the associated data, the data or `V`."
  safety := ["`rounds` must be 10, 12 or 14."]

end VG.Spec.Siv
