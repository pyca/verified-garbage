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
  `encrypt` encrypts the plaintext in place, writing the synthetic IV `V`.
  `decrypt` decrypts the ciphertext in place with the synthetic IV it is
  given, finishes S2V with the plaintext and compares, and if they differ
  overwrites the plaintext with zeros, so that it is never released.
  Whether `V` is right is public: `decrypt` may leak it (it is the result),
  and nothing else secret.

The functions check no length; the RFC limits the associated data to 126
components (§7), which the caller counts. The synthetic IV travels in the
first 16 bytes of `work`, which is also working space, so that fewer
arguments are passed in memory. Each function's working space (`scratch` or
`work`) has room for `vg_aes_ctr32`'s (2048 bytes) and 512 bytes more, and
`encrypt`'s and `decrypt`'s 16 more, for S2V's state.

Every contract takes the number of bytes of stack below the stack pointer
that an implementation's calls and frames use (`stack`, see `Sig.contract`),
0 for one that uses none; the functions may overwrite their arguments passed
in memory, where the calling convention allows it (`writeArgs`), to pass
arguments to the functions they call.
-/

namespace VG.Spec.Siv

/-! ## The key context -/

/-- `vg_aes_siv_init(key: *const u8, key_len: usize, ctx: *mut [u64; 64], scratch: *mut [u64; 320])`.
`scratch` is working space. -/
def initSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 64),
    ("scratch", .array true .u64 320)]

/-- For a key of 32, 48 or 64 bytes at `key`, makes the 512 bytes at `ctx`
its key context (`KeyRepr`). -/
def initContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initSig.contract A
    (pre := fun _key keyLen _ctx _scratch _ =>
      keyLen.toNat = 32 ∨ keyLen.toNat = 48 ∨ keyLen.toNat = 64)
    (post := fun key keyLen ctx _scratch m m' _ => KeyRepr m' ctx (Aes.bytesAt m key keyLen.toNat))
    (writeArgs := true)
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
  safety := [
    "`key_len` must be 32, 48 or 64.",
    "The contents of `scratch` on return are unspecified."]

/-! ## Encryption and decryption -/

/-- The components of associated data that the `n` descriptors at `p` list
in the memory `m`, on a target with `ptrBits`-bit pointers: the bytes of
each slice `Sig.listed` gives, in order. -/
def components (ptrBits : Nat) (m : Mem) (p : Addr) (n : Nat) : List (List Byte) :=
  (Sig.listed ptrBits m .u8 p n).map fun r => Aes.bytesAt m r.base r.len

/-- `vg_aes_siv_encrypt(ctx: *const [u64; 64], rounds: usize, ads: *const [usize; 2], ads_count: usize, data: *mut u8, len: usize, work: *mut [u64; 322])`,
and `vg_aes_siv_decrypt` with the same parameters, returning a `u32`.
`rounds` is public; `ads` lists the components of associated data; `work`
is working space but for the synthetic IV, with room for that of
`seal` and `open` and S2V's state besides. -/
def encryptSig : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("work", .array true .u64 322)]

/-- `vg_aes_siv_decrypt`'s signature: `vg_aes_siv_encrypt`'s, returning a `u32`. -/
def decryptSig : Sig := { encryptSig with ret := some .u32 }

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx` and the
components of associated data `ads` lists (`components`): encrypts the `len`
bytes of plaintext at `data` in place (`encryptWith`) and writes the
synthetic IV `V` to the first 16 bytes of `work`. -/
def encryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptSig.contract A
    (pre := fun _ctx rounds _ads _adsCount _data _len _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds ads adsCount data len work m m' _ =>
      encryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
          (components A.ptrBits m ads adsCount.toNat) (Aes.bytesAt m data len.toNat) =
        (Aes.bytesAt m' work 16, Aes.bytesAt m' data len.toNat))
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
    nonce is the last) and the `len` bytes of plaintext `P` at `data`, writes it to the first \
    16 bytes of `*work`, and encrypts the plaintext in place with AES-CTR under `K2` from `V` \
    with bits 31 and 63 cleared. The RFC's output is `V` followed by the encrypted data. The \
    rest of `*work` is working space, unspecified on return.\n\n\
    Contract: `VG.Spec.Siv.encryptContract`. Constant time: only the pointers, `rounds`, \
    `ads_count`, `len` and where the components are (their addresses and lengths) may affect \
    timing, not the key context, the associated data or the plaintext."
  safety := ["`rounds` must be 10, 12 or 14."]

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, the
components of associated data `ads` lists and the received synthetic IV `V`
in the first 16 bytes of `work`: if `V` is right for the plaintext of the
`len` bytes of ciphertext at `data` (`decryptWith`), returns 1 and leaves the
plaintext at `data`; otherwise returns 0 and leaves zeros at `data`. May leak
which (`decryptWith`'s outcome). -/
def decryptContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptSig.contract A
    (pre := fun _ctx rounds _ads _adsCount _data _len _work _ =>
      rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14)
    (post := fun ctx rounds ads adsCount data len work m m' r =>
      match decryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
          (components A.ptrBits m ads adsCount.toNat) (Aes.bytesAt m work 16)
          (Aes.bytesAt m data len.toNat) with
      | some pt => r = 1 ∧ Aes.bytesAt m' data len.toNat = pt
      | none => r = 0 ∧ Aes.bytesAt m' data len.toNat = zeros len.toNat)
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ctx rounds ads adsCount data len work m =>
      [if (decryptWith (ctxMac m ctx rounds.toNat) (ctxCiph m ctx rounds.toNat)
          (components A.ptrBits m ads adsCount.toNat) (Aes.bytesAt m work 16)
          (Aes.bytesAt m data len.toNat)).isSome
        then 1 else 0])

/-- `vg_aes_siv_decrypt` on every target. -/
def decryptApi : Api where
  module := "aes_siv"
  name := "vg_aes_siv_decrypt"
  sig := decryptSig
  writeArgs := true
  contracts := some fun A stack => decryptContract A stack
  summary := "AES-SIV decryption, `SIV-DECRYPT` (RFC 5297 §2.7): with the key context `*ctx` \
    that `vg_aes_siv_init` wrote for `rounds` rounds and the received synthetic IV `V` in the \
    first 16 bytes of `*work`, decrypts the `len` bytes of ciphertext at `data` in place with \
    AES-CTR under `K2` from `V` with bits 31 and 63 cleared, computes \
    `S2V(K1, AD1, …, ADn, P)` of the `ads_count` components of associated data that `ads` \
    lists (each an address and a length, in bytes) and the plaintext `P`, and returns 1 if it \
    is `V`; otherwise returns 0 and overwrites the `len` bytes at `data` with zeros. The rest \
    of `*work` is working space, unspecified on return. The IVs are compared without a \
    branch.\n\n\
    Contract: `VG.Spec.Siv.decryptContract`. Constant time but for the result: only the \
    pointers, `rounds`, `ads_count`, `len`, where the components are (their addresses and \
    lengths) and whether the function returns 1 or 0 may affect timing, not the key context, \
    the associated data, the data or `V`."
  safety := ["`rounds` must be 10, 12 or 14."]

end VG.Spec.Siv
