module

public import VerifiedGarbage.Spec.Gcm.Precomputed

/-!
# AES-GCM encryption out of place

**Trusted** (as every file in `Spec/`). Encryption that reads the plaintext
from buffers of its own and writes the ciphertext to another, so that a
caller holding the plaintext in buffers it does not own (a TLS record layer,
which must write `ciphertext ‖ tag` to an output buffer) need not first copy
it there to encrypt it in place:

* `vg_aes_gcm_seal_gather` is `vg_aes_gcm_seal` (`sealContract`) whose
  plaintext is the concatenation of a list of slices (`Param.slices`, read
  by `gathered`), as a vector of I/O buffers gives it: a record split into
  pieces, and TLS 1.3's content-type byte after it, are encrypted in one
  call, the ciphertext written to one buffer.
* `vg_aes_gcm_seal_gather_precomputed` is the same with a key context of
  `vg_aes_gcm_init_precomputed`, as the `_precomputed` functions of
  `Spec/Gcm/Precomputed.lean` are those without it.
* `vg_aes_gcm_open_to` is `vg_aes_gcm_open` (`openContract`) that reads the
  ciphertext from `src` and writes the plaintext to `dst`, so that a caller
  holding the ciphertext in a buffer it does not own (a TLS record layer
  reading a record) need not first copy it to decrypt it in place. If the tag
  is wrong it writes zeros to `dst` (where `vg_aes_gcm_open` leaves the data
  as it was), so that an implementation may decrypt into `dst` as it hashes
  `src`, and wipe what it wrote when the tag turns out wrong; it leaks what
  `vg_aes_gcm_open` leaks, whether the tag is right (`openToLeak`).
  `vg_aes_gcm_open_to_precomputed` is the same with a key context of
  `vg_aes_gcm_init_precomputed`.

The output and the input are different buffers: the signatures make the
output overlap no other buffer (`Sig.contract`), so it never overlaps the
input; a caller encrypting or decrypting in place calls the functions of
`Spec/Gcm/Contract.lean`. Each output has its own length argument, which the
preconditions require to be the length of the input. The other
arguments, what is public and what is secret, and the working space are
those of the functions they follow. Existing contracts are unchanged.
-/

@[expose] public section

namespace VG.Spec.Gcm

/-! ## One-shot, from a list of slices -/

/-- The bytes of the slices that the `n` descriptors at `p` list in the
memory `m`, on a target with `ptrBits`-bit pointers, concatenated in order
(`Sig.listed`). -/
def gathered (ptrBits : Nat) (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (Sig.listed ptrBits m .u8 p n).flatMap fun r => Aes.bytesAt m r.base r.len

/-- The total length of the slices that the `n` descriptors at `p` list in
the memory `m`: the length of `gathered`. -/
def gatheredLen (ptrBits : Nat) (m : Mem) (p : Addr) (n : Nat) : Nat :=
  ((Sig.listed ptrBits m .u8 p n).map (·.len)).sum

/-- `vg_aes_gcm_seal_gather(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const [usize; 2], src_count: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16])`.
`rounds` is public; `src` lists the pieces of the plaintext. -/
def sealGatherSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

/-- `vg_aes_gcm_seal_gather`'s precondition: `rounds` is 10, 12 or 14, and
the slices `src` lists are `len` bytes long in all. -/
def sealGatherPre (pb : Nat) : Curry (sealGatherSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat

/-- For every AES key `K` whose key context is at `ctx` with `rounds` rounds
(`KeyRounds`), and slices of `len` bytes in all listed by `src`: the `len`
bytes at `dst` are the encryption of their concatenation (`gathered`), with
the IV the `nonce_len` bytes at `nonce` and the `aad_len` bytes of additional
data at `aad` (GCM-AE under `K`, `aesGcmEncrypt`), and the 16-byte tag is at
`tag`. (`sealPost`, with the plaintext gathered from `src` and the ciphertext
written to `dst`.) -/
def sealGatherPost (pb : Nat) : sealGatherSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag m m' _ =>
    ∀ key, KeyRounds m ctx rounds.toNat key →
    gatheredLen pb m src srcCount.toNat = len.toNat →
    aesGcmEncrypt key 16 (Aes.bytesAt m nonce nonceLen.toNat) (gathered pb m src srcCount.toNat)
        (Aes.bytesAt m aad aadLen.toNat) =
      (Aes.bytesAt m' dst len.toNat, Aes.bytesAt m' tag 16)

/-- For `rounds` of 10, 12 or 14 and slices of `len` bytes in all
(`sealGatherPre`): `sealGatherPost`. -/
def sealGatherContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherSig.contract A (pre := sealGatherPre A.ptrBits) (post := sealGatherPost A.ptrBits)
    (writeArgs := true) (stack := stack)

/-- The documentation of the precondition on the slices `src` lists. -/
def gatherSafety : String :=
  "The slices `src` lists must be `len` bytes long in all."

/-- `vg_aes_gcm_seal_gather` on every target. -/
def sealGatherApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather"
  sig := sealGatherSig
  writeArgs := true
  contracts := some fun A stack => sealGatherContract A stack
  summary := "AES-GCM authenticated encryption (NIST SP 800-38D §7.1, GCM-AE, with a 128-bit \
    tag), out of place, of a plaintext in pieces: with the key context `*ctx` that \
    `vg_aes_gcm_init` wrote for `rounds` rounds, encrypts the concatenation of the \
    `src_count` slices that `src` lists (each an address and a length, in bytes), under the IV \
    the `nonce_len` bytes at `nonce`, writes the ciphertext to the `len` bytes at `dst`, and \
    writes the tag of the ciphertext and the `aad_len` bytes of additional data at `aad` to \
    `*tag`: `vg_aes_gcm_seal` with the plaintext gathered from `src`. A shorter tag is the \
    first bytes of this one.\n\n\
    The function checks no length. GCM is secure only for a nonce of 1 to `2^61 - 1` bytes, \
    at most `2^36 - 32` bytes of data and at most `2^61 - 1` bytes of additional data \
    (§5.2.1.1), which the caller must ensure; and a nonce must never be used twice with the \
    same key.\n\n\
    Contract: `VG.Spec.Gcm.sealGatherContract`. Constant time: only the pointers, `rounds`, \
    the lengths, `src_count` and where the slices are (their addresses and lengths) may \
    affect timing, not the key context, the nonce, the additional data or the data."
  safety := ["`rounds` must be 10, 12 or 14.", gatherSafety]

/-! ## With the powers of the hash subkey -/

/-- `vg_aes_gcm_seal_gather_precomputed(ctx: *const [u64; 128], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const [usize; 2], src_count: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16])`:
`sealGatherSig` with the larger key context. -/
def sealGatherPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16)]

/-- `sealGatherPre`, and the key context at `ctx` holds the powers of its
hash subkey. -/
def sealGatherPrecomputedPre (pb : Nat) :
    Curry (sealGatherPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen src srcCount _dst len _tag m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      gatheredLen pb m src srcCount.toNat = len.toNat ∧ PowersRepr m ctx

/-- `sealGatherContract`, with the larger key context. -/
def sealGatherPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPrecomputedSig.contract A (pre := sealGatherPrecomputedPre A.ptrBits)
    (post := sealGatherPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_precomputed` on every target. -/
def sealGatherPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_seal_gather_precomputed"
  sig := sealGatherPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => sealGatherPrecomputedContract A stack
  summary := "`vg_aes_gcm_seal_gather` with a key context of `vg_aes_gcm_init_precomputed`: \
    with the key context `*ctx` that `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, \
    does exactly what `vg_aes_gcm_seal_gather` does with its first 256 bytes (see \
    `vg_aes_gcm_seal_gather`), and may read the powers of the hash subkey that it holds \
    instead of computing them. Its constant-time guarantee is `vg_aes_gcm_seal_gather`'s, \
    the powers being as secret as the rest of the key context.\n\n\
    Contract: `VG.Spec.Gcm.sealGatherPrecomputedContract`."
  safety := sealGatherApi.safety ++ [powersSafety]

/-! ## Decryption out of place -/

/-- `vg_aes_gcm_open_to(ctx: *const [u64; 32], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const u8, len: usize, dst: *mut u8, dst_len: usize, tag: *const u8, tag_len: usize) -> u32`:
`openSig` with the ciphertext read from `src` and the plaintext written to
`dst`. `rounds` and `tag_len` are public. -/
def openToSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"),
    ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

/-- `vg_aes_gcm_open_to`'s precondition: `rounds` is 10, 12 or 14, and the
output is as long as the input. -/
def openToPre (pb : Nat) : Curry (openToSig.words pb) (Mem → Prop) :=
  fun _ctx rounds _nonce _nonceLen _aad _aadLen _src len _dst dstLen _tag _tagLen _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧ dstLen.toNat = len.toNat

/-- For every AES key `K` whose key context is at `ctx` with `rounds` rounds
(`KeyRounds`) and the received tag the `tag_len` bytes at `tag`: if `tag_len`
is a tag length `tagLenOk` allows and the tag is that of the `len` bytes of
ciphertext at `src` and the `aad_len` bytes of additional data at `aad`, with
the IV the `nonce_len` bytes at `nonce` (GCM-AD under `K`, `decryptWith`), the
result is 1 and the plaintext is the `len` bytes at `dst`; otherwise the
result is 0 and the `len` bytes at `dst` are zero. (`openPost`, with the
ciphertext read from `src` and the plaintext written to `dst`.) -/
def openToPost (pb : Nat) : openToSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src len dst _dstLen tag tagLen m m' r =>
    ∀ key, KeyRounds m ctx rounds.toNat key →
    match openResult (aes key) (aes key 0) tagLen.toNat
        (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m src len.toNat)
        (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m tag tagLen.toNat) with
    | some pt => r = 1 ∧ Aes.bytesAt m' dst len.toNat = pt
    | none => r = 0 ∧ Aes.bytesAt m' dst len.toNat = List.replicate len.toNat 0

/-- What `vg_aes_gcm_open_to` may leak, for `rounds` of 10, 12 or 14: whether
it returns 1 (`openResult`'s outcome on the ciphertext at `src`), as
`openLeak`. -/
def openToLeak (pb : Nat) : Curry (openToSig.words pb) (Mem → List Nat) :=
  fun ctx rounds nonce nonceLen aad aadLen src len _dst _dstLen tag tagLen m =>
    if ¬(rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) then [] else
    [if (openResult (ctxCiph m ctx rounds.toNat) (ctxH m ctx) tagLen.toNat
        (Aes.bytesAt m nonce nonceLen.toNat) (Aes.bytesAt m src len.toNat)
        (Aes.bytesAt m aad aadLen.toNat) (Aes.bytesAt m tag tagLen.toNat)).isSome
      then 1 else 0]

/-- For `rounds` of 10, 12 or 14 and an output as long as the input
(`openToPre`): `openToPost`. May leak whether the tag is right
(`openToLeak`). -/
def openToContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToSig.contract A (pre := openToPre A.ptrBits) (post := openToPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

/-- The documentation of the precondition on the output's length. -/
def openToSafety : String :=
  "`dst_len` must equal `len`."

/-- `vg_aes_gcm_open_to` on every target. -/
def openToApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_to"
  sig := openToSig
  writeArgs := true
  contracts := some fun A stack => openToContract A stack
  summary := "AES-GCM authenticated decryption (NIST SP 800-38D §7.2, GCM-AD), out of place: \
    with the key context `*ctx` that `vg_aes_gcm_init` wrote for `rounds` rounds and the \
    received tag the `tag_len` bytes at `tag`, returns 1 if `tag_len` is between 4 and 16 \
    and the tag is the first `tag_len` bytes of that of the `len` bytes of ciphertext at \
    `src` and the `aad_len` bytes of additional data at `aad`, under the IV the `nonce_len` \
    bytes at `nonce`, having then written the plaintext to the `dst_len = len` bytes at \
    `dst`; otherwise returns 0, having written zeros to them: `vg_aes_gcm_open` with the \
    ciphertext read from `src` and the plaintext written to `dst`. `src` is not written, \
    and `dst` is a buffer of its own: it overlaps no other buffer, `src` included. The \
    tags are compared without a branch.\n\n\
    The function checks no other length: GCM requires a nonce of 1 to `2^61 - 1` bytes, at \
    most `2^36 - 32` bytes of ciphertext and at most `2^61 - 1` bytes of additional data \
    (§5.2.1.1), which the caller must check.\n\n\
    Contract: `VG.Spec.Gcm.openToContract`. Constant time but for the result: only the \
    pointers, `rounds`, the lengths, `tag_len` and whether the function returns 1 or 0 may \
    affect timing, not the key context, the nonce, the additional data, the data or the tag."
  safety := ["`rounds` must be 10, 12 or 14.", openToSafety]

/-- `vg_aes_gcm_open_to_precomputed(ctx: *const [u64; 128], rounds: usize, nonce: *const u8, nonce_len: usize, aad: *const u8, aad_len: usize, src: *const u8, len: usize, dst: *mut u8, dst_len: usize, tag: *const u8, tag_len: usize) -> u32`:
`openToSig` with the larger key context. -/
def openToPrecomputedSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slice false .u8 "len"), ("dst", .slice true .u8 "dst_len"),
    ("tag", .slice false .u8 "tag_len")]
  ret := some .u32

/-- `openToPre`, and the key context at `ctx` holds the powers of its hash
subkey. -/
def openToPrecomputedPre (pb : Nat) : Curry (openToPrecomputedSig.words pb) (Mem → Prop) :=
  fun ctx rounds _nonce _nonceLen _aad _aadLen _src len _dst dstLen _tag _tagLen m =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) ∧
      dstLen.toNat = len.toNat ∧ PowersRepr m ctx

/-- `openToContract`, with the larger key context; it may leak what
`openToContract` may (`openToLeak`). -/
def openToPrecomputedContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToPrecomputedSig.contract A (pre := openToPrecomputedPre A.ptrBits)
    (post := openToPost A.ptrBits)
    (writeArgs := true) (stack := stack) (leak := some (openToLeak A.ptrBits))

/-- `vg_aes_gcm_open_to_precomputed` on every target. -/
def openToPrecomputedApi : Api where
  module := "gcm"
  name := "vg_aes_gcm_open_to_precomputed"
  sig := openToPrecomputedSig
  writeArgs := true
  contracts := some fun A stack => openToPrecomputedContract A stack
  summary := "`vg_aes_gcm_open_to` with a key context of `vg_aes_gcm_init_precomputed`: with \
    the key context `*ctx` that `vg_aes_gcm_init_precomputed` wrote for `rounds` rounds, does \
    exactly what `vg_aes_gcm_open_to` does with its first 256 bytes (see \
    `vg_aes_gcm_open_to`), and may read the powers of the hash subkey that it holds instead \
    of computing them. Its constant-time guarantee is `vg_aes_gcm_open_to`'s, the powers \
    being as secret as the rest of the key context.\n\n\
    Contract: `VG.Spec.Gcm.openToPrecomputedContract`."
  safety := openToApi.safety ++ [powersSafety]

end VG.Spec.Gcm
