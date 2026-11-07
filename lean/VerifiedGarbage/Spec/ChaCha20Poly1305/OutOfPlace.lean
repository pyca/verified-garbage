module
public import VerifiedGarbage.Spec.ChaCha20Poly1305
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 encryption and decryption out of place

**Trusted** (as every file in `Spec/`). `vg_chacha20_poly1305_seal_gather`
is `vg_chacha20_poly1305_seal` (`sealContract`) whose plaintext is the
concatenation of a list of slices (`Param.slices`, read by `gathered`), as
a vector of I/O buffers gives it, and whose ciphertext is written to a
buffer of its own: a caller holding the plaintext in buffers it does not own
(a TLS record layer, which must write `ciphertext ‖ tag` to an output
buffer) encrypts a record split into pieces, and TLS 1.3's content-type byte
after it, in one call, without first copying them there to encrypt them in
place.

The output and the input are different buffers: the signature makes the
output overlap no other buffer (`Sig.contract`), so it never overlaps the
input; a caller encrypting in place calls `vg_chacha20_poly1305_seal`. Unlike
`sealContract`, the contract requires the plaintext to be at most RFC
8439's `P_MAX` long (2³² − 1 blocks of 64 bytes), which the caller must
enforce for the construction to be secure anyway: the block counter never
wraps around. The key, the nonce, the additional data, the data and the tag
are secret; the pointers, the lengths, the number of slices and where they
are (their addresses and lengths) are public.

`vg_chacha20_poly1305_open_to` is `vg_chacha20_poly1305_open`
(`openZeroContract`) that reads the ciphertext from `src` and writes the
plaintext to `dst`, so that a caller holding the ciphertext in a buffer it
does not own (a TLS record layer reading a record) need not first copy it to
decrypt it in place. As `openZeroContract`, it writes zeros to `dst` if the
tag is wrong, so that an implementation may decrypt into `dst` as it
authenticates `src`, and wipe what it wrote when the tag turns out wrong;
and it leaks what `vg_chacha20_poly1305_open` leaks, whether the tag is
right (`openToLeak`). `dst` overlaps no other buffer, `src` included; `dst`
has a length argument of its own, which the precondition requires to be
`len`, and, as `sealGatherContract`, it requires the ciphertext to be at
most `P_MAX` long.
-/

@[expose] public section

namespace VG.Spec.ChaCha20Poly1305

open Poly1305 (bytesAt)

/-- RFC 8439's `P_MAX` (§2.8): the longest plaintext, 2³² − 1 blocks of 64
bytes, as the block counter starts at 1. -/
def pMax : Nat := 64 * (2 ^ 32 - 1)

/-- The bytes of the slices that the `n` descriptors at `p` list in the
memory `m`, on a target with `ptrBits`-bit pointers, concatenated in order
(`Sig.listed`). -/
def gathered (ptrBits : Nat) (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (Sig.listed ptrBits m .u8 p n).flatMap fun r => bytesAt m r.base r.len

/-- The total length of the slices that the `n` descriptors at `p` list in
the memory `m`: the length of `gathered`. -/
def gatheredLen (ptrBits : Nat) (m : Mem) (p : Addr) (n : Nat) : Nat :=
  ((Sig.listed ptrBits m .u8 p n).map (·.len)).sum

/-- `vg_chacha20_poly1305_seal_gather(key: *const [u8; 32], nonce: *const [u8; 12], aad: *const u8, aad_len: usize, src: *const [usize; 2], src_count: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16])`.
`src` lists the pieces of the plaintext. -/
def sealGatherSig : Sig where
  params := [("key", .array false .u8 32), ("nonce", .array false .u8 12),
    ("aad", .slice false .u8 "aad_len"), ("src", .slices .u8 "src_count"),
    ("dst", .slice true .u8 "len"), ("tag", .array true .u8 16)]

/-- The slices `src` lists are `len` bytes long in all, and at most
`P_MAX`. -/
def sealGatherPre (pb : Nat) : Curry (sealGatherSig.words pb) (Mem → Prop) :=
  fun _key _nonce _aad _aadLen src srcCount _dst len _tag m =>
    gatheredLen pb m src srcCount.toNat = len.toNat ∧ len.toNat ≤ pMax

/-- With the key at `key` and the nonce at `nonce`, and slices of `len`
bytes in all (at most `P_MAX`) listed by `src`: the `len` bytes at `dst`
are the encryption of their concatenation (`gathered`), for the `aad_len`
bytes of additional data at `aad`, and the tag is at `tag`. (`sealPost`,
with the plaintext gathered from `src` and the ciphertext written to
`dst`.) -/
def sealGatherPost (pb : Nat) : sealGatherSig.Post pb :=
  fun key nonce aad aadLen src srcCount dst len tag m m' _ =>
    gatheredLen pb m src srcCount.toNat = len.toNat → len.toNat ≤ pMax →
    encrypt (bytesAt m key 32) (bytesAt m nonce 12) (bytesAt m aad aadLen.toNat)
        (gathered pb m src srcCount.toNat) =
      (bytesAt m' dst len.toNat, bytesAt m' tag 16)

/-- For slices of `len` bytes in all, at most `P_MAX` (`sealGatherPre`):
`sealGatherPost`. -/
def sealGatherContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherSig.contract A (pre := sealGatherPre A.ptrBits) (post := sealGatherPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

/-- `vg_chacha20_poly1305_seal_gather` on every target. -/
def sealGatherApi : Api where
  module := "chacha20poly1305"
  name := "vg_chacha20_poly1305_seal_gather"
  sig := sealGatherSig
  writeArgs := true
  contracts := some fun A stack => sealGatherContract A stack
  summary := "ChaCha20-Poly1305 encryption (RFC 8439 §2.8), out of place, of a plaintext in \
    pieces: with the key `*key` and the nonce `*nonce`, encrypts the concatenation of the \
    `src_count` slices that `src` lists (each an address and a length, in bytes), writes the \
    ciphertext to the `len` bytes at `dst`, and writes the tag of the ciphertext and the \
    `aad_len` bytes of additional data at `aad` to `*tag`: `vg_chacha20_poly1305_seal` with the \
    plaintext gathered from `src`.\n\n\
    Contract: `VG.Spec.ChaCha20Poly1305.sealGatherContract`. Constant time: only the pointers, \
    the lengths, `src_count` and where the slices are (their addresses and lengths) may affect \
    timing, not the key, the nonce, the additional data or the data."
  safety := [
    "The slices `src` lists must be `len` bytes long in all.",
    "`len` must be at most `P_MAX`, 2³² − 1 blocks of 64 bytes (RFC 8439 §2.8)."]

/-! ## Decryption out of place -/

/-- `vg_chacha20_poly1305_open_to(key: *const [u8; 32], nonce: *const [u8; 12], aad: *const u8, aad_len: usize, src: *const u8, len: usize, dst: *mut u8, dst_len: usize, tag: *const [u8; 16]) -> u32`:
`openSig` with the ciphertext read from `src` and the plaintext written to
`dst`. -/
def openToSig : Sig where
  params := [("key", .array false .u8 32), ("nonce", .array false .u8 12),
    ("aad", .slice false .u8 "aad_len"), ("src", .slice false .u8 "len"),
    ("dst", .slice true .u8 "dst_len"), ("tag", .array false .u8 16)]
  ret := some .u32

/-- The output is as long as the input, which is at most `P_MAX`. -/
def openToPre (pb : Nat) : Curry (openToSig.words pb) (Mem → Prop) :=
  fun _key _nonce _aad _aadLen _src len _dst dstLen _tag _ =>
    dstLen.toNat = len.toNat ∧ len.toNat ≤ pMax

/-- With the key at `key`, the nonce at `nonce` and the received tag at
`tag`: if the message (the `len` bytes of ciphertext at `src`, with the
`aad_len` bytes of additional data at `aad`) is authenticated, the result is
1 and the plaintext is the `len` bytes at `dst`; otherwise the result is 0,
and the `len` bytes at `dst` are zeros. (`openZeroPost`, with the ciphertext
read from `src` and the plaintext written to `dst`.) -/
def openToPost (pb : Nat) : openToSig.Post pb :=
  fun key nonce aad aadLen src len dst _dstLen tag m m' r =>
    match decrypt (bytesAt m key 32) (bytesAt m nonce 12) (bytesAt m aad aadLen.toNat)
        (bytesAt m src len.toNat) (bytesAt m tag 16) with
    | some pt => r = 1 ∧ bytesAt m' dst len.toNat = pt
    | none => r = 0 ∧ bytesAt m' dst len.toNat = List.replicate len.toNat 0

/-- What `vg_chacha20_poly1305_open_to` may leak: whether it returns 1
(`decrypt`'s outcome on the ciphertext at `src`), as `openLeak`. -/
def openToLeak (pb : Nat) : Curry (openToSig.words pb) (Mem → List Nat) :=
  fun key nonce aad aadLen src len _dst _dstLen tag m =>
    [if (decrypt (bytesAt m key 32) (bytesAt m nonce 12) (bytesAt m aad aadLen.toNat)
        (bytesAt m src len.toNat) (bytesAt m tag 16)).isSome then 1 else 0]

/-- For an output as long as the input, at most `P_MAX` (`openToPre`):
`openToPost`. May leak whether the tag is right (`openToLeak`). -/
def openToContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openToSig.contract A (pre := openToPre A.ptrBits) (post := openToPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)
    (leak := some (openToLeak A.ptrBits))

/-- `vg_chacha20_poly1305_open_to` on every target. -/
def openToApi : Api where
  module := "chacha20poly1305"
  name := "vg_chacha20_poly1305_open_to"
  sig := openToSig
  writeArgs := true
  contracts := some fun A stack => openToContract A stack
  summary := "ChaCha20-Poly1305 decryption (RFC 8439 §2.8), out of place: with the key `*key`, \
    the nonce `*nonce` and the received tag `*tag`, returns 1 if the tag is that of the `len` \
    bytes of ciphertext at `src` and the `aad_len` bytes of additional data at `aad`, having \
    then written the plaintext to the `dst_len = len` bytes at `dst`; otherwise returns 0, \
    having written zeros to them: `vg_chacha20_poly1305_open` with the ciphertext read from \
    `src` and the plaintext written to `dst`. `src` is not written, and `dst` is a buffer of \
    its own: it overlaps no other buffer, `src` included. The tags are compared without a \
    branch.\n\n\
    Contract: `VG.Spec.ChaCha20Poly1305.openToContract`. Constant time but for the result: \
    only the pointers, the lengths and whether the function returns 1 or 0 may affect timing, \
    not the key, the nonce, the additional data, the tag or the data."
  safety := [
    "`dst_len` must equal `len`.",
    "`len` must be at most `P_MAX`, 2³² − 1 blocks of 64 bytes (RFC 8439 §2.8)."]

end VG.Spec.ChaCha20Poly1305
