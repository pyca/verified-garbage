import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract

/-!
# ChaCha20-Poly1305 encryption out of place

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
are (their addresses and lengths) are public. Existing contracts are
unchanged.
-/

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

end VG.Spec.ChaCha20Poly1305
