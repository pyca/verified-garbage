module

public import VerifiedGarbage.Spec.ChaCha20Poly1305
public import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20-Poly1305: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`vg_chacha20_poly1305_seal_split` is `vg_chacha20_poly1305_seal` on the data
in `dst` whose first `src_len` bytes are read from `src` instead: the first
slice of a gathered plaintext encrypted out of place, the rest (a TLS
record's content type) already copied after it in place, with no copy of
the first slice. Its output overlaps no other buffer, and, as `seal`'s, its
contract does not limit the length of the data; its input from `src` is at
most as long as its output. The key, the nonce, the additional data, the
data and the tag are secret; the pointers and the lengths are public.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305

open VG.Spec VG.Spec.ChaCha20Poly1305
open VG.Spec.Poly1305 (bytesAt)

/-- `vg_chacha20_poly1305_seal_split(key: *const [u8; 32], nonce: *const [u8; 12], aad: *const u8, aad_len: usize, src: *const u8, src_len: usize, dst: *mut u8, len: usize, tag: *mut [u8; 16])`. -/
def sealSplitSig : Sig where
  params := [("key", .array false .u8 32), ("nonce", .array false .u8 12),
    ("aad", .slice false .u8 "aad_len"), ("src", .slice false .u8 "src_len"),
    ("dst", .slice true .u8 "len"), ("tag", .array true .u8 16)]

/-- The input from `src` is at most as long as the output. -/
def sealSplitPre (pb : Nat) : Curry (sealSplitSig.words pb) (Mem → Prop) :=
  fun _key _nonce _aad _aadLen _src srcLen _dst len _tag _ => srcLen.toNat ≤ len.toNat

/-- With the key at `key` and the nonce at `nonce`, and an input from `src`
at most as long as the output: the `len` bytes at `dst` are the encryption of
the `src_len` bytes at `src` followed by the bytes at `dst` from `src_len`
on, for the `aad_len` bytes of additional data at `aad`, and the tag is at
`tag`. (`sealPost`, with the data's first `src_len` bytes read from `src`.) -/
def sealSplitPost (pb : Nat) : sealSplitSig.Post pb :=
  fun key nonce aad aadLen src srcLen dst len tag m m' _ =>
    srcLen.toNat ≤ len.toNat →
    encrypt (bytesAt m key 32) (bytesAt m nonce 12) (bytesAt m aad aadLen.toNat)
        (bytesAt m src srcLen.toNat ++ (bytesAt m dst len.toNat).drop srcLen.toNat) =
      (bytesAt m' dst len.toNat, bytesAt m' tag 16)

/-- For an input from `src` at most as long as the output (`sealSplitPre`):
`sealSplitPost`. -/
def sealSplitContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealSplitSig.contract A (pre := sealSplitPre A.ptrBits) (post := sealSplitPost A.ptrBits)
    (writeArgs := true)
    (stack := stack)

end VG.Proof.ChaCha20Poly1305
