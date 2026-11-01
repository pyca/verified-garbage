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

The output and the input are different buffers: the signatures make the
output overlap no other buffer (`Sig.contract`), so it never overlaps the
input; a caller encrypting in place calls the functions of
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

/-- For `rounds` of 10, 12 or 14, with the key context at `ctx`, and slices
of `len` bytes in all listed by `src`: the `len` bytes at `dst` are the
encryption of their concatenation (`gathered`), with the IV the `nonce_len`
bytes at `nonce` and the `aad_len` bytes of additional data at `aad`
(GCM-AE, `encryptWith`), and the 16-byte tag is at `tag`. (`sealPost`, with
the plaintext gathered from `src` and the ciphertext written to `dst`.) -/
def sealGatherPost (pb : Nat) : sealGatherSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag m m' _ =>
    (rounds.toNat = 10 ∨ rounds.toNat = 12 ∨ rounds.toNat = 14) →
    gatheredLen pb m src srcCount.toNat = len.toNat →
    encryptWith (ctxCiph m ctx rounds.toNat) (ctxH m ctx) 16 (Aes.bytesAt m nonce nonceLen.toNat)
        (gathered pb m src srcCount.toNat) (Aes.bytesAt m aad aadLen.toNat) =
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

end VG.Spec.Gcm
