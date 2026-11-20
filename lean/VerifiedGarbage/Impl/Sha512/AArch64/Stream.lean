module

public import VerifiedGarbage.Impl.Sha512.AArch64
public import VerifiedGarbage.Impl.MdStream.AArch64
public import VerifiedGarbage.Impl.Residue.AArch64.Writes
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Impl.MdStream.AArch64.OneShot
public import VerifiedGarbage.Impl.Residue.AArch64.Union

/-!
# Streaming SHA-512: AArch64 implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`).

* `init iv (state = x0)` stores the initial hash value `iv`.
* `update(state = x0, count = x1, data = x2, len = x3, scratch = x4)` and
  `finalize(state = x0, count = x1, out = x2, scratch = x3)` are the generic
  streaming code of `Impl/MdStream/AArch64.lean`, calling the compression
  function with the suffix `suffix` (`vg_sha512_compress` or
  `vg_sha512_compress_sha3`, `compressName`), and are emitted once for each
  implementation (`Generic/MdHash/AArch64/Stream.lean`). It is called with
  `scratch[0..scratchBytes)` as its scratch space; our caller's callee-saved
  registers are saved in the 48 bytes after it. The length field is the length in bits as
  a 128-bit big-endian integer: `count >> 61`, then `count << 3` (modulo
  2⁶⁴); the words of the final hash value are big-endian.
-/

@[expose] public section

namespace VG.Impl.Sha512.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha512.AArch64 (movImm64 scratchBytes)
open VG.Impl.MdStream.AArch64 (Params len128 out64)

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k => movImm64 .x9 iv[k]! ++ ([.str .x .x9 .x0 (8 * k)] : List Instr))

/-- `init`, storing the hash value sixteen bytes at a time (`stp`), at the
offsets the compression functions load it from: for the one-shot digests,
whose first compression reads it right away. -/
def initPairs (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 4).flatMap fun k =>
    movImm64 .x9 iv[2 * k]! ++ movImm64 .x10 iv[2 * k + 1]! ++ ([.stp .x9 .x10 .x0 (16 * k)] : List Instr))

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 64
  B := 128
  L := 16
  so := scratchBytes
  -- The length field, at `N + B - L`.
  len := len128 176
  out := out64 8

/-- The symbol of the compression function with the suffix `suffix`. -/
def compressName (suffix : String) : String := "vg_sha512_compress" ++ suffix

/-- `update`, calling the compression function `code` with the suffix `suffix`. -/
def updateWith (suffix : String) (code : Prog isa) : Prog isa :=
  MdStream.AArch64.update params (compressName suffix) code

/-- `finalize`, calling the compression function `code` with the suffix `suffix`. -/
def finalizeWith (suffix : String) (code : Prog isa) : Prog isa :=
  MdStream.AArch64.finalize params (compressName suffix) code

/-! ## The truncated digests

SHA-384, SHA-512/256 and SHA-512/224 output the first 48, 32 and 28 bytes of
the final hash value: `params` with a digest of 6 or 4 words, or of 3 words
and the high half of the fourth (`outHi`). -/

/-- The high half of word `k` of the hash value at `x19`, big-endian, written
to `x21 + 8 k`. -/
def outHi (k : Nat) : List Instr :=
  [.ldr .w .x9 .x19 (8 * k + 4), .rev32 .x9 .x9, .str .w .x9 .x21 (8 * k)]

def params384 : Params := { params with out := out64 6 }
def params512_256 : Params := { params with out := out64 4 }
def params512_224 : Params := { params with out := out64 3 ++ outHi 3 }

/-- `finalizeWith`, writing the digest `P.out` writes (`params384`, …). -/
def finalizeDigestWith (P : Params) (suffix : String) (code : Prog isa) : Prog isa :=
  MdStream.AArch64.finalize P (compressName suffix) code

/-- An implementation of the compression function for a function that hashes
to call: its code, the suffix of its name (`compressName`) and of the
streaming functions made with it, and the registers its code writes, of
those the calling convention does not preserve: what a function that calls
it clears for it before returning, with those its own instructions write
(the proofs hold it to the code, `Proof.Sha512.AArch64.Compress.scrub`). -/
structure Compress where
  code : Prog isa
  suffix : String
  clear : Impl.Residue.AArch64.Clear

/-! ## The functions, as emitted

Each streaming function over a compression function is its code with its
working space in a frame on the stack, then its cleanup
(`Impl.Residue.AArch64.scrubOf`), which clears the registers the code may
write, the compression function's included, and zeroes that stack, so that it
returns without secret residue. -/

namespace Fn

open VG.Impl.Residue.AArch64 (scrubOf)
open VG.Impl.StackScratch.AArch64 (withStackScratch)

/-- `vg_sha512_update` over the compression function `code`, its working space in a frame of its own. -/
def update (suffix : String) (code : Prog isa) : Prog isa :=
  scrubOf (16 + 688) 0 (withStackScratch 688 .x4 (updateWith suffix code))

/-- `vg_sha512_finalize` over the compression function `code`, its working space in a frame of its own. -/
def finalize (suffix : String) (code : Prog isa) : Prog isa :=
  scrubOf (16 + 688) 0 (withStackScratch 688 .x3 (finalizeWith suffix code))

/-- `vg_sha512_digest`, the one-shot digest over the compression function `code`, in its frame. -/
def digest512 (suffix : String) (code : Prog isa) : Prog isa :=
  scrubOf (MdStream.AArch64.OneShot.frameBytes params) 0
    (MdStream.AArch64.OneShot.digest { params with out := out64 8 } (initPairs Spec.Sha512.H0_512) (compressName suffix) code)

/-- `vg_sha384_finalize` over the compression function `code`, its working space in a frame of its own. -/
def finalize384 (suffix : String) (code : Prog isa) : Prog isa :=
  scrubOf (16 + 688) 0 (withStackScratch 688 .x3 (finalizeDigestWith params384 suffix code))

/-- `vg_sha384_digest`, the one-shot digest over the compression function `code`, in its frame. -/
def digest384 (suffix : String) (code : Prog isa) : Prog isa :=
  scrubOf (MdStream.AArch64.OneShot.frameBytes params) 0
    (MdStream.AArch64.OneShot.digest { params with out := out64 6 } (initPairs Spec.Sha512.H0_384) (compressName suffix) code)

/-- `vg_sha512_256_finalize` over the compression function `code`, its working space in a frame of its own. -/
def finalize512_256 (suffix : String) (code : Prog isa) : Prog isa :=
  scrubOf (16 + 688) 0 (withStackScratch 688 .x3 (finalizeDigestWith params512_256 suffix code))

/-- `vg_sha512_256_digest`, the one-shot digest over the compression function `code`, in its frame. -/
def digest512_256 (suffix : String) (code : Prog isa) : Prog isa :=
  scrubOf (MdStream.AArch64.OneShot.frameBytes params) 0
    (MdStream.AArch64.OneShot.digest { params with out := out64 4 } (initPairs Spec.Sha512.H0_512_256) (compressName suffix) code)

/-- `vg_sha512_224_finalize` over the compression function `code`, its working space in a frame of its own. -/
def finalize512_224 (suffix : String) (code : Prog isa) : Prog isa :=
  scrubOf (16 + 688) 0 (withStackScratch 688 .x3 (finalizeDigestWith params512_224 suffix code))

/-- `vg_sha512_224_digest`, the one-shot digest over the compression function `code`, in its frame. -/
def digest512_224 (suffix : String) (code : Prog isa) : Prog isa :=
  scrubOf (MdStream.AArch64.OneShot.frameBytes params) 0
    (MdStream.AArch64.OneShot.digest { params with out := out64 3 ++ outHi 3 } (initPairs Spec.Sha512.H0_512_224) (compressName suffix) code)

end Fn

end VG.Impl.Sha512.AArch64.Stream
