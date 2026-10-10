import VerifiedGarbage.Impl.Sha512.AArch64
import VerifiedGarbage.Impl.MdStream.AArch64

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

namespace VG.Impl.Sha512.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha512.AArch64 (movImm64 scratchBytes)
open VG.Impl.MdStream.AArch64 (Params len128 out64)

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k => movImm64 .x9 iv[k]! ++ ([.str .x .x9 .x0 (8 * k)] : List Instr))

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

end VG.Impl.Sha512.AArch64.Stream
