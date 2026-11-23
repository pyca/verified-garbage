module

public import VerifiedGarbage.Impl.Sha512.Arm
public import VerifiedGarbage.Impl.MdStream.Arm
public import VerifiedGarbage.Impl.MdStream.Arm.Digest
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# Streaming SHA-512: 32-bit ARM implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`); each 64-bit word of the hash
value is stored little-endian, so as its low half followed by its high half.

* `init iv (state = r0)` stores the initial hash value `iv`.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/Arm.lean`), calling the compression function
  (`vg_sha512_compress`) with `scratch[0..224)` as its scratch space, and
  saving our caller's `r4`–`r11` and `lr` in `scratch[224..260)`. The length
  field is the length in bits as a 128-bit big-endian integer: `count >> 61`,
  then `count << 3` (modulo 2⁶⁴); the words of the final hash value are
  big-endian.
-/

@[expose] public section

namespace VG.Impl.Sha512.Arm.Stream

open VG.Arm
open VG.Impl.Sha512.Arm (compress lo hi)
open VG.Impl.MdStream.Arm (Params len64)

/-- Store word `k` of `iv`. -/
def initW (iv : Spec.Sha512.HashValue) (k : Nat) : List Instr :=
  [.movw .r12 ((lo iv[k]!).extractLsb' 0 16), .movt .r12 ((lo iv[k]!).extractLsb' 16 16),
   .str .r12 .r0 (8 * k),
   .movw .r12 ((hi iv[k]!).extractLsb' 0 16), .movt .r12 ((hi iv[k]!).extractLsb' 16 16),
   .str .r12 .r0 (8 * k + 4)]

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap (initW iv))

/-- Word `k` of the final hash value, big-endian. -/
def outW (k : Nat) : List Instr :=
  [.ldr .r9 .r0 (8 * k), .ldr .r10 .r0 (8 * k + 4), .rev .r10 .r10, .rev .r9 .r9,
   .str .r10 .r6 (8 * k), .str .r9 .r6 (8 * k + 4)]

/-- The sizes, the length field and the digest. -/
def params : Params where
  N := 64
  B := 128
  L := 16
  so := 224
  len := ([.mov .r9 (.imm 0), .str .r9 .r0 176, .mov .r9 (.shifted .r5 .lsr 29), .rev .r9 .r9, .str .r9 .r0 180] : List Instr) ++
    len64 184 true
  out := (List.range 8).flatMap outW

def update : Prog isa := MdStream.Arm.update params "vg_sha512_compress" compress

def finalize : Prog isa := MdStream.Arm.finalize params "vg_sha512_compress" compress

/-! ## The truncated digests

SHA-384, SHA-512/256 and SHA-512/224 output the first 48, 32 and 28 bytes of
the final hash value: `params` with a digest of 6 or 4 words, or of 3 words
and the high half of the fourth (`outHi`). -/

/-- The high half of word `k` of the final hash value, big-endian. -/
def outHi (k : Nat) : List Instr :=
  [.ldr .r10 .r0 (8 * k + 4), .rev .r10 .r10, .str .r10 .r6 (8 * k)]

def params384 : Params := { params with out := (List.range 6).flatMap outW }
def params512_256 : Params := { params with out := (List.range 4).flatMap outW }
def params512_224 : Params := { params with out := (List.range 3).flatMap outW ++ outHi 3 }

/-- `finalize`, writing the digest `P.out` writes (`params384`, …). -/
def finalizeDigest (P : Params) : Prog isa := MdStream.Arm.finalize P "vg_sha512_compress" compress

/-- The SHA-512 family's streaming functions as HMAC, PBKDF2 and the one-shot
digest call them (`Impl.Pbkdf2.Stream.Arm.Hash`), for the member with
initial hash value `iv`, a `D`-byte digest and `init` named `initN`: a
192-byte streaming state and 34 words of working space. -/
def streamFnsOf (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Impl.Pbkdf2.Stream.Arm.Hash :=
  ⟨128, 192, D, 64, 34, initN, init iv, "vg_sha512_update_scratch", update, "vg_sha512_finalize_scratch",
    finalize⟩

def streamFns384 : Impl.Pbkdf2.Stream.Arm.Hash := streamFnsOf 48 "vg_sha384_init_core" Spec.Sha512.H0_384
def streamFns512 : Impl.Pbkdf2.Stream.Arm.Hash := streamFnsOf 64 "vg_sha512_init_core" Spec.Sha512.H0_512
def streamFns512_224 : Impl.Pbkdf2.Stream.Arm.Hash :=
  streamFnsOf 28 "vg_sha512_224_init_core" Spec.Sha512.H0_512_224
def streamFns512_256 : Impl.Pbkdf2.Stream.Arm.Hash :=
  streamFnsOf 32 "vg_sha512_256_init_core" Spec.Sha512.H0_512_256

end VG.Impl.Sha512.Arm.Stream

/-! ## The functions as emitted

Each is its code, then its cleanup (`Impl/Scrub/Arm.lean`): the registers
a callee may change set to constants, and first, for `update` and
`finalize`, the 288 bytes of the stack of their contract, their frame
(`withStackScratch`), zeroed, and for `digest` the whole stack of its
contract, its working space (`withRegScratch`) and what it pushes around
`update`. None returns a value. -/

namespace VG.Impl.Sha512.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_sha384_init`. -/
def init384 : Prog isa := scrub 0 (Stream.init Spec.Sha512.H0_384)

/-- `vg_sha512_init`. -/
def init512 : Prog isa := scrub 0 (Stream.init Spec.Sha512.H0_512)

/-- `vg_sha512_224_init`. -/
def init512_224 : Prog isa := scrub 0 (Stream.init Spec.Sha512.H0_512_224)

/-- `vg_sha512_256_init`. -/
def init512_256 : Prog isa := scrub 0 (Stream.init Spec.Sha512.H0_512_256)

/-- `vg_sha512_update`, which the truncations share. -/
def update : Prog isa := scrubAll 0 288 (Impl.StackScratch.Arm.withStackScratch 288 2 Stream.update)

/-- `vg_sha512_finalize`. -/
def finalize : Prog isa := scrubAll 0 288 (Impl.StackScratch.Arm.withStackScratch 288 1 Stream.finalize)

/-- `vg_sha384_finalize`. -/
def finalize384 : Prog isa :=
  scrubAll 0 288 (Impl.StackScratch.Arm.withStackScratch 288 1 (Stream.finalizeDigest Stream.params384))

/-- `vg_sha512_256_finalize`. -/
def finalize512_256 : Prog isa :=
  scrubAll 0 288 (Impl.StackScratch.Arm.withStackScratch 288 1 (Stream.finalizeDigest Stream.params512_256))

/-- `vg_sha512_224_finalize`. -/
def finalize512_224 : Prog isa :=
  scrubAll 0 288 (Impl.StackScratch.Arm.withStackScratch 288 1 (Stream.finalizeDigest Stream.params512_224))

/-- `vg_sha384_digest`. -/
def digest384 : Prog isa := scrubAll 0 584 (Impl.MdStream.Arm.Digest.digest Stream.streamFns384)

/-- `vg_sha512_digest`. -/
def digest512 : Prog isa := scrubAll 0 584 (Impl.MdStream.Arm.Digest.digest Stream.streamFns512)

/-- `vg_sha512_224_digest`. -/
def digest512_224 : Prog isa := scrubAll 0 584 (Impl.MdStream.Arm.Digest.digest Stream.streamFns512_224)

/-- `vg_sha512_256_digest`. -/
def digest512_256 : Prog isa := scrubAll 0 584 (Impl.MdStream.Arm.Digest.digest Stream.streamFns512_256)

end VG.Impl.Sha512.Arm.Fn
