module

public import VerifiedGarbage.Impl.AesGcm.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm

/-!
# ECDSA verification of the hash function's output on 32-bit ARM

`vg_ecdsa_<curve>_verify(public, digest, digest_len, sig, scratch) -> r0`
(`Instance.verifyHashContract`, `Spec/Ecdsa/Verify/Generic.lean`; AAPCS:
`public`, `digest`, `digest_len` and `sig` in `r0`–`r3`, `scratch` on the
stack): in a frame of `frameBytes` bytes on the stack (`withStackScratch`,
which passes the address of its buffer of 80 bytes as a stack
argument after `scratch`), the `len` bytes of the hash that the verification
of a curve takes (`Proof.Ecdsa.Verify.fixedDigest`), then that verification,
`core`, run with them in place of the hash (`hashed`):

1. the buffer's address into `r12`, `sig` saved in the buffer's last word
   (at `sigOff`), and whether `digest_len < len`, from the carry of
   `digest_len - len`, into `Z` (`head`);
2. if `digest_len ≥ len`, the hash's leftmost `len` bytes copied to the
   buffer (`long`);
3. otherwise 72 zero bytes stored, and the hash copied to the `len -
   digest_len` bytes after the buffer's start (AES-GCM's `copyLoop`, if
   `digest_len` is not zero); for a curve whose `n` has 7 bits fewer than
   `8 len` (`wide`, P-521), the `len + 1` bytes then shifted right by one
   bit, byte `i` becoming the low bit of byte `i` and the seven high bits of
   byte `i + 1` (`shiftBytes`), so that the `len` bytes are the hash's
   integer shifted left by 7 bits (`short`);
4. `core`'s arguments: `public` stays in `r0`, the buffer goes to `r1`,
   `sig` (from the buffer) to `r2` and `scratch` (from the stack) to `r3`
   (`args`).

The hash, its length and the pointers are public, so the branches and the
loop may depend on them.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm.VerifyHash

open VG.Arm
open VG.Impl.AesGcm.Arm (imm copyLoop)

/-- Where in the buffer `sig` is kept. -/
def sigOff : Nat := 76

/-- The frame: the copy of `scratch`, the buffer's address, the saved `lr`
and the buffer, a multiple of 8. -/
def frameBytes : Nat := 96

/-- The buffer into `r12`, `sig` into the buffer, and `Z` set iff
`digest_len < len` (the carry of `digest_len - len`, through `r3`). -/
def head (len : Nat) : List Instr :=
  [.ldrSp .r12 4, .str .r3 .r12 sigOff, .cmp .r2 (imm len), .mov .r3 (imm 0), .adc .r3 .r3 (imm 0),
    .cmp .r3 (imm 0)]

/-- The hash's first `len` bytes (at `r1`) copied to the buffer (at `r12`),
through `r3`. -/
def long (len : Nat) : List Instr :=
  (List.range len).flatMap fun i => [.ldrb .r3 .r1 i, .strb .r3 .r12 i]

/-- Byte `i` of the `len` bytes (at `r12`) becomes the low bit of byte `i`
and the seven high bits of byte `i + 1`, through `r1` and `r2`. -/
def shiftBytes (len : Nat) : List Instr :=
  (List.range len).flatMap fun i =>
    [.ldrb .r1 .r12 i, .ldrb .r2 .r12 (i + 1), .mov .r1 (.shifted .r1 .lsl 7),
      .dp .add .r1 .r1 (.shifted .r2 .lsr 1), .strb .r1 .r12 i]

/-- 72 zeros at `r12`, then `r3 := digest_len`, `r2 := r12 + len - digest_len`
and `Z` set iff `digest_len` is zero. -/
def zeros (len : Nat) : List Instr :=
  .mov .r3 (imm 0) :: (List.range 72).flatMap (fun i => [.strb .r3 .r12 i]) ++
    [.mov .r3 (.reg .r2), .dp .add .r2 .r12 (imm len), .dp .sub .r2 .r2 (.reg .r3), .cmp .r3 (imm 0)]

/-- A hash shorter than `len` bytes: zeros, the hash after `len - digest_len`
of them, and, if `wide`, the shift (from the buffer's address again). -/
def short (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block (zeros len)) <|
  .seq (.ite .eq (.block []) copyLoop) <|
  .block (if wide then .ldrSp .r12 4 :: shiftBytes len else [])

/-- The `len` bytes of the hash at `r1` (`r2` bytes) in the buffer. -/
def convert (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block (head len)) (.ite .eq (short len wide) (.block (long len)))

/-- The arguments of `core`: the buffer in `r1`, `sig` in `r2`, `scratch` in `r3`. -/
def args : List Instr := [.ldrSp .r1 4, .ldr .r2 .r1 sigOff, .ldrSp .r3 0]

/-- The conversion, then `core` with the buffer for the hash. -/
def hashed (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  .seq (convert len wide) (.seq (.block args) core)

/-- `vg_ecdsa_<curve>_verify`, with the buffer in a frame on the stack, after
the one stack argument, `scratch`. -/
def verifyHash (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  Impl.StackScratch.Arm.withStackScratch frameBytes 1 (hashed len wide core)

end VG.Impl.Ecdsa.Arm.VerifyHash
