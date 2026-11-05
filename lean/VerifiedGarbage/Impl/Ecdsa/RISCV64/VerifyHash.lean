module

public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Impl.StackScratch.RISCV64

/-!
# ECDSA verification of the hash function's output on RISC-V

`vg_ecdsa_<curve>_verify(public, digest, digest_len, sig, scratch) -> a0`
(`Instance.verifyHashContract`, `Spec/Ecdsa/Verify/Generic.lean`): in a
frame of `bufBytes` bytes on the stack (`withStackScratch`, its address in
`a5`), the `len` bytes of the hash that the verification of a curve takes
(`Proof.Ecdsa.Verify.fixedDigest`), then that verification, `core`, run
with them in place of the hash (`hashed`):

1. if `digest_len ≥ len`, the hash's leftmost `len` bytes copied to the
   buffer (`copyBytes`);
2. otherwise 72 zero bytes stored, and the hash copied to the `len -
   digest_len` bytes after the buffer's start (`copyLoop`, if `digest_len`
   is not zero); for a curve whose `n` has 7 bits fewer than `8 len` (`wide`,
   P-521), the `len + 1` bytes then shifted right by one bit, byte `i`
   becoming the low bit of byte `i` and the seven high bits of byte `i + 1`
   (`shiftBytes`), so that the `len` bytes are the hash's integer shifted left
   by 7 bits;
3. `core`'s arguments: `public` stays in `a0`, the buffer goes to `a1`, `sig`
   to `a2` and `scratch` to `a3`.

The hash, its length and the pointers are public, so the branches and the
loop may depend on them.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.RISCV64.VerifyHash

open VG.RISCV64 VG.Impl.Words.RISCV64

/-- The buffer's bytes: at least `len + 1` (67 for P-521) and 72 (the zeros),
a multiple of 16. -/
def bufBytes : Nat := 80

/-- Byte `i` of the `len` bytes becomes the low bit of byte `i` and the seven
high bits of byte `i + 1`, through `t1` and `t2`. -/
def shiftBytes (len : Nat) : List Instr :=
  (List.range len).flatMap fun i =>
    [.load .b .t1 .a5 i, .load .b .t2 .a5 (i + 1), .shift .sll .d .t1 .t1 7,
      .shift .srl .d .t2 .t2 1, .add .t1 .t1 .t2, .store .b .t1 .a5 i]

/-- A hash shorter than `len` bytes: zeros, the hash after `len - digest_len`
of them, and, if `wide`, the shift. -/
def short (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block (storeBytes .t1 .a5 0 (List.replicate 72 0) ++
    [.addi .t2 .a5 len, .sub .t2 .t2 .a2])) <|
  .seq (.ite (.zero .a2) (.block []) (copyLoop .t1 .a1 .t2 .a2)) <|
  .block (if wide then shiftBytes len else [])

/-- The `len` bytes of the hash at `a1` (`a2` bytes) in the buffer at `a5`. -/
def convert (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block [.li .t0 len]) <|
  .ite (.ltu .a2 .t0) (short len wide) (.block (copyBytes .t1 .a1 .a5 0 0 len))

/-- The arguments of `core`: the buffer in `a1`, `sig` in `a2`, `scratch` in `a3`. -/
def args : List Instr := [.addi .a1 .a5 0, .addi .a2 .a3 0, .addi .a3 .a4 0]

/-- The conversion, then `core` with the buffer for the hash. -/
def hashed (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  .seq (convert len wide) (.seq (.block args) core)

/-- `vg_ecdsa_<curve>_verify`, with the buffer in a frame on the stack. -/
def verifyHash (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  Impl.StackScratch.RISCV64.withStackScratch bufBytes .a5 (hashed len wide core)

end VG.Impl.Ecdsa.RISCV64.VerifyHash
