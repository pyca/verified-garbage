module

public import VerifiedGarbage.Impl.Rc2.AArch64.Stream
public import VerifiedGarbage.Impl.StackScratch.AArch64

/-!
# ECDSA verification of the hash function's output on AArch64

`vg_ecdsa_<curve>_verify(public, digest, digest_len, sig, scratch) -> x0`
(`Instance.verifyHashContract`, `Spec/Ecdsa/Verify/Generic.lean`): in a
frame of `bufBytes` bytes on the stack (`withStackScratch`, its address in
`x5`), the `len` bytes of the hash that the verification of a curve takes
(`Proof.Ecdsa.Verify.fixedDigest`), then that verification, `core`, run
with them in place of the hash (`hashed`):

1. whether `digest_len ≥ len`, in `x11`, which `cbnz` tests: the model has
   no flags the taint analysis tracks, so a shift and a mask (`test`);
2. if so, the hash's leftmost `len` bytes copied to the buffer (`long`);
3. otherwise 72 zero bytes stored, and the hash copied to the `len -
   digest_len` bytes after the buffer's start (`copy`, which does nothing if
   `digest_len` is zero); for a curve whose `n` has 7 bits fewer than
   `8 len` (`wide`, P-521), the `len + 1` bytes then shifted right by one
   bit, byte `i` becoming the low bit of byte `i` and the seven high bits of
   byte `i + 1` (`shiftBytes`), so that the `len` bytes are the hash's
   integer shifted left by 7 bits;
4. `core`'s arguments: `public` stays in `x0`, the buffer goes to `x1`, `sig`
   to `x2` and `scratch` to `x3`.

Only caller-saved registers are written: `x9`–`x13`, and `x1` and `x2`,
which the copy advances. The hash, its length and the pointers are public,
so the branches and the loop may depend on them.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.AArch64.VerifyHash

open VG.AArch64

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The buffer's bytes: at least `len + 1` (67 for P-521) and 72 (the zeros),
a multiple of 16. -/
def bufBytes : Nat := 80

/-- `x11` nonzero if and only if `digest_len` (`x2`) is at least `len`
(`0 < len ≤ 66`), without the flags: `x2 / 128`, or'ed with
`(x2 mod 128 + 128 - len) / 128`, which is 1 exactly when `x2 mod 128 ≥ len`. -/
def test (len : Nat) : List Instr :=
  [.lsr .x .x10 .x2 7, .movz .x .x11 127 0, .logic .and .x .x12 .x2 .x11,
    .addImm .x .x12 .x12 (128 - len), .lsr .x .x12 .x12 7, .logic .orr .x .x11 .x10 .x12]

/-- The hash's leftmost `len` bytes (from `x1`) to the buffer (`x5`), through
`x9`. -/
def long (len : Nat) : List Instr :=
  (List.range len).flatMap fun i => [.ldrb .x9 .x1 i, .strb .x9 .x5 i]

/-- 72 zero bytes at the buffer (`x5`), from `x12`. -/
def zeroBytes : List Instr :=
  (List.range 72).flatMap fun j => [.strb .x12 .x5 j]

/-- Byte `i` of the `len` bytes becomes the low bit of byte `i` and the seven
high bits of byte `i + 1`, through `x9` and `x10`. -/
def shiftBytes (len : Nat) : List Instr :=
  (List.range len).flatMap fun i =>
    [.ldrb .x9 .x5 i, .ldrb .x10 .x5 (i + 1), .lsl .x .x9 .x9 7, .lsr .x .x10 .x10 1,
      .add .x .x9 .x9 .x10, .strb .x9 .x5 i]

/-- A hash shorter than `len` bytes: zeros, the hash after `len - digest_len`
of them (`x13`), and, if `wide`, the shift. -/
def short (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block (.movz .x .x12 0 0 :: zeroBytes ++ [.addImm .x .x13 .x5 len, .sub .x .x13 .x13 .x2])) <|
  .seq (Impl.Rc2.AArch64.Stream.copy .x1 0 .x13 0 .x2) <|
  .block (if wide then shiftBytes len else [])

/-- The `len` bytes of the hash at `x1` (`x2` bytes) in the buffer at `x5`. -/
def convert (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block (test len)) <|
  .ite (.nonzero .x .x11) (.block (long len)) (short len wide)

/-- The arguments of `core`: the buffer in `x1`, `sig` in `x2`, `scratch` in `x3`. -/
def args : List Instr := [mov .x1 .x5, mov .x2 .x3, mov .x3 .x4]

/-- The conversion, then `core` with the buffer for the hash. -/
def hashed (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  .seq (convert len wide) (.seq (.block args) core)

/-- `vg_ecdsa_<curve>_verify`, with the buffer in a frame on the stack. -/
def verifyHash (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  Impl.StackScratch.AArch64.withStackScratch bufBytes .x5 (hashed len wide core)

end VG.Impl.Ecdsa.AArch64.VerifyHash
