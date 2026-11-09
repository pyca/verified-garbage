module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Impl.StackScratch.X86_64

/-!
# ECDSA verification of the hash function's output on x86-64

`vg_ecdsa_<curve>_verify(public, digest, digest_len, sig, scratch) -> eax`
(`Instance.verifyHashContract`, `Spec/Ecdsa/Verify/Generic.lean`): in a
frame of `bufBytes` bytes on the stack (`withStackScratch`, the buffer's
address in `r9`), the `len` bytes of the hash that the verification of a
curve takes (`Proof.Ecdsa.Verify.fixedDigest`), then that verification,
`core`, run with them in place of the hash (`hashed`), as on RISC-V
(`Impl/Ecdsa/RISCV64/VerifyHash.lean`):

1. if `digest_len ≥ len`, the hash's leftmost `len` bytes copied to the
   buffer (`copyLong`);
2. otherwise 72 zero bytes stored, and the hash copied to the `len -
   digest_len` bytes after the buffer's start (`copyLoop`, if `digest_len`
   is not zero); for a curve whose `n` has 7 bits fewer than `8 len` (`wide`,
   P-521), the `len + 1` bytes then shifted right by one bit (`shiftBytes`);
3. `core`'s arguments: `public` stays in `rdi`, the buffer goes to `rsi`,
   `sig` to `rdx` and `scratch` to `rcx`.

The hash, its length and the pointers are public, so the branches and the
loop may depend on them.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64.VerifyHash

open VG.X86_64

/-- The frame's bytes: the return address's 8, then the buffer's 80. -/
def bufBytes : Nat := 88

/-- `[r + d]`. -/
def at_ (r : Reg) (d : Nat) : MemOp := { base := r, disp := (d : Int) }

/-- The hash's leftmost `len` bytes, through `r10`. -/
def copyLong (len : Nat) : List Instr :=
  (List.range len).flatMap fun i => [.movzx8 .r10 (at_ .rsi i), .store8 (at_ .r9 i) .r10]

/-- 72 zero bytes, through `r10`. -/
def zeros : List Instr := .mov32 .r10 (.imm 0) :: (List.range 72).flatMap fun j => [.store8 (at_ .r9 j) .r10]

/-- Copy the `rdx ≥ 1` bytes at `rsi` to `r11`, a byte at a time. -/
def copyLoop : Prog isa :=
  .loop (.block [.movzx8 .r10 { base := .rsi }, .store8 { base := .r11 } .r10, .alu .add .rsi (.imm 1),
    .alu .add .r11 (.imm 1), .alu .sub .rdx (.imm 1)]) .ne

/-- Byte `i` of the `len` bytes becomes the low bit of byte `i` and the seven
high bits of byte `i + 1`, through `r10` and `r11`. -/
def shiftBytes (len : Nat) : List Instr :=
  (List.range len).flatMap fun i =>
    [.movzx8 .r10 (at_ .r9 i), .movzx8 .r11 (at_ .r9 (i + 1)), .shift .shl .r10 7, .shift .shr .r11 1,
      .alu .add .r10 (.reg .r11), .store8 (at_ .r9 i) .r10]

/-- A hash shorter than `len` bytes: zeros, the hash after `len - digest_len`
of them, and, if `wide`, the shift. -/
def short (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block (zeros ++ [.mov .r11 (.reg .r9), .alu .add .r11 (.imm (BitVec.ofNat 32 len)),
    .alu .sub .r11 (.reg .rdx), .alu .test .rdx (.reg .rdx)])) <|
  .seq (.ite .e (.block []) copyLoop) <|
  .block (if wide then shiftBytes len else [])

/-- The `len` bytes of the hash at `rsi` (`rdx` bytes) in the buffer at `r9`. -/
def convert (len : Nat) (wide : Bool) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 len))]) <|
  .ite .b (short len wide) (.block (copyLong len))

/-- The arguments of `core`: the buffer in `rsi`, `sig` in `rdx`, `scratch` in `rcx`. -/
def args : List Instr := [.mov .rsi (.reg .r9), .mov .rdx (.reg .rcx), .mov .rcx (.reg .r8)]

/-- The conversion, then `core` with the buffer for the hash. -/
def hashed (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  .seq (convert len wide) (.seq (.block args) core)

/-- `vg_ecdsa_<curve>_verify`, with the buffer in a frame on the stack. -/
def verifyHash (len : Nat) (wide : Bool) (core : Prog isa) : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch bufBytes .r9 (hashed len wide core)

end VG.Impl.Ecdsa.X86_64.VerifyHash
