module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Verify
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Comb

/-!
# `vg_ed25519_scalar_base(out = a0, scalar = a1, scratch = a2)` on RISC-V

The PPC64LE code (`Impl/Ed25519/PPC64LE/ScalarBase.lean`, ARMv7's): the
base point in slots 0–3, `[s] B` by `pointFromScalar 16` (all 256 bits),
and its encoding into `out` (whose pointer is in `s3`). The working space,
aligned to 8 bytes, is moved to `a3`, and the callee-saved registers it
writes, `s0`–`s3`, `s5` and `s6`, and `ra` are saved at `SAVE`
(`baseSave`). It leaves `s4` and `s7`–`s11` alone, so that a caller can keep
public values there across the call: a register restored from memory is
secret to the analysis of constant time.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64
open VG.RISCV64

/-- The registers saved, in order. -/
def baseSaved : List Reg := [.s0, .s1, .s2, .s3, .s5, .s6, .ra]

def baseSave : List Instr := (List.range 7).map fun i => .store .d (baseSaved.getD i .s0) .a3 (SAVE + 8 * i)

def baseRestore : List Instr := (List.range 7).map fun i => .load .d (baseSaved.getD i .s0) .a3 (SAVE + 8 * i)

def scalarBaseEngine : Prog isa :=
  .seq (.block initFields) (.seq combMultiply pointEncode)

def scalarBaseSetup : List Instr :=
  [.addi .a3 .a2 0] ++ baseSave ++ [.addi .s3 .a0 0, .addi .s0 .a1 0]

def scalarBaseFinish : List Instr :=
  [.addi .s0 .s3 0] ++ packField .s0 FR 0 ++ baseRestore

def scalarBase : Prog isa :=
  .seq (.block scalarBaseSetup) (.seq scalarBaseEngine (.block scalarBaseFinish))

end VG.Impl.Ed25519.RISCV64
