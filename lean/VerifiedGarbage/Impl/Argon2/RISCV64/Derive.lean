module

public import VerifiedGarbage.Impl.Argon2.RISCV64.Fill
public import VerifiedGarbage.Impl.Argon2.RISCV64.MemoryInit

/-!
# Argon2 on RISC-V: the derivation

`vg_argon2(kind = a0, password = a1, password_len = a2, salt = a3,
salt_len = a4, iterations = a5, memory_cost = a6, lanes = a7, threads,
secret, secret_len, associated_data, ad_len, memory, blocks, scratch, out,
out_len)`, the last ten on the caller's stack.

The PPC64LE derivation (`Impl/Argon2/PPC64LE/Derive.lean`): it allocates its
frame (`Impl/Argon2/RISCV64/Layout.lean`), saves the return address, the
caller's `s0`–`s4` and its register arguments there, and points `s3` to the
frame, `s4` to `scratch` and `s0` 2048 bytes above it throughout. The
contract's `memory` and `scratch` are arrays of `u64`, which RISC-V's
contracts require to be 8-byte aligned (`Abi.alignsBufs`), so every access to
them is a doubleword's or a word's. It computes the parameters and H₀, initializes the
memory, fills it, XORs the last block of every lane into the first block of
the memory, and writes H′ of it to `out`. The lanes are evaluated serially,
which every positive `threads` permits.
-/

@[expose] public section

namespace VG.Impl.Argon2.RISCV64.Derive

open VG.RISCV64

/-! ## The final block and the tag -/

/-- Zero the memory's first block. -/
def reduceClear : List Instr :=
  [lda .a3 memoryArg, .li .a0 0] ++ (List.range 128).map fun k => .store .d .a0 .a3 (8 * k)

/-- XOR the last block of lane `[s3 + laneOff]` into the first block. -/
def reduceLane : List Instr :=
  [ld .a0 laneOff, ld .a1 laneLenOff, .addi .a1 .a1 (-1)] ++ blockAddr ++
    ([HPrime.mov .a1 .a0, lda .a3 memoryArg] : List Instr) ++ writeBlock true

def reduce : Prog isa :=
  .seq (.block (reduceClear ++ setLocal laneOff 0))
    (.loop (.block (reduceLane ++ advanceBy laneOff (ldw .a1 lanesArg))) (.nonzero .a1))

/-- `hprime(memory, 1024, out, out_len, scratch)`. -/
def finalOutput : Prog isa :=
  .seq (.block [lda .a0 memoryArg, .li .a1 1024, lda .a2 outArg, lda .a3 outLenArg,
      HPrime.mov .a4 .s4])
    hPrimeCall

/-! ## The whole function -/

/-- The return address and the caller's registers, and where they are
saved. -/
def savedSlots : List (Reg × Nat) :=
  [(.ra, raOff), (.s0, 80), (.s1, 88), (.s2, 96), (.s3, 104), (.s4, 112)]

/-- The register arguments, `a0`–`a7`, and where they are saved. -/
def argSlots : List (Reg × Nat) :=
  [(.a0, 120), (.a1, 128), (.a2, 136), (.a3, 144), (.a4, 152), (.a5, 160), (.a6, 168), (.a7, 176)]

/-- Save the return address, the caller's registers and the register
arguments, and point `s3` to the frame, `s4` to `scratch` and `s0` 2048
bytes above it. -/
def setup : List Instr :=
  [.addSp .t0 0] ++ (savedSlots ++ argSlots).map (fun (r, d) => .store .d r .t0 d) ++
  [HPrime.mov .s3 .t0, lda .s4 scratchArg, .addi .s0 .s4 1024, .addi .s0 .s0 1024]

/-- The return address and the caller's registers, in the order they are
restored: `s3`, the frame's pointer, last. -/
def restoreSlots : List (Reg × Nat) :=
  [(.ra, raOff), (.s0, 80), (.s1, 88), (.s2, 96), (.s4, 112), (.s3, 104)]

/-- Restore the return address and the caller's registers. -/
def restore : List Instr := restoreSlots.map (fun (r, d) => .load .d r .s3 d)

def body : Prog isa :=
  .seq (.block (setup ++ parameters))
  (.seq code
  (.seq memoryInit
  (.seq passesLoop
  (.seq reduce
  (.seq finalOutput (.block restore))))))

def derive : Prog isa := .frame (.alloc locals) body (.free locals)

end VG.Impl.Argon2.RISCV64.Derive
