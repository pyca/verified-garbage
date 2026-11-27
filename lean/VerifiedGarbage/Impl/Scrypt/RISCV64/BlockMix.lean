module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.Salsa

/-!
# scryptBlockMix: RISC-V implementation

`vg_scrypt_blockmix(b = a0, r = a1, y = a2, save = a3)` (with doubleword accesses,
`wide`; `b` and `y` multiples of 8) and `vg_scrypt_blockmix_bytes` (byte
accesses, any pointers) write scryptBlockMix (RFC 7914 §4) of the `128 * r`
bytes at `b` to the `128 * r` bytes at `y`: `Y[2k]` goes to `y + 64k` and
`Y[2k + 1]` to `y + 64 (r + k)`. `X`, the block just written (initially
`B[2r - 1]`), stays in registers from one step to the next (`half`,
`Impl/Scrypt/RISCV64/Salsa.lean`), and only the first is read from memory.

`save` (96 bytes, a multiple of 8, in the frame of `vg_scrypt`) holds our
caller's `s0`–`s8` and `s10` (`[0, 80)`); there is no stack frame, and no
call. Beside `X`, `s5` is `B[2k]`, `s6` is `y + 64k`, `s7` is
`y + 64 (r + k)`, `s8` counts the pairs left, and `s10` is `save`. Every
address is one of these plus a constant (or `B[2r - 1]`), and the only branch
is on the count, so only the pointers and `r` affect timing.
-/

@[expose] public section

namespace VG.Impl.Scrypt.RISCV64

open VG.RISCV64

/-- `mv d, n`. -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The registers we save, and where they are in `save`. `s10` is last: the
epilogue reads the others through it. -/
def bmSaved : List (Reg × Nat) :=
  [(.s0, 0), (.s1, 8), (.s2, 16), (.s3, 24), (.s4, 32), (.s5, 40), (.s6, 48), (.s7, 56), (.s8, 64),
    (.s10, 72)]

/-- The width of the copies' units: doublewords, or without `wide` bytes. -/
def unitW (wide : Bool) : Width := if wide then .d else .b

/-- The units' size. -/
def unitB (wide : Bool) : Nat := if wide then 8 else 1

/-- Saving our caller's registers and setting up ours; `t0 = b + 128 r - 64`
(`B[2r - 1]`). -/
def bmPrologue : List Instr :=
  bmSaved.map (fun (r, d) => .store .d r .a3 d) ++
    ([mov .s8 .a1, mov .s5 .a0, mov .s6 .a2, mov .s10 .a3,
      .shift .sll .d .t1 .a1 6, .add .s7 .a2 .t1,
      .shift .sll .d .t1 .a1 7, .add .t0 .a0 .t1, .addi .t0 .t0 (-64)] : List Instr)

/-- One pair: `Y[2k]` from `X` and `B[2k]`, then `Y[2k + 1]` from it and
`B[2k + 1]`; then the pointers move on and the count goes down. -/
def bmBody (wide : Bool) : Prog isa :=
  .seq (half wide .s6 .s5) <|
  .seq (.block [.addi .s5 .s5 64]) <|
  .seq (half wide .s7 .s5)
    (.block [.addi .s5 .s5 64, .addi .s6 .s6 64, .addi .s7 .s7 64, .addi .s8 .s8 (-1)])

/-- Restoring them. -/
def bmEpilogue : List Instr := bmSaved.map fun (r, d) => .load .d r .s10 d

def blockMix (wide : Bool) : Prog isa :=
  .seq (.block bmPrologue) <| .seq (.block (load wide .t0)) <| .seq (.loop (bmBody wide) (.nonzero .s8)) (.block bmEpilogue)

def blockMixName (wide : Bool) : String :=
  if wide then "vg_scrypt_blockmix" else "vg_scrypt_blockmix_bytes"

end VG.Impl.Scrypt.RISCV64
