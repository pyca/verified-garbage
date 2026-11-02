module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.Salsa

/-!
# scryptBlockMix: RISC-V implementation

`vg_scrypt_blockmix(b = a0, r = a1, y = a2)` (with doubleword accesses,
`wide`; `b` and `y` multiples of 8) and `vg_scrypt_blockmix_bytes` (byte
accesses, any pointers) write scryptBlockMix (RFC 7914 §4) of the `128 * r`
bytes at `b` to the `128 * r` bytes at `y`, as on PPC64LE
(`Impl/Scrypt/PPC64LE/BlockMix.lean`): `Y[2k]` goes to `y + 64k` and
`Y[2k + 1]` to `y + 64 (r + k)`, each computed in place (`T = X xor B[i]`
is written there, and Salsa20/8 replaces it by `Salsa (T)`); `X` is the
block just written (initially `B[2r - 1]`).

The function runs in a 48-byte frame on the stack holding our return
address, which each call replaces, and our caller's `s4`–`s8`. Across the
calls, which preserve them, `s4` is `B[2k]`, `s5` is `y + 64k`, `s6` is
`y + 64 (r + k)`, `s7` counts the pairs left and `s8` is `X`. Every address
is one of these or the stack pointer plus a constant, and the only branch is
on the count, so only the pointers and `r` affect timing.
-/

@[expose] public section

namespace VG.Impl.Scrypt.RISCV64

open VG.RISCV64

/-- `mv d, n`. -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The registers we save, and where they are in the frame. -/
def bmSaved : List (Reg × Nat) :=
  [(.ra, 0), (.s4, 8), (.s5, 16), (.s6, 24), (.s7, 32), (.s8, 40)]

/-- The width of the copies' units: doublewords, or without `wide` bytes. -/
def unitW (wide : Bool) : Width := if wide then .d else .b

/-- The units' size. -/
def unitB (wide : Bool) : Nat := if wide then 8 else 1

/-- Unit `k` (a doubleword, or without `wide` a byte) of
`[dst] ← [x] xor [src]`. -/
def xorU (wide : Bool) (dst x src : Reg) (k : Nat) : List Instr :=
  [.load (unitW wide) .t0 x (unitB wide * k), .load (unitW wide) .t1 src (unitB wide * k),
   .logic .xor .t0 .t0 .t1, .store (unitW wide) .t0 dst (unitB wide * k)]

/-- The 64 bytes `[dst] ← [x] xor [src]`. -/
def xor64 (wide : Bool) (dst x src : Reg) : List Instr :=
  (List.range (if wide then 8 else 64)).flatMap (xorU wide dst x src)

/-- Salsa20/8 of the block at `dst`. -/
def salsaAt (wide : Bool) (dst : Reg) : Prog isa :=
  .seq (.block [mov .a0 dst]) (.call (salsaName wide) (salsa wide))

/-- Saving the return address and our caller's registers and setting up
ours: `s6 = y + 64 r`, `s8 = b + 128 r - 64` (`B[2r - 1]`). -/
def bmPrologue : List Instr :=
  .addSp .t0 0 :: bmSaved.map (fun (r, d) => .store .d r .t0 d) ++
    ([mov .s7 .a1, mov .s4 .a0, mov .s5 .a2,
      .shift .sll .d .t1 .a1 6, .add .s6 .a2 .t1,
      .shift .sll .d .t1 .a1 7, .add .s8 .a0 .t1, .addi .s8 .s8 (-64)] : List Instr)

/-- One pair: `Y[2k]` from `X` and `B[2k]`, then `Y[2k + 1]` from it and
`B[2k + 1]`; then the pointers move on and the count goes down. -/
def bmBody (wide : Bool) : Prog isa :=
  .seq (.block (xor64 wide .s5 .s8 .s4)) <|
  .seq (salsaAt wide .s5) <|
  .seq (.block (.addi .s4 .s4 64 :: xor64 wide .s6 .s5 .s4)) <|
  .seq (salsaAt wide .s6)
    (.block [mov .s8 .s6, .addi .s4 .s4 64, .addi .s5 .s5 64,
      .addi .s6 .s6 64, .addi .s7 .s7 (-1)])

/-- Restoring them. -/
def bmEpilogue : List Instr := .addSp .t0 0 :: bmSaved.map fun (r, d) => .load .d r .t0 d

def blockMixMain (wide : Bool) : Prog isa :=
  .seq (.block bmPrologue) (.seq (.loop (bmBody wide) (.nonzero .s7)) (.block bmEpilogue))

def blockMix (wide : Bool) : Prog isa := .frame (.alloc 48) (blockMixMain wide) (.free 48)

def blockMixName (wide : Bool) : String :=
  if wide then "vg_scrypt_blockmix" else "vg_scrypt_blockmix_bytes"

end VG.Impl.Scrypt.RISCV64
