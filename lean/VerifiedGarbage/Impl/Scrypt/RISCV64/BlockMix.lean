module

public import VerifiedGarbage.Impl.Scrypt.RISCV64.Salsa

/-!
# scryptBlockMix: RISC-V implementation

`vg_scrypt_blockmix(b = a0, r = a1, y = a2, save = a3)` (with doubleword accesses,
`wide`; `b` and `y` multiples of 8) and `vg_scrypt_blockmix_bytes` (byte
accesses, any pointers) write scryptBlockMix (RFC 7914 §4) of the `128 * r`
bytes at `b` to the `128 * r` bytes at `y`, as on PPC64LE
(`Impl/Scrypt/PPC64LE/BlockMix.lean`): `Y[2k]` goes to `y + 64k` and
`Y[2k + 1]` to `y + 64 (r + k)`, each computed in place (`T = X xor B[i]`
is written there, and Salsa20/8 replaces it by `Salsa (T)`); `X` is the
block just written (initially `B[2r - 1]`).

`save` (96 bytes, a multiple of 8, in the frame of `vg_scrypt`) holds our
return address, which each call replaces, and our caller's `s5`–`s10`
(`[0, 56)`), and is where Salsa20/8 saves its caller's registers
(`[56, 96)`); there is no stack frame. Across the calls, which preserve
them, `s5` is `B[2k]`, `s6` is `y + 64k`, `s7` is `y + 64 (r + k)`, `s8`
counts the pairs left, `s9` is `X` and `s10` is `save`. Every address is one
of these plus a constant, and the only branch is on the count, so only the
pointers and `r` affect timing.
-/

@[expose] public section

namespace VG.Impl.Scrypt.RISCV64

open VG.RISCV64

/-- `mv d, n`. -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The registers we save, and where they are in `save`. `s10` is last: the
epilogue reads the others through it. -/
def bmSaved : List (Reg × Nat) :=
  [(.ra, 0), (.s5, 8), (.s6, 16), (.s7, 24), (.s8, 32), (.s9, 40), (.s10, 48)]

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
  .seq (.block [mov .a0 dst, .addi .a1 .s10 56]) (.call (salsaName wide) (salsa wide))

/-- Saving the return address and our caller's registers and setting up
ours (`s9 = save`): `s6 = y + 64 r`, `s8 = b + 128 r - 64` (`B[2r - 1]`). -/
def bmPrologue : List Instr :=
  bmSaved.map (fun (r, d) => .store .d r .a3 d) ++
    ([mov .s8 .a1, mov .s5 .a0, mov .s6 .a2, mov .s10 .a3,
      .shift .sll .d .t1 .a1 6, .add .s7 .a2 .t1,
      .shift .sll .d .t1 .a1 7, .add .s9 .a0 .t1, .addi .s9 .s9 (-64)] : List Instr)

/-- One pair: `Y[2k]` from `X` and `B[2k]`, then `Y[2k + 1]` from it and
`B[2k + 1]`; then the pointers move on and the count goes down. -/
def bmBody (wide : Bool) : Prog isa :=
  .seq (.block (xor64 wide .s6 .s9 .s5)) <|
  .seq (salsaAt wide .s6) <|
  .seq (.block (.addi .s5 .s5 64 :: xor64 wide .s7 .s6 .s5)) <|
  .seq (salsaAt wide .s7)
    (.block [mov .s9 .s7, .addi .s5 .s5 64, .addi .s6 .s6 64,
      .addi .s7 .s7 64, .addi .s8 .s8 (-1)])

/-- Restoring them. -/
def bmEpilogue : List Instr := bmSaved.map fun (r, d) => .load .d r .s10 d

def blockMix (wide : Bool) : Prog isa :=
  .seq (.block bmPrologue) (.seq (.loop (bmBody wide) (.nonzero .s8)) (.block bmEpilogue))

def blockMixName (wide : Bool) : String :=
  if wide then "vg_scrypt_blockmix" else "vg_scrypt_blockmix_bytes"

end VG.Impl.Scrypt.RISCV64
