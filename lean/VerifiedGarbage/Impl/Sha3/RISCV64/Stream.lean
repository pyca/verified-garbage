module

public import VerifiedGarbage.Impl.Sha3.RISCV64

/-!
# The SHA-3 sponge: RISC-V implementation

The PPC64LE implementation (`Impl/Sha3/PPC64LE/Stream.lean`), a byte at a
time. The streaming state is the Keccak state (`[u64; 25]` at `state`),
with the bytes of a partial block XORed into it as they arrive (see
`VG.Spec.Sha3.Repr`); the position in the block is kept by the caller.

* `absorb(state = a0, rate = a1, pos = a2, data = a3, len = a4)` XORs the
  bytes of `data` into the state from byte `pos`, permuting the state
  whenever a block is complete, and returns the position after them.
* `pad(state = a0, rate = a1, pos = a2, suffix = a3)` XORs the suffix into
  byte `pos` and `0x80` into byte `rate - 1`, and permutes the state.
* `squeeze(state = a0, rate = a1, pos = a2, out = a3, outlen = a4)` copies
  the state to `out` from byte `pos`, permuting it whenever a block has been
  used up and more output is needed, and returns the position after them.

The state, the data and the output are argument buffers, whose alignment
the contracts do not state, so they are accessed a byte at a time (`lbu`,
`sb`); byte `pos` of the state is addressed as `0(t2)` with `t2 = state +
pos` computed just before the access. A lane at a time, as on PPC64LE,
would assemble each lane from its bytes, which costs about as much.

Each function runs in a frame on the stack (`alloc`), whose first 512 bytes
are the permutation's scratch space (`vg_keccak_f1600`,
`Impl.Sha3.RISCV64.permute`, which they call), and in which they save the
return address, which each call replaces, and, for `absorb` and `squeeze`,
our caller's values of the callee-saved registers they use, `s2`–`s6`,
which the permutation never writes (it saves and restores `s0` and `s1`, so
it would leave values loaded from memory in those): their variables live there (`s2` =
`state`, `s3` = `rate`, `s4` = the position in the block, `s5` = `data` or
`out`, `s6` = bytes of it left). The stack pointer is 16-byte aligned, so
the saves and restores are aligned doubleword accesses.

The comparison of the position with the rate is a subtraction tested against
zero. Every address and branch depends only on the pointers, `rate`, `pos`
and the lengths.
-/

@[expose] public section

namespace VG.Impl.Sha3.RISCV64.Stream

open VG.RISCV64

/-- `mv d, n` (`addi d, n, 0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The bytes of `absorb`'s and `squeeze`'s frames: the permutation's scratch
space (512 bytes), then the saved registers. -/
def frameBytes : Nat := 560

/-- The registers `absorb` and `squeeze` save, and where in the frame. -/
def saved : List (Reg × Nat) := [(.ra, 512), (.s2, 520), (.s3, 528), (.s4, 536), (.s5, 544), (.s6, 552)]

/-- Save them, with the frame's address in `t0`. -/
def save : List Instr := .addSp .t0 0 :: saved.map fun (r, d) => .store .d r .t0 d

/-- Restore them, with the frame's address in `t0`. -/
def restore : List Instr := .addSp .t0 0 :: saved.map fun (r, d) => .load .d r .t0 d

/-- Permute the state at `s2`, with the frame's first 512 bytes as scratch
space. -/
def permuteAt : Prog isa :=
  .seq (.block [mov .a0 .s2, .addSp .a1 0]) (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute)

/-- Save registers and set up ours. -/
def setup : List Instr :=
  save ++ [mov .s2 .a0, mov .s3 .a1, mov .s4 .a2, mov .s5 .a3, mov .s6 .a4]

/-- If the position has reached the rate, back to 0 and permute. -/
def permuteIfFull : Prog isa :=
  .seq (.block [.sub .t1 .s4 .s3]) (.ite (.zero .t1) (.seq (.block [.li .s4 0]) permuteAt) (.block []))

/-- Run the loop `body` while bytes are left (`s6 ≠ 0`), then return the
position, in the frame. -/
def withLoop (body : Prog isa) : Prog isa :=
  .frame (.alloc frameBytes)
    (.seq (.block setup)
      (.seq (.ite (.zero .s6) (.block []) (.loop body (.nonzero .s6)))
        (.block (mov .a0 .s4 :: restore))))
    (.free frameBytes)

/-! ## `absorb` -/

/-- A byte of data XORed into the state. -/
def absorbByte : List Instr :=
  [.load .b .t1 .s5 0, .add .t2 .s2 .s4, .load .b .t3 .t2 0, .logic .xor .t1 .t1 .t3,
    .store .b .t1 .t2 0, .addi .s5 .s5 1, .addi .s4 .s4 1, .addi .s6 .s6 (-1)]

def absorbBody : Prog isa := .seq (.block absorbByte) permuteIfFull

def absorb : Prog isa := withLoop absorbBody

/-! ## `pad` -/

/-- The bytes of `pad`'s frame: the permutation's scratch space, then the
saved return address. -/
def padBytes : Nat := 528

def padMain : List Instr :=
  [.addSp .t0 0, .store .d .ra .t0 512,
    .add .t1 .a0 .a2, .load .b .t2 .t1 0, .logic .xor .t2 .t2 .a3, .store .b .t2 .t1 0,
    .add .t1 .a0 .a1, .addi .t1 .t1 (-1), .load .b .t2 .t1 0, .logicImm .xor .t2 .t2 0x80,
    .store .b .t2 .t1 0, .addSp .a1 0]

def pad : Prog isa :=
  .frame (.alloc padBytes)
    (.seq (.block padMain)
      (.seq (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute)
        (.block [.addSp .t0 0, .load .d .ra .t0 512])))
    (.free padBytes)

/-! ## `squeeze` -/

/-- A byte of the state to `out`. -/
def squeezeByte : List Instr :=
  [.add .t2 .s2 .s4, .load .b .t1 .t2 0, .store .b .t1 .s5 0, .addi .s5 .s5 1,
    .addi .s4 .s4 1, .addi .s6 .s6 (-1)]

def squeezeBody : Prog isa := .seq permuteIfFull (.block squeezeByte)

def squeeze : Prog isa := withLoop squeezeBody

end VG.Impl.Sha3.RISCV64.Stream
