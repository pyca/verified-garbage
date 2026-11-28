module

public import VerifiedGarbage.Impl.Sha3.X86_64.X4

/-!
# SLH-DSA on x86-64: four SHAKE256 hashes at once

`thash4(in = rdi, stride = rsi, len = rdx, out = rcx, work = r8)` computes
`SHAKE256(Mₖ, 8n)` of four messages of the same length, `Mₖ` the `len` bytes
at `in + k·stride`, to the `n` bytes at `out + k·stride`, for `k` from 0 to
3: every `F`, `H`, `PRF` and `T_ℓ` of the SHAKE parameter sets is one lane of
it. `len` is a positive multiple of 8, and so is `n` (16, 24 or 32), which
the code is built for. Each lane is `PK.seed ‖ ADRS ‖ M` and its output goes
over the start of `M`: `out` is `in + n + 32`, and the code writes the
outputs there, from the lanes' addresses (it does not read `rcx`). Every
message is read before any output is written.

The four Keccak states run at once in the four 64-bit elements of `ymm`
registers (`permute4`, `Impl/Sha3/X86_64/X4.lean`; with `fast`, AVX-512VL's
`permute4R`), interleaved in `work[0..800)`: lane `j` of state `k` at byte
`32 j + 8 k`. `work[800..1600)` is the permutation's second buffer, and
`work[1600..2368)` holds the table of its round constants, which the caller
writes (`rcTable`) and the code only reads.

It keeps the lanes' addresses in `rdi`, `r9`, `r10` and `r11`, zeroes the
states, then XORs the messages into them a word of each at a time (a row of
the states: the position in the messages in `rsi`, the row's offset in
`rcx`, the bytes left in `rdx`), permuting them after the 17th row of each
block (136 bytes, SHAKE256's rate); then XORs SHAKE's suffix `0x1f` into
the next row and `0x80` into the last byte of row 16, permutes the states,
and copies the first `n` bytes of each to its output. Across each
permutation it keeps `rdi`, the bytes left and the position in
`work[2368..2392)`. Those slots are written after the stores of the row
before, whose offset in `work` is a register, and read back before the next
such store, so a constant-time analysis keeps track of them. The only
branches are on `rcx` and on the bytes left, and every address is a pointer
plus an offset that depends only on them, so only the pointers and `len`
can affect timing.

`thash4With zero perm` is the code with the states zeroed by `zero` and
permuted by `perm`, so that implementations without AVX2 share the rest
(`Impl/SlhDsa/X86_64/Thash4Base.lean`).
-/

@[expose] public section

namespace VG.Impl.SlhDsa.X86_64.Thash4

open VG.X86_64
open VG.Impl.Sha3.X86_64 (at_)
open VG.Impl.Sha3.X86_64.X4 (vb st permute4)

/-- The offsets in `work`: the second buffer of the permutation, the table
of the round constants, and the slots of `rdi`, the bytes left and the
position. -/
def oTmp : Nat := 800
def oRc : Nat := 1600
def oPtr : Nat := 2368
def oLeft : Nat := 2376
def oPos : Nat := 2384

/-- The size of `work`. -/
def workLen : Nat := 2400

/-- The lanes' registers: lane `k`'s address. -/
def lanePtr (k : Nat) : Reg := [Reg.rdi, .r9, .r10, .r11].getD k .rdi

/-- `[lane k + rsi]`: the next word of message `k`. -/
def msgAt (k : Nat) : MemOp := { base := lanePtr k, index := some .rsi, scale := 1 }

/-- `[r8 + rcx + 8 k]`: lane `k` of the row `rcx` points to. -/
def rowLane (k : Nat) : MemOp := { base := .r8, index := some .rcx, scale := 1, disp := 8 * k }

/-- The states zeroed with AVX2. -/
def zeroV : List Instr := vb .vpxor .xmm0 .xmm0 .xmm0 :: (List.range 25).map (fun i => st .r8 i .xmm0)

/-- Zero the states (`zero`), set the lanes' addresses, and start at
position 0 and row 0. -/
def pro (zero : List Instr) : List Instr :=
  zero ++ [.mov .r9 (.reg .rdi), .alu .add .r9 (.reg .rsi), .mov .r10 (.reg .r9), .alu .add .r10 (.reg .rsi),
    .mov .r11 (.reg .r10), .alu .add .r11 (.reg .rsi), .mov32 .rsi (.imm 0), .mov32 .rcx (.imm 0)]

/-- The next word of message `k` XORed into lane `k` of the row. -/
def xorLane (k : Nat) : List Instr :=
  [.mov .rax (.mem (msgAt k)), .alu .xor .rax (.mem (rowLane k)), .store (rowLane k) .rax]

/-- A row: a word of each message XORed into it; advance the position and
the row, count the bytes, and set ZF if the row was the block's last. -/
def row : List Instr :=
  (List.range 4).flatMap xorLane ++
    [.alu .add .rsi (.imm 8), .alu .add .rcx (.imm 32), .alu .sub .rdx (.imm 8), .alu .cmp .rcx (.imm 544)]

/-- The arguments of `permute4`: the states, the second buffer, and the
table and its end. -/
def permArgs : List Instr :=
  [.mov .rdi (.reg .r8), .mov .rsi (.reg .r8), .alu .add .rsi (.imm (BitVec.ofNat 32 oTmp)),
    .mov .rdx (.reg .r8), .alu .add .rdx (.imm (BitVec.ofNat 32 oRc)), .mov .rcx (.reg .r8),
    .alu .add .rcx (.imm (BitVec.ofNat 32 oPtr))]

/-- Permute the states with `perm`, keeping `rdi`, the bytes left and the
position in `work`, and start the next block at row 0. -/
def permuteKeep (perm : Prog isa) : Prog isa :=
  .seq (.block ([.store (at_ .r8 oPtr) .rdi, .store (at_ .r8 oLeft) .rdx, .store (at_ .r8 oPos) .rsi] ++ permArgs))
    (.seq perm
      (.block [.mov .rdi (.mem (at_ .r8 oPtr)), .mov .rdx (.mem (at_ .r8 oLeft)), .mov .rsi (.mem (at_ .r8 oPos)),
        .mov32 .rcx (.imm 0)]))

/-- The loop's body: a row, the permutation if it completed the block, and
ZF set if no bytes are left. -/
def body (perm : Prog isa) : Prog isa :=
  .seq (.block row) (.seq (.ite .e (permuteKeep perm) (.block [])) (.block [.alu .test .rdx (.reg .rdx)]))

/-- The padding: `0x1f` XORed into lane `k` of the row, and `0x80` into the
last byte of lane `k` of row 16 (in `rsi`, shifted to the top byte). -/
def padLane (k : Nat) : List Instr :=
  [.mov .rax (.mem (rowLane k)), .alu .xor .rax (.imm 0x1f), .store (rowLane k) .rax,
    .mov .rax (.mem (at_ .r8 (512 + 8 * k))), .alu .xor .rax (.reg .rsi), .store (at_ .r8 (512 + 8 * k)) .rax]

/-- The padding of the four states. -/
def pad : List Instr :=
  .movImm64 .rsi 0x8000000000000000 :: (List.range 4).flatMap padLane

/-- The first `n` bytes (`n / 8` lanes) of state `k` to its output, at
`n + 32` in its lane. -/
def extractLane (n k : Nat) : List Instr :=
  (List.range (n / 8)).flatMap fun i =>
    [.mov .rax (.mem (at_ .r8 (32 * i + 8 * k))), .store (at_ (lanePtr k) (n + 32 + 8 * i)) .rax]

/-- The outputs. -/
def extract (n : Nat) : List Instr := (List.range 4).flatMap (extractLane n)

/-- `thash4` for outputs of `n` bytes, with the states zeroed by `zero` and
permuted by `perm`, and `tail` after the outputs. -/
def thash4With (zero : List Instr) (perm : Prog isa) (n : Nat) (tail : List Instr) : Prog isa :=
  .seq (.block (pro zero))
    (.seq (.loop (body perm) .ne)
      (.seq (.block pad) (.seq (permuteKeep perm) (.block (extract n ++ tail)))))

/-- `thash4` for outputs of `n` bytes, with AVX2 (or, with `fast`, AVX-512VL). -/
def thash4 (n : Nat) (fast : Bool := false) : Prog isa :=
  thash4With zeroV (permute4 fast) n [.vop .vzeroupper]

end VG.Impl.SlhDsa.X86_64.Thash4
