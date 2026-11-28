module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2

/-!
# SLH-DSA on AArch64: four SHAKE256 hashes, as two pairs

`thash4(in = x0, stride = x1, len = x2, out = x3, work = x4)` computes
`SHAKE256(Mₖ, 8n)` of four messages of the same length, `Mₖ` the `len` bytes
at `in + k·stride`, to the `n` bytes at `out + k·stride`, for `k` from 0 to
3: every `F`, `H`, `PRF` and `T_ℓ` of the SHAKE parameter sets is one lane of
it. `len` is a positive multiple of 8, and so is `n` (16, 24 or 32), which
the code is built for. Each lane is `PK.seed ‖ ADRS ‖ M` and its output goes
over the start of `M`: `out` is `in + n + 32`, and the code writes the
outputs there, from the lanes' addresses (it does not read `x3`). Every
message is read before any output is written. This is the interface of the
x86-64 `thash4` (`Impl/SlhDsa/X86_64/Thash4.lean`), in AAPCS64's registers.

The four Keccak states are two pairs of the two-way permutation
`vg_keccak_f1600_x2` (`Impl/Sha3/AArch64/Neon/X2.lean`): states 0 and 1
interleaved in `work[0..400)` and states 2 and 3 in `work[400..800)`, lane `j`
of state `k` at byte `400·⌊k/2⌋ + 16 j + 8 (k mod 2)` (`Proof/Sha3/X2Contract.lean`,
`stateX2At`). So a row (lane `j` of every state) is the two 16-byte pairs
at `16 j` and `400 + 16 j`, which `ldp`/`stp` load and store. `work[800..928)`
is the permutation's working space and `work[928..936)` the return address
the call keeps there (`X2.call`); the code is generic over the permutation's
variant (`sha3`: with FEAT_SHA3, or in general registers), which it calls
twice for each permutation of the four states.

It keeps its variables in callee-saved registers, which the permutation
keeps: `x19` = `work`, `x20`–`x23` = the lanes' addresses (`in + k·stride`),
`x24` = the position in the messages, `x25` = the bytes left, `x26` = the
row's address (`work + 16 j`), `x27` = the rows left in the block. It saves
its caller's values of them in `work[936..1008)` (`saved`) and restores them
at the end, `x19` last. It zeroes the states (with `v16`, the only vector
register it writes), then XORs the messages into them a word of each at a
time, permuting them after the 17th row of each block (136 bytes,
SHAKE256's rate); then XORs SHAKE's suffix `0x1f` into the next row and
`0x80` into the last byte of row 16, permutes the states, and copies the
first `n` bytes of each to its output.

The only branches are on `x27` and `x25` (`cbz`/`cbnz`), and every address
is a register that depends only on the pointers, `stride`, `len` and the
position, plus an immediate, so only the pointers, `stride` and `len` can
affect timing.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.AArch64.Thash4

open VG.AArch64

/-- The offsets in `work`: the second pair of states, the permutation's
working space (and the return address after it), and the saved registers. -/
def oPair1 : Nat := 400
def oX2 : Nat := 800
def oSave : Nat := 936

/-- The size of `work`. -/
def workLen : Nat := 1024

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The lanes' registers: lane `k`'s address. -/
def lanePtr (k : Nat) : Reg := [Reg.x20, .x21, .x22, .x23].getD k .x20

/-- The callee-saved registers the code uses, and their slots in `work`. -/
def saved : List (Reg × Nat) :=
  [(.x19, oSave), (.x20, oSave + 8), (.x21, oSave + 16), (.x22, oSave + 24), (.x23, oSave + 32),
    (.x24, oSave + 40), (.x25, oSave + 48), (.x26, oSave + 56), (.x27, oSave + 64)]

/-- Save them, with `work` in `x4`. -/
def save : List Instr := saved.map fun (r, d) => .str .x r .x4 d

/-- Restore them from `work` in `x19` (`x19`, the base, last). -/
def restore : List Instr :=
  (saved.filter (·.1 != .x19)).map (fun (r, d) => .ldr .x r .x19 d) ++ [.ldr .x .x19 .x19 oSave]

/-- The states zeroed: 50 stores of the zeroed `v16`. -/
def zero : List Instr := .vop (.movi0 .v16) :: (List.range 50).map fun i => .strq .v16 .x19 (16 * i)

/-- Save the registers, keep the arguments, zero the states, and start at
position 0 and row 0, with 17 rows left in the block. -/
def pro : List Instr :=
  save ++ [mov .x19 .x4, mov .x20 .x0, .add .x .x21 .x20 .x1, .add .x .x22 .x21 .x1, .add .x .x23 .x22 .x1,
    .movz .x .x24 0 0, mov .x25 .x2, mov .x26 .x19, .movz .x .x27 17 0] ++ zero

/-- The next words of messages `2p` and `2p + 1` XORed into pair `p` of the row. -/
def xorPair (p : Nat) : List Instr :=
  [.add .x .x9 (lanePtr (2 * p)) .x24, .ldr .x .x9 .x9 0, .add .x .x10 (lanePtr (2 * p + 1)) .x24,
    .ldr .x .x10 .x10 0, .ldp .x11 .x12 .x26 (oPair1 * p), .logic .eor .x .x11 .x11 .x9,
    .logic .eor .x .x12 .x12 .x10, .stp .x11 .x12 .x26 (oPair1 * p)]

/-- A row: a word of each message XORed into it; advance the position and
the row, and count the bytes and the rows left. -/
def row : List Instr :=
  xorPair 0 ++ xorPair 1 ++
    [.addImm .x .x24 .x24 8, .addImm .x .x26 .x26 16, .subImm .x .x25 .x25 8, .subImm .x .x27 .x27 1]

/-- The four states permuted: the variant's two-way permutation on each pair. -/
def perm (sha3 : Bool) : Prog isa :=
  .seq (Impl.Sha3.AArch64.Neon.X2.call sha3 .x19 .x19 oX2)
    (.seq (.block [.addImm .x .x9 .x19 oPair1]) (Impl.Sha3.AArch64.Neon.X2.call sha3 .x9 .x19 oX2))

/-- Permute the states, and start the next block at row 0. -/
def permuteKeep (sha3 : Bool) : Prog isa :=
  .seq (perm sha3) (.block [mov .x26 .x19, .movz .x .x27 17 0])

/-- The loop's body: a row, and the permutation if it completed the block. -/
def body (sha3 : Bool) : Prog isa :=
  .seq (.block row) (.ite (.zero .x .x27) (permuteKeep sha3) (.block []))

/-- The padding: `0x1f` XORed into each lane of the row, and `0x80` into the
last byte of each lane of row 16. -/
def pad : List Instr :=
  .movz .x .x10 0x1f 0 :: ([0, 8, oPair1, oPair1 + 8].flatMap fun o =>
    [.ldr .x .x9 .x26 o, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x26 o]) ++
  .movz .x .x10 0x8000 3 :: ([256, 264, oPair1 + 256, oPair1 + 264].flatMap fun o =>
    [.ldr .x .x9 .x19 o, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x19 o])

/-- The first `n` bytes (`n / 8` lanes) of the states of pair `p` to their
outputs, at `n + 32` in their lanes. -/
def extractPair (n p : Nat) : List Instr :=
  (List.range (n / 8)).flatMap fun i =>
    [.ldp .x9 .x10 .x19 (oPair1 * p + 16 * i), .str .x .x9 (lanePtr (2 * p)) (n + 32 + 8 * i),
      .str .x .x10 (lanePtr (2 * p + 1)) (n + 32 + 8 * i)]

/-- The outputs. -/
def extract (n : Nat) : List Instr := extractPair n 0 ++ extractPair n 1

/-- `thash4` for outputs of `n` bytes, over the two-way permutation with
FEAT_SHA3 (`sha3`) or in general registers. -/
def thash4 (n : Nat) (sha3 : Bool) : Prog isa :=
  .seq (.block pro)
    (.seq (.loop (body sha3) (.nonzero .x .x25))
      (.seq (.block pad) (.seq (perm sha3) (.block (extract n ++ restore)))))

end VG.Impl.SlhDsa.AArch64.Thash4
