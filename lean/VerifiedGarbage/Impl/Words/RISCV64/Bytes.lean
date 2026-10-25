module

public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# Bytes of argument buffers in RISC-V code

Instruction sequences for buffers whose alignment the contracts do not
state, which the model reads and writes a byte at a time (see
`Impl/Words/RISCV64.lean`); their lemmas are in
`Proof/Framework/RISCV64/Bytes.lean`:
* `copyBytes`: `n` bytes copied, one at a time;
* `storeBytes`: constant bytes stored, each built by `li`;
* `loadLE64`, `storeLE64`: a little-endian doubleword, as two words.
-/

@[expose] public section

namespace VG.Impl.Words.RISCV64

open VG.RISCV64

/-- Copy the `n` bytes at `soff(src)` to `doff(dst)`, a byte at a time,
through `tmp`. -/
def copyBytes (tmp src dst : Reg) (soff doff n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.load .b tmp src (soff + i), .store .b tmp dst (doff + i)]

/-- Store the bytes `bs` (each below 2048, as `li` encodes it) at `doff(dst)`,
through `tmp`. -/
def storeBytes (tmp dst : Reg) (doff : Nat) (bs : List Nat) : List Instr :=
  (List.range bs.length).flatMap fun i =>
    [.li tmp ((bs.getD i 0 : Nat) : Int), .store .b tmp dst (doff + i)]

/-- `d :=` the little-endian doubleword at `off(n)`, as two words (the high
one in `hi`); `tmp` and `hi` are clobbered. `d`, `tmp`, `hi` and `n` are
different. -/
def loadLE64 (d tmp hi n : Reg) (off : Nat) : List Instr :=
  loadLE32 d tmp n off ++ loadLE32 hi tmp n (off + 4) ++
    [.shift .sll .d hi hi 32, .logic .or d d hi]

/-- Store `v` at `off(n)`, little-endian, as two words (the high one shifted
into `hi`); `tmp` and `hi` are clobbered. `tmp` is neither `v`, `hi` nor
`n`, and `hi` is not `n`. -/
def storeLE64 (v tmp hi n : Reg) (off : Nat) : List Instr :=
  storeLE32 v tmp n off ++ [.shift .srl .d hi v 32] ++ storeLE32 hi tmp n (off + 4)

end VG.Impl.Words.RISCV64
