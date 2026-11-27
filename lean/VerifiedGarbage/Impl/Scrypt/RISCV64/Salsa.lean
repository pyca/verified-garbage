module

public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# The Salsa20/8 Core of `X xor B[i]`: RISC-V implementation

A step of scryptBlockMix (RFC 7914 §4), with `X` in registers: `half wide
dst src` replaces `X` by the Salsa20/8 Core (RFC 7914 §3) of
`T = X xor` the 64 bytes at `src`, and writes it to the 64 bytes at `dst`,
with word accesses (`wide`; `dst` and `src` multiples of 4) or byte accesses.

* Word `k` of `X` lives in the low word of `wreg k` (`a2`–`a7`, `t2`–`t6`,
  `s0`–`s4`) throughout; the four double rounds are fully unrolled. RV64I
  with the M extension has no rotation: `x[i] ^= R(x[j] + x[k], n)` is
  `addw`, then `sllw` and `srliw`, through the temporaries `t0` and `t1`,
  each of which is `xor`ed into `x[i]`. Only the low
  words of the registers matter: the 32-bit shifts read only them, and the
  stores write only them.
* `T` is in `dst` during the rounds: the final addition re-reads word `k`
  into `t0` just before storing word `k` of the result over it. Without
  `wide`, a word is read as four bytes (`lbu`, shifted into place through
  `t1`) and written as four (`sb` of it shifted right through `t1`).
* Every address is `dst` or `src` plus a constant, and there are
  no branches, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Scrypt.RISCV64

open VG.RISCV64

/-- The register holding word `k`. -/
def wreg (k : Nat) : Reg :=
  [.a2, .a3, .a4, .a5, .a6, .a7, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4].getD k .a2

/-- `x[i] ^= R(x[j] + x[k], n)`. -/
def line (i j k n : Nat) : List Instr :=
  [.addw .t0 (wreg j) (wreg k), .shift .sll .w .t1 .t0 n, .shift .srl .w .t0 .t0 (32 - n),
   .logic .xor (wreg i) (wreg i) .t1, .logic .xor (wreg i) (wreg i) .t0]

/-- The lines `(i, j, k, n)` of a double round (a column round and a row
round). Each round's four quarter-rounds touch disjoint words: rather than
RFC 7914 §3's order (each quarter-round's four lines in turn), a line of
each quarter-round in turn, so that the four chains of dependent lines are
side by side in the code. -/
def lines : List (Nat × Nat × Nat × Nat) := [
  (4, 0, 12, 7), (9, 5, 1, 7), (14, 10, 6, 7), (3, 15, 11, 7),
  (8, 4, 0, 9), (13, 9, 5, 9), (2, 14, 10, 9), (7, 3, 15, 9),
  (12, 8, 4, 13), (1, 13, 9, 13), (6, 2, 14, 13), (11, 7, 3, 13),
  (0, 12, 8, 18), (5, 1, 13, 18), (10, 6, 2, 18), (15, 11, 7, 18),
  (1, 0, 3, 7), (6, 5, 4, 7), (11, 10, 9, 7), (12, 15, 14, 7),
  (2, 1, 0, 9), (7, 6, 5, 9), (8, 11, 10, 9), (13, 12, 15, 9),
  (3, 2, 1, 13), (4, 7, 6, 13), (9, 8, 11, 13), (14, 13, 12, 13),
  (0, 3, 2, 18), (5, 4, 7, 18), (10, 9, 8, 18), (15, 14, 13, 18)]

def doubleRound : Prog isa := .block (lines.flatMap fun (i, j, k, n) => line i j k n)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- `d ← ` the word at `off(n)`: one `lw`, or four `lbu` (`loadLE32`,
through `t1`). -/
def loadWord (wide : Bool) (d n : Reg) (off : Nat) : List Instr :=
  if wide then [.load .w d n off] else Impl.Words.RISCV64.loadLE32 d .t1 n off

/-- The low word of `r` to `off(n)`: one `sw`, or four `sb` (`storeLE32`,
through `t1`). -/
def storeWord (wide : Bool) (r n : Reg) (off : Nat) : List Instr :=
  if wide then [.store .w r n off] else Impl.Words.RISCV64.storeLE32 r .t1 n off

/-- Load the 64 bytes at `src` into the registers. -/
def load (wide : Bool) (src : Reg) : List Instr :=
  (List.range 16).flatMap fun k => loadWord wide (wreg k) src (4 * k)

/-- Word `k` of `T`, `xor`ed into its register and written to `dst`. -/
def mixWord (wide : Bool) (dst src : Reg) (k : Nat) : List Instr :=
  loadWord wide .t0 src (4 * k) ++ ([.logic .xor (wreg k) (wreg k) .t0] : List Instr) ++
    storeWord wide (wreg k) dst (4 * k)

def mix (wide : Bool) (dst src : Reg) : List Instr := (List.range 16).flatMap (mixWord wide dst src)

/-- Add word `k` of `T` (re-read from `dst` into `t0`) to word `k` of the
rounds' result, and store the sum over it. -/
def finishWord (wide : Bool) (dst : Reg) (k : Nat) : List Instr :=
  loadWord wide .t0 dst (4 * k) ++ ([.addw (wreg k) (wreg k) .t0] : List Instr) ++
    storeWord wide (wreg k) dst (4 * k)

def finish (wide : Bool) (dst : Reg) : List Instr := (List.range 16).flatMap (finishWord wide dst)

/-- A step: `X xor` the block at `src`, the rounds, and the final addition,
to `dst`. -/
def half (wide : Bool) (dst src : Reg) : Prog isa :=
  .seq (.block (mix wide dst src)) (.seq (rounds 4) (.block (finish wide dst)))

end VG.Impl.Scrypt.RISCV64
