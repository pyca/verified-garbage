module

public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# The Salsa20/8 Core: RISC-V implementation

`vg_salsa20_8(b = a0, save = a1)` (with word accesses, `wide`; `b` a
multiple of 4) and `vg_salsa20_8_bytes(b = a0, save = a1)` (with byte
accesses, for any `b`) replace
the 64 bytes at `b` by their Salsa20/8 Core (RFC 7914 §3), as on PPC64LE
(`Impl/Scrypt/PPC64LE/Salsa.lean`).

* Word `k` lives in the low word of `wreg k` (`a2`–`a7`, `t2`–`t6`,
  `s0`–`s4`) throughout; the four double rounds are fully unrolled. RV64I
  with the M extension has no rotation: `x[i] ^= R(x[j] + x[k], n)` is
  `addw`, then the rotation by `sllw`, `srliw` and `or`, through the
  temporaries `t0` and `t1`, then `xor`. Only the low
  words of the registers matter: the 32-bit shifts read only them, and the
  stores write only them.
* `s0`–`s4` are callee-saved: they are saved in the 40 bytes at `save`, a
  multiple of 8 (in the frame of `vg_scrypt`), first and restored last.
* The input stays in `b` until the final addition, which re-reads word `k`
  into `t0` just before storing word `k` of the result over it. Without
  `wide`, a word is read as four bytes (`lbu`, shifted into place through
  `t1`) and written as four (`sb` of it shifted right through `t1`).
* Every address is `a0` or `a1` plus a constant, and there are
  no branches, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Scrypt.RISCV64

open VG.RISCV64

/-- The register holding word `k`. -/
def wreg (k : Nat) : Reg :=
  [.a2, .a3, .a4, .a5, .a6, .a7, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4].getD k .a2

/-- The callee-saved registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6].getD i .s0

/-- Save them in `save`. -/
def save : List Instr := (List.range 7).flatMap fun i => [.store .d (saved i) .a1 (8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 7).flatMap fun i => [.load .d (saved i) .a1 (8 * i)]

/-- `x[i] ^= R(x[j] + x[k], n)`. -/
def line (i j k n : Nat) : List Instr :=
  [.addw .t0 (wreg j) (wreg k), .shift .sll .w .t1 .t0 n, .shift .srl .w .t0 .t0 (32 - n),
   .logic .or .t0 .t0 .t1, .logic .xor (wreg i) (wreg i) .t0]

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

/-- Two lines side by side, the second through `s5` and `s6`. -/
def pair (a b : Nat × Nat × Nat × Nat) : List Instr :=
  [.addw .t0 (wreg a.2.1) (wreg a.2.2.1), .addw .s5 (wreg b.2.1) (wreg b.2.2.1),
   .shift .sll .w .t1 .t0 a.2.2.2, .shift .sll .w .s6 .s5 b.2.2.2,
   .shift .srl .w .t0 .t0 (32 - a.2.2.2), .shift .srl .w .s5 .s5 (32 - b.2.2.2),
   .logic .xor (wreg a.1) (wreg a.1) .t1, .logic .xor (wreg b.1) (wreg b.1) .s6,
   .logic .xor (wreg a.1) (wreg a.1) .t0, .logic .xor (wreg b.1) (wreg b.1) .s5]

def pairs : List (Nat × Nat × Nat × Nat) → List Instr
  | a :: b :: r => pair a b ++ pairs r
  | _ => []

def doubleRound : Prog isa := .block (pairs lines)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- `d ← ` the word at `a0 + off`: one `lw`, or four `lbu` (`loadLE32`,
through `t1`). -/
def loadWord (wide : Bool) (d : Reg) (off : Nat) : List Instr :=
  if wide then [.load .w d .a0 off] else Impl.Words.RISCV64.loadLE32 d .t1 .a0 off

/-- The low word of `r` to `a0 + off`: one `sw`, or four `sb` (`storeLE32`,
through `t1`). -/
def storeWord (wide : Bool) (r : Reg) (off : Nat) : List Instr :=
  if wide then [.store .w r .a0 off] else Impl.Words.RISCV64.storeLE32 r .t1 .a0 off

/-- Load the input into the registers. -/
def load (wide : Bool) : List Instr := (List.range 16).flatMap fun k => loadWord wide (wreg k) (4 * k)

/-- Add word `k` of the input (re-read from `b` into `t0`) to word `k` of the
rounds' result, and store the sum over it. -/
def finishWord (wide : Bool) (k : Nat) : List Instr :=
  loadWord wide .t0 (4 * k) ++ ([.addw (wreg k) (wreg k) .t0] : List Instr) ++ storeWord wide (wreg k) (4 * k)

def finish (wide : Bool) : List Instr := (List.range 16).flatMap (finishWord wide)

/-- Load, run the rounds and add. -/
def main (wide : Bool) : Prog isa := .seq (.block (load wide)) (.seq (rounds 4) (.block (finish wide)))

def salsa (wide : Bool) : Prog isa := .seq (.block save) (.seq (main wide) (.block restore))

def salsaName (wide : Bool) : String := if wide then "vg_salsa20_8" else "vg_salsa20_8_bytes"

end VG.Impl.Scrypt.RISCV64
