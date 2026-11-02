module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# The Salsa20/8 Core: RISC-V implementation

`vg_salsa20_8(b = a0)` (with word accesses, `wide`; `b` a multiple of 4)
and `vg_salsa20_8_bytes(b = a0)` (with byte accesses, for any `b`) replace
the 64 bytes at `b` by their Salsa20/8 Core (RFC 7914 §3), as on PPC64LE
(`Impl/Scrypt/PPC64LE/Salsa.lean`).

* Word `k` lives in the low word of `wreg k` (`a1`–`a7`, `t2`–`t6`,
  `s0`–`s3`) throughout; the four double rounds are fully unrolled. RV64I
  with the M extension has no rotation: `x[i] ^= R(x[j] + x[k], n)` is
  `addw`, then the two halves of the rotation by `sllw` and `srliw`, each
  xored into `x[i]`, through the temporaries `t0` and `t1`. Only the low
  words of the registers matter: the 32-bit shifts read only them, and the
  stores write only them.
* `s0`–`s3` are callee-saved: they are saved in a 32-byte frame on the
  stack (`t0` points to it) first and restored last.
* The input stays in `b` until the final addition, which re-reads word `k`
  into `t0` just before storing word `k` of the result over it. Without
  `wide`, a word is read as four bytes (`lbu`, shifted into place through
  `t1`) and written as four (`sb` of it shifted right through `t1`).
* Every address is `a0` or the stack pointer plus a constant, and there are
  no branches, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Scrypt.RISCV64

open VG.RISCV64

/-- The register holding word `k`. -/
def wreg (k : Nat) : Reg :=
  [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3].getD k .a1

/-- The callee-saved registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.s0, .s1, .s2, .s3].getD i .s0

/-- Save them in the frame. -/
def save : List Instr :=
  .addSp .t0 0 :: (List.range 4).flatMap fun i => [.store .d (saved i) .t0 (8 * i)]

/-- Restore them. -/
def restore : List Instr :=
  .addSp .t0 0 :: (List.range 4).flatMap fun i => [.load .d (saved i) .t0 (8 * i)]

/-- `x[i] ^= R(x[j] + x[k], n)`. -/
def line (i j k n : Nat) : List Instr :=
  [.addw .t0 (wreg j) (wreg k), .shift .sll .w .t1 .t0 n, .logic .xor (wreg i) (wreg i) .t1,
   .shift .srl .w .t0 .t0 (32 - n), .logic .xor (wreg i) (wreg i) .t0]

/-- The lines `(i, j, k, n)` of a double round (a column round and a row
round), in the order of RFC 7914 §3. -/
def lines : List (Nat × Nat × Nat × Nat) := [
  (4, 0, 12, 7), (8, 4, 0, 9), (12, 8, 4, 13), (0, 12, 8, 18),
  (9, 5, 1, 7), (13, 9, 5, 9), (1, 13, 9, 13), (5, 1, 13, 18),
  (14, 10, 6, 7), (2, 14, 10, 9), (6, 2, 14, 13), (10, 6, 2, 18),
  (3, 15, 11, 7), (7, 3, 15, 9), (11, 7, 3, 13), (15, 11, 7, 18),
  (1, 0, 3, 7), (2, 1, 0, 9), (3, 2, 1, 13), (0, 3, 2, 18),
  (6, 5, 4, 7), (7, 6, 5, 9), (4, 7, 6, 13), (5, 4, 7, 18),
  (11, 10, 9, 7), (8, 11, 10, 9), (9, 8, 11, 13), (10, 9, 8, 18),
  (12, 15, 14, 7), (13, 12, 15, 9), (14, 13, 12, 13), (15, 14, 13, 18)]

def doubleRound : Prog isa := .block (lines.flatMap fun (i, j, k, n) => line i j k n)

/-- `n` double rounds. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) doubleRound

/-- `d ← ` the word at `a0 + off`: one `lw`, or four `lbu` (through `t1`). -/
def loadWord (wide : Bool) (d : Reg) (off : Nat) : List Instr :=
  if wide then [.load .w d .a0 off] else
    .load .b d .a0 off :: (List.range 3).flatMap fun i =>
      [.load .b .t1 .a0 (off + i + 1), .shift .sll .d .t1 .t1 (8 * (i + 1)), .logic .or d d .t1]

/-- The low word of `r` to `a0 + off`: one `sw`, or four `sb` (through `t1`). -/
def storeWord (wide : Bool) (r : Reg) (off : Nat) : List Instr :=
  if wide then [.store .w r .a0 off] else
    .store .b r .a0 off :: (List.range 3).flatMap fun i =>
      [.shift .srl .d .t1 r (8 * (i + 1)), .store .b .t1 .a0 (off + i + 1)]

/-- Load the input into the registers. -/
def load (wide : Bool) : List Instr := (List.range 16).flatMap fun k => loadWord wide (wreg k) (4 * k)

/-- Add word `k` of the input (re-read from `b` into `t0`) to word `k` of the
rounds' result, and store the sum over it. -/
def finishWord (wide : Bool) (k : Nat) : List Instr :=
  loadWord wide .t0 (4 * k) ++ ([.addw (wreg k) (wreg k) .t0] : List Instr) ++ storeWord wide (wreg k) (4 * k)

def finish (wide : Bool) : List Instr := (List.range 16).flatMap (finishWord wide)

/-- Load, run the rounds and add. -/
def main (wide : Bool) : Prog isa :=
  .seq (.block (save ++ load wide)) (.seq (rounds 4) (.block (finish wide ++ restore)))

/-- The function, in its frame. -/
def salsa (wide : Bool) : Prog isa := .frame (.alloc 32) (main wide) (.free 32)

def salsaName (wide : Bool) : String := if wide then "vg_salsa20_8" else "vg_salsa20_8_bytes"

end VG.Impl.Scrypt.RISCV64
