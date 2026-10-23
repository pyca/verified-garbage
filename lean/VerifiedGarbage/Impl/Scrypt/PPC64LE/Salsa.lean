module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# The Salsa20/8 Core: PPC64LE implementation

`vg_salsa20_8(b = r3, scratch = r4)`: replaces the 64 bytes at `b` by their
Salsa20/8 Core (RFC 7914 §3).

* Word `k` lives in the low word of `wreg k` (`r5`–`r12`, `r14`–`r21`)
  throughout; the four double rounds are fully unrolled. The additions act
  on all 64 bits, so the high words of the registers hold carries, which the
  rotations (`rlwinm`, which reads the low word and zero-extends) and the
  word stores ignore.
* `r0` is the temporary of every line `x[i] ^= R(x[j] + x[k], n)` (a
  rotation left by `n` is a rotation right by `32 - n`).
* `r14`–`r21` are nonvolatile: they are saved in `scratch` first and
  restored last.
* The input stays in `b` until the final addition, which re-reads word `k`
  into `r0` just before storing word `k` of the result over it.
* Every address is `r3` or `r4` plus a constant, and there are no branches,
  so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Scrypt.PPC64LE

open VG.PPC64LE

/-- The register holding word `k`. -/
def wreg (k : Nat) : Reg :=
  [.r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21].getD
    k .r5

/-- The nonvolatile registers used, in the order they are saved. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21].getD i .r14

/-- Save them in `scratch`. -/
def save : List Instr := (List.range 8).flatMap fun i => [.store .d (saved i) .r4 (8 * i)]

/-- Restore them. -/
def restore : List Instr := (List.range 8).flatMap fun i => [.load .d (saved i) .r4 (8 * i)]

/-- `x[i] ^= R(x[j] + x[k], n)`. -/
def line (i j k n : Nat) : List Instr :=
  [.add .r0 (wreg j) (wreg k), .rotr .w .r0 .r0 (32 - n), .logic .xor (wreg i) (wreg i) .r0]

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

/-- Load the input into the registers. -/
def load : List Instr := (List.range 16).flatMap fun k => [.load .w (wreg k) .r3 (4 * k)]

/-- Add word `k` of the input (re-read from `b` into `r0`) to word `k` of the
rounds' result, and store the sum over it. -/
def finishWord (k : Nat) : List Instr :=
  [.load .w .r0 .r3 (4 * k), .add (wreg k) (wreg k) .r0, .store .w (wreg k) .r3 (4 * k)]

def finish : List Instr := (List.range 16).flatMap finishWord

/-- Load, run the rounds and add. -/
def main : Prog isa := .seq (.block load) (.seq (rounds 4) (.block finish))

def salsa : Prog isa := .seq (.block save) (.seq main (.block restore))

end VG.Impl.Scrypt.PPC64LE
