module

public import VerifiedGarbage.Spec.Blake2
public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# BLAKE2 compression function: AArch64 implementation

`vg_blake2{b,s}_compress(state = x0, blocks = x1, n = x2, t = x3, last = w4, scratch = x5)`,
for words of `w` bits (64 for BLAKE2b, 32 for BLAKE2s, with the 64-bit or
32-bit forms of the instructions, `sz w`) and the parameters `P`
(`Spec.Blake2.b` or `Spec.Blake2.s`).

* The sixteen words of the work vector `v` live in registers throughout
  (`wreg`); the rounds are fully unrolled, and each `G` loads its two
  message words from the block (little-endian loads, as BLAKE2 is
  little-endian) into the temporary `x27` as it adds them. The four column
  Gs and then the four diagonal Gs run stage by stage, exposing independent
  arithmetic while keeping each message load adjacent to its additions.
* `x19`–`x24` and `x28`–`x30` are never written (the streaming functions keep
  their own values in `x19`–`x24` across a call); `x25`–`x27` are saved in
  `scratch[0, 24)` and restored at the end.
* The offset counter and the final block flag are kept in `scratch`:
  `scratch[32, 40)` is the low 64 bits of the counter of the current block,
  `scratch[40, 48)` the bits above (the carries out of the low word, which
  only BLAKE2b uses: its counter is 128 bits), and `scratch[48, 56)` the flag
  word, all ones if `last ≠ 0` (a 32-bit argument, whose upper half is
  unspecified) and zero otherwise, computed without a branch.
* Advancing the counter by the block size `2 ^ k` wraps its low word exactly
  when the new low word is below `2 ^ k`, i.e. when its `k`-th and higher
  bits are zero: the carry is `((lo >> k) - 1) >> 63`, again without a branch.
* The only branches are on `n`, and every address is `state`, `blocks`
  (advanced by the block size) or `scratch` plus a constant, so only the
  pointers and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.Blake2.AArch64

open VG.AArch64

/-- The operand size of words of `w` bits. -/
def sz (w : Nat) : Size := if w = 64 then .x else .w

/-- The size of a word in bytes. -/
def ws (w : Nat) : Nat := w / 8

/-- The log₂ of the block size, `16 · ws w`. -/
def lbb (w : Nat) : Nat := if w = 64 then 7 else 6

/-- The register holding word `k` of the work vector. -/
def wreg (k : Nat) : Reg :=
  [.x3, .x4, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x25,
    .x26].getD k .x3

/-- The temporary. -/
def T : Reg := .x27

/-! ## The layout of `scratch` -/

def loOff : Nat := 32
def hiOff : Nat := 40
def fOff : Nat := 48

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.x25, 0), (.x26, 8), (.x27, 16)]

/-- `mov d, #v` for a 64-bit constant: a `movz` and three `movk`s. -/
def movImm64 (d : Reg) (v : BitVec 64) : List Instr :=
  [.movz .x d (v.extractLsb' 0 16) 0, .movk .x d (v.extractLsb' 16 16) 1,
   .movk .x d (v.extractLsb' 32 16) 2, .movk .x d (v.extractLsb' 48 16) 3]

section
variable {w : Nat} (P : Spec.Blake2.Params w)

/-! ## The rounds -/

/-- `G` (RFC 7693 §3.1) on the words in `a, b, c, d`, with the message words
`j` and `k` of the block. Add the message word before `b`: the message
load is independent of the preceding half's final rotation of `b`, keeping
that rotation off the path through both additions. -/
def g (a b c d : Reg) (j k : Nat) : List Instr := [
  .ldr (sz w) T .x1 (ws w * j),
  .add (sz w) a a T, .add (sz w) a a b, .logic .eor (sz w) d d a, .ror (sz w) d d P.R1,
  .add (sz w) c c d, .logic .eor (sz w) b b c, .ror (sz w) b b P.R2,
  .ldr (sz w) T .x1 (ws w * k),
  .add (sz w) a a T, .add (sz w) a a b, .logic .eor (sz w) d d a, .ror (sz w) d d P.R3,
  .add (sz w) c c d, .logic .eor (sz w) b b c, .ror (sz w) b b P.R4]

/-- `G(v, x, y, z, u, m[s[2i]], m[s[2i+1]])` of round `r` (the `i`-th `G` of the
round). -/
def gAt (r i x y z u : Nat) : Prog isa :=
  .block (g P (wreg x) (wreg y) (wreg z) (wreg u) (Spec.Blake2.sigmaAt r (2 * i))
    (Spec.Blake2.sigmaAt r (2 * i + 1)))

/-- Register indices for the four independent column or diagonal Gs. -/
def slots (diagonal : Bool) : List (List Nat) :=
  if diagonal then [[0, 5, 10, 15], [1, 6, 11, 12], [2, 7, 8, 13], [3, 4, 9, 14]]
  else [[0, 4, 8, 12], [1, 5, 9, 13], [2, 6, 10, 14], [3, 7, 11, 15]]

/-- One stage of a G. Its load and message addition stay together because
all four lanes share `T`; the remaining stages use disjoint state registers. -/
def stage (r : Nat) (diagonal : Bool) (lane step : Nat) : List Instr :=
  let rs := ((slots diagonal).getD lane []).map wreg
  let a := rs.getD 0 .x3
  let b := rs.getD 1 .x3
  let c := rs.getD 2 .x3
  let d := rs.getD 3 .x3
  let j := Spec.Blake2.sigmaAt r ((if diagonal then 8 else 0) + 2 * lane +
    (if step < 6 then 0 else 1))
  match step % 6 with
  | 0 => [.ldr (sz w) T .x1 (ws w * j), .add (sz w) a a T, .add (sz w) a a b]
  | 1 => [.logic .eor (sz w) d d a]
  | 2 => [.ror (sz w) d d (if step < 6 then P.R1 else P.R3)]
  | 3 => [.add (sz w) c c d]
  | 4 => [.logic .eor (sz w) b b c]
  | _ => [.ror (sz w) b b (if step < 6 then P.R2 else P.R4)]

/-- The sequential instruction list for four independent Gs, used to prove
that the schedule preserves their final machine state. -/
def referencePass (r : Nat) (diagonal : Bool) : List Instr :=
  (List.range 4).flatMap fun lane =>
    let rs := ((slots diagonal).getD lane []).map wreg
    g P (rs.getD 0 .x3) (rs.getD 1 .x3) (rs.getD 2 .x3) (rs.getD 3 .x3)
      (Spec.Blake2.sigmaAt r ((if diagonal then 8 else 0) + 2 * lane))
      (Spec.Blake2.sigmaAt r ((if diagonal then 8 else 0) + 2 * lane + 1))

/-- Four-way scalar scheduling, without extra registers, loads or instructions. -/
def passCode (r : Nat) (diagonal : Bool) : List Instr :=
  (List.range 12).flatMap fun step =>
    (List.range 4).flatMap fun lane => stage P r diagonal lane step

/-- The same column/diagonal round, interleaved to expose independent arithmetic. -/
def round (r : Nat) : Prog isa :=
  .seq (.block (passCode P r false)) (.block (passCode P r true))

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (round P n)

/-! ## One block -/

/-- Load words `0 … n-1` of the state into words `0 … n-1` of the work vector. -/
def lds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (lds n) (.block [.ldr (sz w) (wreg n) .x0 (ws w * n)])

/-- Words `8 … n+7` of the work vector: the IV. -/
def ivs : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (ivs n) (.block (movImm64 (wreg (n + 8)) ((P.IV.toList.getD n 0).setWidth 64)))

/-- The high word of the offset counter into `T`: BLAKE2b's is `scratch[40, 48)`,
BLAKE2s's the upper half of the low 64 bits. -/
def hiW : List Instr :=
  if w = 64 then [.ldr .x T .x5 hiOff] else [.ldr .x T .x5 loOff, .lsr .x T T 32]

/-- The low word of the offset counter into word 12. -/
def ctrLo : List Instr := [.ldr .x T .x5 loOff, .logic .eor (sz w) (wreg 12) (wreg 12) T]

/-- The high word of the offset counter (in `T`, from `hiW`) into word 13, and
the final block flag into word 14. -/
def ctrHi : List Instr :=
  [.logic .eor (sz w) (wreg 13) (wreg 13) T, .ldr .x T .x5 fOff,
   .logic .eor (sz w) (wreg 14) (wreg 14) T]

/-- XOR the two halves of the work vector into words `0 … n-1` of the state:
`h[i] := h[i] ^ v[i] ^ v[i + 8]`. -/
def fin : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (fin n) (.block [.ldr (sz w) T .x0 (ws w * n),
      .logic .eor (sz w) T T (wreg n), .logic .eor (sz w) T T (wreg (n + 8)),
      .str (sz w) T .x0 (ws w * n)])

/-- Advance to the next block and its offset counter (the carry out of the
low word into the high word), and decrement the count of blocks. The work
vector is dead: `x3, x4, x6, x7` are temporaries. -/
def advance : List Instr :=
  [.addImm .x .x1 .x1 (16 * ws w),
   .ldr .x .x3 .x5 loOff, .addImm .x .x3 .x3 (16 * ws w), .str .x .x3 .x5 loOff,
   .lsr .x .x4 .x3 (lbb w), .subImm .x .x4 .x4 1, .lsr .x .x4 .x4 63,
   .ldr .x .x6 .x5 hiOff, .add .x .x6 .x6 .x4, .str .x .x6 .x5 hiOff,
   .subImm .x .x2 .x2 1]

/-- Initialize the work vector (RFC 7693 §3.2). -/
def init : Prog isa :=
  .seq (lds (w := w) 8) <| .seq (ivs P 8) <| .seq (.block (ctrLo (w := w))) <|
  .seq (.block (hiW (w := w))) (.block (ctrHi (w := w)))

def body : Prog isa :=
  .seq (init P) <| .seq (rounds P P.r) <| .seq (fin (w := w) 8) (.block (advance (w := w)))

/-! ## The whole function -/

def save : List Instr := saved.map fun (r, d) => .str .x r .x5 d
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x5 d

/-- Keep the counter in `scratch` (its high word starts at 0) and the flag
word: with `z` the zero-extended `last`, `0 - ((z | (0 - z)) >> 63)`. -/
def setup : List Instr :=
  [.str .x .x3 .x5 loOff, .movz .x T 0 0, .str .x T .x5 hiOff,
   .logic .orr .w .x4 .x4 .x4, .sub .x .x3 T .x4, .logic .orr .x .x4 .x4 .x3,
   .lsr .x .x4 .x4 63, .sub .x .x4 T .x4, .str .x .x4 .x5 fOff]

def compress : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .x .x2) (.block []) (.loop (body P) (.nonzero .x .x2))) (.block restore))

end

end VG.Impl.Blake2.AArch64
