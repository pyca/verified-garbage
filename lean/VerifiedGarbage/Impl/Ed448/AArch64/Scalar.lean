module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Word

/-!
# Ed448 scalar arithmetic on AArch64

Arithmetic modulo the subgroup order `L = 2^446 - c` (`c < 2^224`), on a
remainder of seven words in `x5–x11`.

Reduction consumes the input a 64-bit word at a time, from the top: the
remainder `r < L` becomes `v = 2^64 r + w` for the next word `w` (in `x4`),
which is `h 2^446 + l` with `h < 2^64`, so `v ≡ l + h c` (mod L) since
`2^446 ≡ c`, and `n = l + h c` is below `2^446 + 2^288 < 2L` (`wordFold`).
`h` is one `extr` of the top two words, and `h c` four `mul`/`umulh` pairs
by the words of `c`, kept in `x21–x24`. The words of `n` are written over
those of `l`, which are the remainder's moved up a word: `n₀` in `x4` and
`nᵢ₊₁` in `x5 + i`. A conditional subtraction of `L` (`csub`) leaves
`v mod L`: `K = 2^448 - L` is added (into `x12–x17`, `x19`), which carries
out of 448 bits exactly when `n ≥ L`, and the sum or `n` selected into
`x5–x11`, from the top word down, with the mask `sbcs` makes of the carry.

Multiply-add copies its inputs to the working space as eight words each
(the top one a byte), forms `r + k s` in sixteen words by product scanning
(`columns`), with `r` as the products of its words and a word one, and
reduces them as above.

Every step runs for all words, independent of their values, with `mul`,
`umulh`, additions, shifts and masks: no division instruction, no branch but
on the loop counter `x3`, and every address a pointer plus a constant or
the counter. The callee-saved registers `x19–x26` are saved in the first 64
bytes of the working space, whose base is in `x2`.
-/

@[expose] public section

namespace VG.Impl.Ed448.AArch64

open VG.AArch64
open VG.Impl.Ed25519.AArch64 (const64 mov)

/-! ## Registers -/

/-- The remainder, lowest word first. -/
def R : List Reg := [.x5, .x6, .x7, .x8, .x9, .x10, .x11]

/-- `n = l + h c`: its low word in `x4`, the others over the remainder's lower six. -/
def N : List Reg := [.x4, .x5, .x6, .x7, .x8, .x9, .x10]

/-- `n + K`. -/
def S : List Reg := [.x12, .x13, .x14, .x15, .x16, .x17, .x19]

/-- The words of `c`, `2^448 - L`'s top word, and zero. -/
def C0 : Reg := .x21
def C1 : Reg := .x22
def C2 : Reg := .x23
def C3 : Reg := .x24
def KT : Reg := .x25
def Z : Reg := .x26

/-- The callee-saved registers used, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.x19, 0), (.x20, 8), (.x21, 16), (.x22, 24), (.x23, 32), (.x24, 40), (.x25, 48), (.x26, 56)]

/-! ## Constants -/

def c0 : BitVec 64 := 0xdc873d6d54a7bb0d
def c1 : BitVec 64 := 0xde933d8d723a70aa
def c2 : BitVec 64 := 0x3bb124b65129c96f
def c3 : BitVec 64 := 0x8335dc16

/-- The words of `c`, `KT = 2^62 · 3` (`K = 2^448 - L = 3 · 2^446 + c`) and zero. -/
def consts : List Instr :=
  const64 C0 c0 ++ const64 C1 c1 ++ const64 C2 c2 ++ const64 C3 c3 ++
    [.movz .x KT 0xc000 3, .movz .x Z 0 0]

/-! ## One word -/

/-- The next word from the top: `x3` counts the input's bytes down. -/
def wordRead : List Instr := [.subImm .x .x3 .x3 8, .add .x .x4 .x1 .x3, .ldr .x .x4 .x4 0]

/-- `h = r₅ >> 62 + 4 r₆` into `x11` (`r₆ < 2^62`), `r₅ mod 2^62` into `x10`. -/
def foldSplit : List Instr := [.extr .x .x11 .x11 .x10 62, .lsl .x .x10 .x10 2, .lsr .x .x10 .x10 2]

/-- The products of `h` by the words of `c`: low halves in `x12–x15`, high
halves in `x16`, `x17`, `x19`, `x20`. -/
def foldMul : List Instr :=
  [.mul .x .x12 .x11 C0, .umulh .x16 .x11 C0, .mul .x .x13 .x11 C1, .umulh .x17 .x11 C1,
    .mul .x .x14 .x11 C2, .umulh .x19 .x11 C2, .mul .x .x15 .x11 C3, .umulh .x20 .x11 C3]

/-- `h c` into `x12–x15`, `x20`. -/
def foldProd : List Instr :=
  [.adds .x .x13 .x13 .x16, .adcs .x .x14 .x14 .x17, .adcs .x .x15 .x15 .x19,
    .adcs .x .x20 .x20 Z]

/-- `n = l + h c`, with `l = (w, r₀, …, r₄, r₅ mod 2^62)` in `x4–x10`. -/
def foldAdd : List Instr :=
  [.adds .x .x4 .x4 .x12, .adcs .x .x5 .x5 .x13, .adcs .x .x6 .x6 .x14, .adcs .x .x7 .x7 .x15,
    .adcs .x .x8 .x8 .x20, .adcs .x .x9 .x9 Z, .adcs .x .x10 .x10 Z]

/-- `2^64 r + w`, reduced below `2L`, in `N`. -/
def wordFold : List Instr := foldSplit ++ foldMul ++ foldProd ++ foldAdd

/-- `n + K` into `S`, with the carry. -/
def csubAdd : List Instr :=
  [.adds .x .x12 .x4 C0, .adcs .x .x13 .x5 C1, .adcs .x .x14 .x6 C2, .adcs .x .x15 .x7 C3,
    .adcs .x .x16 .x8 Z, .adcs .x .x17 .x9 Z, .adcs .x .x19 .x10 KT]

/-- `r = m ? n : s`, through `n`'s register. -/
def sel (r n s : Reg) : List Instr :=
  [.logic .eor .x n n s, .logic .and .x n n .x20, .logic .eor .x r s n]

/-- The words selected, from the top: `rᵢ` from `nᵢ` (`N`) or `sᵢ` (`S`). -/
def selTriples : List (Reg × Reg × Reg) :=
  [(.x11, .x10, .x19), (.x10, .x9, .x17), (.x9, .x8, .x16), (.x8, .x7, .x15), (.x7, .x6, .x14),
    (.x6, .x5, .x13), (.x5, .x4, .x12)]

/-- `n mod L`: the mask (all ones without a carry, so when `n < L`), and the
words selected. -/
def csub : List Instr :=
  csubAdd ++ .sbcs .x .x20 Z Z :: selTriples.flatMap fun (r, n, s) => sel r n s

/-- The next word from the top, folded in and reduced. -/
def scalarWord : List Instr := wordRead ++ wordFold ++ csub

/-- The loop over the words below `x3`. -/
def scalarLoop : Prog isa := .loop (.block scalarWord) (.nonzero .x .x3)

/-! ## Entry and exit -/

def saveRegs (b : Reg) : List Instr := saved.map fun p => .str .x p.1 b p.2
def restoreRegs : List Instr := saved.map fun p => .ldr .x p.1 .x2 p.2

/-- The remainder's words but the lowest zeroed. -/
def zeroHigh : List Instr := [.x6, .x7, .x8, .x9, .x10, .x11].map fun r => .movz .x r 0 0

/-- The remainder's words and their offsets in the output. -/
def outWords : List (Reg × Nat) :=
  [(.x5, 0), (.x6, 8), (.x7, 16), (.x8, 24), (.x9, 32), (.x10, 40), (.x11, 48)]

/-- The remainder to the 57 bytes at `x0`: seven words and a zero byte, after
the callee-saved registers are restored. -/
def finish : List Instr :=
  restoreRegs ++ outWords.map (fun p => .str .x p.1 .x0 p.2) ++ [.movz .x .x12 0 0, .strb .x12 .x0 56]

/-- The top two bytes of the 114 at `x1` as the remainder, and the count of
the bytes below them. -/
def init114 : List Instr :=
  [.ldrb .x5 .x1 112, .ldrb .x12 .x1 113, .lsl .x .x12 .x12 8, .add .x .x5 .x5 .x12] ++
    zeroHigh ++ [.movz .x .x3 112 0]

/-- `vg_ed448_scalar_reduce(out = x0, wide = x1, scratch = x2)`. -/
def scalarReduce : Prog isa :=
  .seq (.block (saveRegs .x2 ++ consts ++ init114)) <| .seq scalarLoop (.block finish)

/-! ## Multiply-add -/

/-- Where `k` and `r` (the left operands), `s` and a word one (the right
operands), and the sixteen words of `r + k s` are. -/
def XK : Nat := 64
def YS : Nat := 192
def ACC : Nat := 320

/-- The 57 bytes at `src` as eight words at `[x4 + o]`. -/
def copy57 (src : Reg) (o : Nat) : List Instr :=
  (List.range 7).flatMap (fun i => [.ldr .x .x5 src (8 * i), .str .x .x5 .x4 (o + 8 * i)]) ++
    [.ldrb .x5 src 56, .str .x .x5 .x4 (o + 56)]

/-- The operands: `k` then `r` at `XK`, `s` then one at `YS`, and the base
into `x2`. -/
def operands : List Instr :=
  copy57 .x2 XK ++ copy57 .x1 (XK + 64) ++ copy57 .x3 YS ++
    [.movz .x .x5 1 0, .str .x .x5 .x4 (YS + 64), mov .x2 .x4]

/-- The accumulator of column `k`: three of `x5–x7`, rotating. -/
def accR (k : Nat) : Nat → Reg := fun n => [Reg.x5, .x6, .x7].getD ((k + n) % 3) .x5

/-- `a₀ a₁ a₂ += x_i · y_j`, loading both operands. -/
def term (a0 a1 a2 : Reg) (i j : Nat) : List Instr :=
  [.ldr .x .x12 .x2 (XK + 8 * i), .ldr .x .x13 .x2 (YS + 8 * j), .mul .x .x14 .x12 .x13,
    .umulh .x15 .x12 .x13, .adds .x a0 a0 .x14, .adcs .x a1 a1 .x15, .adc .x a2 a2 Z]

/-- The terms of column `k`: `k_i s_j` for `i + j = k`, and `r_k · 1`. -/
def mulCol (k : Nat) : List (Nat × Nat) :=
  ((List.range 8).filter fun i => k - i < 8 ∧ i ≤ k).map (fun i => (i, k - i)) ++
    if k < 8 then [(8 + k, 8)] else []

/-- Column `k`: its terms, then its low word stored at `ACC + 8k` and cleared. -/
def column (k : Nat) : List Instr :=
  (mulCol k).flatMap (fun t => term (accR k 0) (accR k 1) (accR k 2) t.1 t.2) ++
    [.str .x (accR k 0) .x2 (ACC + 8 * k), .movz .x (accR k 0) 0 0]

/-- `r + k s` into the sixteen words at `ACC`. -/
def columns : List Instr :=
  [.movz .x Z 0 0, .movz .x .x5 0 0, .movz .x .x6 0 0, .movz .x .x7 0 0] ++
    (List.range 16).flatMap column

/-- The loop over the words at `ACC`, with a zero remainder. -/
def accInit : List Instr :=
  [.addImm .x .x1 .x2 ACC, .movz .x .x5 0 0] ++ zeroHigh ++ [.movz .x .x3 128 0]

/-- `vg_ed448_scalar_mul_add(out = x0, r = x1, k = x2, s = x3, scratch = x4)`. -/
def scalarMulAdd : Prog isa :=
  .seq (.block (saveRegs .x4 ++ operands ++ columns ++ consts ++ accInit)) <|
    .seq scalarLoop (.block finish)

end VG.Impl.Ed448.AArch64
