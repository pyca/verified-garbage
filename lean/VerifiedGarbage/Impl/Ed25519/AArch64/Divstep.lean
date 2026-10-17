module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.Inv
public import VerifiedGarbage.Impl.Ed25519.AArch64.Field

/-!
# Ed25519 and X25519 on AArch64: the inversion modulo `p = 2²⁵⁵ - 19` by divsteps

`[slot 15] ≡ [slot 2]^(p - 2)` (mod `p`), as s2n-bignum's
`bignum_inv_p25519`: ten batches of 59 Bernstein–Yang divsteps (the short
Weierstrass curves' packed divsteps, `Weierstrass.AArch64.pwords`) from
`(d, f, g) = (1, p, x mod p)`, each batch's matrix applied to `(f, g)`, shifted
right by 59, and to `(u, v)` modulo `p`, which start at `(0, 2⁻⁵⁹⁰ mod p)` so
that `(f, g) ≡ x · 2^(590 - 59 i) · (u, v)` after `i` batches. Then `f = ±1`
(or `p`, for `x ≡ 0`, when `u = 0`) and `x⁻¹ ≡ f u`.

All of it but the divsteps is in registers but for the numbers: `f` and `g`
(signed, four words), `u` and `v` (below `2²⁵⁶`), and each row of a batch's
products (five words) before its shift or its reduction, at byte offsets 192
to 487 of the working space (`x0`); `d` is kept there too, the output pointer
`x1` in `x19` and the batch counter in `x20`. A row multiplies by the
magnitudes of the matrix entries, complementing the words for a negative one
and adding the magnitude back, as s2n-bignum does.
-/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64.Divstep

open VG.AArch64
open VG.Impl.Ed25519.AArch64 (ld st const64 offset loads stores)

/-! ## Layout (byte offsets) -/

def F : Nat := 192
def G : Nat := 224
def U : Nat := 256
def V : Nat := 288
/-- The rows' products, five words each. -/
def TF : Nat := 320
def TG : Nat := 360
def TU : Nat := 400
def TV : Nat := 440
def DSAVE : Nat := 480

/-- `2⁻⁵⁹⁰ mod p`. -/
def v0 : Nat := 0x276508b2417706156c6c893805ac5242a8c68f3f1d132595a0f99e2375022099

/-- `[o] = v` (four words), through `x2`. -/
def storeConst (o v : Nat) : List Instr :=
  (List.range 4).flatMap fun i => const64 .x2 (BitVec.ofNat 64 (v >>> (64 * i))) ++ [st .x2 (o + 8 * i)]

/-! ## A row of a batch

`[t] = c + (x ⊕ sa) ma + (y ⊕ sb) mb - 2²⁵⁶ (ma ∧ ta + mb ∧ tb)` modulo `2³²⁰`
(five words): the magnitudes `ma`, `mb` of two matrix entries and their sign
masks `sa`, `sb`, the words of `x` and `y` (four each) complemented by them,
`c = (ma ∧ sa) + (mb ∧ sb)`, and `ta`, `tb` the masks of the complemented
top words' signs if `x` and `y` are signed (`f`, `g`), else `sa` and `sb`
(`u`, `v`). Through `x1`–`x3`, `x8`–`x10`, with `x12 = 0`. -/

/-- `x9, x10 = lo, hi (a m)`; `wo + 2⁶⁴ co = wi + 2⁶⁴ ci + a m`. -/
def half (a m wi wo ci co : Reg) : List Instr :=
  [.mul .x .x9 a m, .umulh .x10 a m, .adds .x wo wi .x9, .adc .x co ci .x10]

/-- `x8 = [o] ⊕ s`. -/
def ldx (o : Nat) (s : Reg) : List Instr := [ld .x8 o, .logic .eor .x .x8 .x8 s]

/-- `d = -(m ∧ t)`, `t` the mask of `x8`'s sign if `signed`, else `s`, through `d`. -/
def corr (signed : Bool) (d m s : Reg) : List Instr :=
  if signed then [.lsr .x d .x8 63, .sub .x d .x12 d, .logic .and .x d d m, .sub .x d .x12 d]
  else [.logic .and .x d s m, .sub .x d .x12 d]

/-- A word of a row below the top: `[t] + 2⁶⁴ x2 = wi + [xo] ⊕ sa · ma + [yo] ⊕ sb · mb`. -/
def digit (t xo yo : Nat) (ma sa mb sb wi : Reg) : List Instr :=
  ldx xo sa ++ half .x8 ma wi .x1 .x12 .x2 ++ ldx yo sb ++ half .x8 mb .x1 .x1 .x2 .x2 ++ [st .x1 t]

/-- The row's top two words, `x2` carried in and the corrections in `x3`. -/
def top (signed : Bool) (t xo yo : Nat) (ma sa mb sb : Reg) : List Instr :=
  ldx xo sa ++ corr signed .x3 ma sa ++ half .x8 ma .x2 .x1 .x3 .x3 ++
  ldx yo sb ++ corr signed .x2 mb sb ++ [.add .x .x3 .x3 .x2] ++ half .x8 mb .x1 .x1 .x3 .x3 ++
    [st .x1 t, st .x3 (t + 8)]

/-- A row: `x`, `y` at `xo`, `yo`; the entries `(ma, sa)`, `(mb, sb)`; `c` in `car`. -/
def row (signed : Bool) (t xo yo : Nat) (ma sa mb sb car : Reg) : List Instr :=
  digit t xo yo ma sa mb sb car ++ digit (t + 8) (xo + 8) (yo + 8) ma sa mb sb .x2 ++
  digit (t + 16) (xo + 16) (yo + 16) ma sa mb sb .x2 ++ top signed (t + 24) (xo + 24) (yo + 24) ma sa mb sb

/-! ## The rows' results -/

/-- `[o] = [t] / 2⁵⁹` (four words of the five). -/
def shift (o t : Nat) : List Instr :=
  [ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24), ld .x9 (t + 32),
    .extr .x .x1 .x2 .x1 59, .extr .x .x2 .x3 .x2 59, .extr .x .x3 .x8 .x3 59, .extr .x .x8 .x9 .x8 59,
    st .x1 o, st .x2 (o + 8), st .x3 (o + 16), st .x8 (o + 24)]

/-- `[o] ≡ [t]` (mod `p`), below `2²⁵⁶`, for `[t]` signed (five words): with
`q = ⌊[t] / 2²⁵⁵⌋ - [[t] < 0]`, `[t] - 2²⁵⁵ q + 19 q`. `x13 = 19`. -/
def reduce (o t : Nat) : List Instr :=
  [ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24), ld .x9 (t + 32),
    -- q into x10
    .extr .x .x10 .x9 .x8 63, .lsr .x .x11 .x9 63, .sub .x .x10 .x10 .x11,
    -- the low part's top word
    .lsl .x .x11 .x10 63, .add .x .x8 .x8 .x11,
    -- 19 q: low word x9, high word x11 (signed), sign words x14
    .lsr .x .x14 .x10 63, .sub .x .x14 .x12 .x14,
    .mul .x .x9 .x10 .x13, .umulh .x11 .x10 .x13, .logic .and .x .x15 .x14 .x13, .sub .x .x11 .x11 .x15,
    .adds .x .x1 .x1 .x9, .adcs .x .x2 .x2 .x11, .adcs .x .x3 .x3 .x14, .adc .x .x8 .x8 .x14,
    st .x1 o, st .x2 (o + 8), st .x3 (o + 16), st .x8 (o + 24)]

/-! ## A batch -/

/-- The magnitude of `m` in place and its sign mask in `s`. -/
def signMag (m s : Reg) : List Instr :=
  [.lsr .x s m 63, .sub .x s .x12 s, .logic .eor .x m m s, .sub .x m m s]

/-- The matrix `x4`–`x7` as magnitudes and the masks `x14`–`x17`, and the
rows' constants `x13` and `x11`. -/
def mat : List Instr :=
  [.movz .x .x12 0 0] ++ signMag .x4 .x14 ++ signMag .x5 .x15 ++ signMag .x6 .x16 ++ signMag .x7 .x17 ++
  [.logic .and .x .x8 .x4 .x14, .logic .and .x .x9 .x5 .x15, .add .x .x13 .x8 .x9,
    .logic .and .x .x8 .x6 .x16, .logic .and .x .x9 .x7 .x17, .add .x .x11 .x8 .x9]

/-- A batch: the divsteps, the rows, their results, and the counter `x20`. -/
def batch : List Instr :=
  [ld .x1 DSAVE, ld .x2 F, ld .x3 G] ++ VG.Impl.Weierstrass.AArch64.pwords ++ [st .x1 DSAVE] ++ mat ++
  row true TF F G .x4 .x14 .x5 .x15 .x13 ++ row true TG F G .x6 .x16 .x7 .x17 .x11 ++
  row false TU U V .x4 .x14 .x5 .x15 .x13 ++ row false TV U V .x6 .x16 .x7 .x17 .x11 ++
  shift F TF ++ shift G TG ++ [.movz .x .x13 19 0] ++ reduce U TU ++ reduce V TV ++
  [.subImm .x .x20 .x20 1]

/-! ## The start and the end -/

/-- `x7 = 2⁶³ - 1`. -/
def low63 : List Instr := const64 .x7 0x7fffffffffffffff

/-- `x2`–`x5` folded at bit 255 (as 19), below `2²⁵⁵ + 19`, given `x6 = 19`,
`x7 = 2⁶³ - 1` and `x12 = 0`. -/
def fold : List Instr :=
  [.lsr .x .x8 .x5 63, .logic .and .x .x5 .x5 .x7, .mul .x .x8 .x8 .x6,
    .adds .x .x2 .x2 .x8, .adcs .x .x3 .x3 .x12, .adcs .x .x4 .x4 .x12, .adc .x .x5 .x5 .x12]

/-- `x2`–`x5` (below `2²⁵⁵ + 19`) less `p` if not below it, through `x8`–`x11`, `x13`. -/
def freeze : List Instr :=
  [.adds .x .x8 .x2 .x6, .adcs .x .x9 .x3 .x12, .adcs .x .x10 .x4 .x12, .adc .x .x11 .x5 .x12,
    .lsr .x .x13 .x11 63, .logic .and .x .x11 .x11 .x7, .sub .x .x13 .x12 .x13] ++
  [(Reg.x2, Reg.x8), (.x3, .x9), (.x4, .x10), (.x5, .x11)].flatMap fun (x, y) =>
    [.logic .eor .x y y x, .logic .and .x y y .x13, .logic .eor .x x x y]

/-- The output pointer saved; `g = [slot 2] mod p`, `f = p`, `u = 0`, `v = 2⁻⁵⁹⁰`,
`d = 1`, and ten batches to go. -/
def init : List Instr :=
  [.addImm .x .x19 .x1 0, .movz .x .x12 0 0, .movz .x .x6 19 0] ++ low63 ++
  loads (offset 2) .x2 .x3 .x4 .x5 ++ fold ++ freeze ++ stores G .x2 .x3 .x4 .x5 ++
  storeConst F Spec.X25519.P ++ stores U .x12 .x12 .x12 .x12 ++
  storeConst V v0 ++ [.movz .x .x1 1 0, st .x1 DSAVE, .movz .x .x20 10 0]

/-- `[slot 15] ≡ f u`: `u` folded below `2p`, and `2p - u` if `f < 0`; `x1` back. -/
def finish : List Instr :=
  [.movz .x .x12 0 0, .movz .x .x6 19 0] ++ low63 ++
  loads U .x2 .x3 .x4 .x5 ++ fold ++
  -- 2p - u into x8–x11
  const64 .x9 (BitVec.ofNat 64 (2 ^ 64 - 38)) ++ const64 .x10 (BitVec.allOnes 64) ++
  [.subs .x .x8 .x9 .x2, .sbcs .x .x9 .x10 .x3, .sbcs .x .x11 .x10 .x4, .sbc .x .x10 .x10 .x5] ++
  -- the mask of `f`'s sign
  [ld .x13 (F + 24), .lsr .x .x13 .x13 63, .sub .x .x13 .x12 .x13] ++
  [(Reg.x2, Reg.x8), (.x3, .x9), (.x4, .x11), (.x5, .x10)].flatMap (fun (x, y) =>
    [.logic .eor .x y y x, .logic .and .x y y .x13, .logic .eor .x x x y]) ++
  stores (offset 15) .x2 .x3 .x4 .x5 ++ [.addImm .x .x1 .x19 0]

/-- `[slot 15] ≡ [slot 2]^(p - 2)` (mod `p`). -/
def invert : Prog isa :=
  .seq (.block init) (.seq (.loop (.block batch) (.nonzero .x .x20)) (.block finish))

end VG.Impl.Ed25519.AArch64.Divstep
