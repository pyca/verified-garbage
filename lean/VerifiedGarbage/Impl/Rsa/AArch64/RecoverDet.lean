module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Impl.Rsa.AArch64.Crt

/-!
# `vg_rsa_recover_primes_det` on AArch64: SP 800-56B Rev. 2 Appendix C.2

The arguments' header slots, the entry, the exits and `d e` (in the namespace
`Recover`), and `Keys.lean`'s layout at two widths, which the code switches between by
rewriting the header (`setNar`, `setWid`): narrow numbers of
`v = ⌈k / 8⌉ + 1` words and wide ones of `W = 2 v + 2` words, wide array `j`
being narrow arrays `2 j` and `2 j + 1`. Then, without a branch on a
secret (`Proof/Rsa/RecoverDetModel.lean`'s computation):

* `n`, `e`, `d` loaded (narrow), `M = d e` (`Recover.prod`, narrow arrays
  10 and 11: wide array 5);
* `X = M - 1` (wide), and `M ≥ 1`, `X ≥ 1` and'ed into the mask;
* `64 v` halvings (`twosBody`): `u` (from `n - 1`) halved while even, and
  while `x` (narrow, from `X`) is even too, `x` halved and `X` doubled;
* `gcd(u, x)` by `Keys.inverse` modulo the odd `u` (1 if `u = 1`), and
  `a = gcd · X` by `64 v` steps of a bit-serial product (`prodBody`);
* `m = a / n`, `r = a mod n` (wide `divmod`), `m < n` and'ed into the mask;
  `m + 1`, `n - r`, their quotient `q` and remainder (narrow `divmod`),
  the remainder zero and'ed into the mask;
* `b = q + 1`, `b²` (`prodBody`), `b² - 4 n` and its checks;
* its integer square root, two bits at a time (`sqrtBody`, `32 W` steps),
  the remainder zero and'ed into the mask;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask.

Every loop's count is a function of the public `k`; every check is a mask.
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.Recover

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Bignum.Public (sN sK sE sElen sMask sCnt aN aX aR2 aXm aY aOne)

/-! ## The layout -/

/-- Header slots, beside `vg_rsa_public`'s `sN`, `sK`, `sE`, `sElen`,
`sMask` and `sCnt` and the layout's `sStride`: `p` and `q`'s pointers, and
`d`'s pointer and length. -/
def sP : Nat := sFn 0
def sQ : Nat := sFn 5
def sD : Nat := sFn 7
def sDl : Nat := sFn 8
/-- Arrays, after `vg_rsa_public`'s 0 to 7: `e` (8), `d` (9), and `M = d e`
over 10 and 11. -/
def aE : Nat := 8
def aD : Nat := 9
def aM : Nat := 10
/-! ## The entry and the exits -/

/-- The arguments in the header at `scratch` (the third stack argument),
whose base goes in `x0`; then `n` and `n_len` into `x2` and `x3` for
`invalid`. `p_len` and `q_len` are `n_len`. -/
def entry : List Instr :=
  [.ldrSp .x8 16, .str .x .x0 .x8 (8 * sP), .str .x .x2 .x8 (8 * sQ), .str .x .x4 .x8 (8 * sN),
    .str .x .x5 .x8 (8 * sK), .str .x .x6 .x8 (8 * sE), .str .x .x7 .x8 (8 * sElen),
    .ldrSp .x9 0, .str .x .x9 .x8 (8 * sD), .ldrSp .x9 8, .str .x .x9 .x8 (8 * sDl), mov .x0 .x8,
    mov .x2 .x4, mov .x3 .x5]

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [zeroOut sP sK, zeroOut sQ sK, .block [movi .x0 0]]

/-! ## `d e` -/

/-- `M := d e`: `M += e_j d` at word `j`, for each word `j` of `e`. -/
def prod : List (Prog isa) :=
  [zeroA aM, zeroA (aM + 1),
    .block (ws ++ base aE .x5 ++ base aD .x9 ++ base aM .x8 ++
      [mov .x11 .x5, ldh .x3 sElen, .addImm .x .x3 .x3 7, .lsr .x .x13 .x3 3, movi .x7 0]),
    Crt.mulRows]

/-- `x15 :=` the mask of `x9 = 0` (`x9 - 1` borrows). -/
def zeroMask : List Instr := [movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask

end VG.Impl.Rsa.AArch64.Recover

namespace VG.Impl.Rsa.AArch64.RecoverDet

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Bignum.Public (sN sK sE sElen sMask sCnt aN)
open VG.Impl.Rsa.AArch64.Recover (sP sQ sD sDl aE aD aM entry fail prod zeroMask)
open VG.Impl.Rsa.AArch64.InvBatch (batchCount coefMasks4 cnegBody)

/-! ## The widths -/

/-- `w` in `x12` into the header: its slot, the arrays' bases and the
stride. -/
def setW : List Instr :=
  [sth .x12 sW] ++ setBases ++ [.addImm .x .x3 .x12 2, .lsl .x .x3 .x3 3, sth .x3 sStride]

/-- The narrow width `v = ⌈k / 8⌉ + 1` into `x12`. -/
def narW : List Instr := [ldh .x3 sK, .addImm .x .x12 .x3 15, .lsr .x .x12 .x12 3]

/-- The header at the narrow width. -/
def setNar : List Instr := narW ++ setW

/-- The header at the wide width `2 v + 2`. -/
def setWid : List Instr := narW ++ [.add .x .x12 .x12 .x12, .addImm .x .x12 .x12 2] ++ setW

/-! ## Operations on arrays at the header's width -/

/-- `[o] := [a] - [b]`, and `x15` the mask of no borrow. -/
def subA (o a b : Nat) : Prog isa :=
  seqs [.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base a .x16 ++ base b .x17 ++
    base o .x13), countLoop .x14 subBody, .block carryMask]

/-- `[o] := ([a] & x15) + [b]` (`o` neither `a` nor `b`). -/
def addA (o a b : Nat) : Prog isa :=
  .seq (.block (ws ++ [movi .x7 0, mov .x14 .x12, .adds .x .x3 .x7 .x7] ++ base a .x10 ++ base b .x8 ++
    base o .x5)) (countLoop .x14 addMBody)

/-- `x15` all ones. -/
def ones : List Instr := [movi .x7 0, .subImm .x .x15 .x7 1]

/-- `[o] := [a] / 2`, word `w` of `[a]` the bit shifted in. -/
def halfA (o a : Nat) : Prog isa :=
  .seq (.block (ws ++ [mov .x14 .x12] ++ base a .x16 ++ base o .x17)) (countLoop .x14 shrBody)

/-- `[o] := [a]` if `x15` is all ones. -/
def selA (o a : Nat) : Prog isa :=
  .seq (.block (ws ++ [mov .x14 .x12] ++ base a .x16 ++ base o .x17)) Crt.selLoop

/-- `[a] := 2 [a] + C` for the carry flag `C` that `cin` sets (`x7 = 0`),
and `cout` after it. -/
def dblA (a : Nat) (cin cout : List Instr) : Prog isa :=
  seqs [.block (ws ++ [movi .x7 0, mov .x14 .x12] ++ base a .x16 ++ cin), countLoop .x14 shlBody, .block cout]

/-- The carry flag clear. -/
def c0 : List Instr := [.adds .x .x3 .x7 .x7]

/-- The mask in `x15` and'ed into `sMask`. -/
def andMask : List Instr := [ldh .x3 sMask, .logic .and .x .x3 .x3 .x15, sth .x3 sMask]

/-- `[a] := 1` (all its words). -/
def oneA (a : Nat) : List (Prog isa) := [zeroA a, .block (setOneA a)]

/-! ## Arrays

Narrow: `n` (0), one (1), `e` (8) and `d` (9) at first, and working
arrays. Wide: `M = d e` (5), `X` and then `2^k X` (6), the product and the
quotient (7), one (8), temporaries (9), and `n` (4, narrow array 8). -/

def nOne : Nat := 1
def wM : Nat := 5
def wX : Nat := 6
def wA : Nat := 7
def wOne : Nat := 8
def wT : Nat := 9
def wN : Nat := 4

/-! ## `d e - 1` -/

def deMinus : Prog isa :=
  seqs ([.block setWid] ++ oneA wOne ++ [subA wX wM wOne, .block andMask, subA wT wX wOne, .block andMask])

/-! ## Shifts by masked stages -/

/-- The context for a stage over `[j]`: the narrow `v` words, or the wide `W` (`wide`). -/
def ctxOf (wide : Bool) : List Instr := (if wide then setWid else []) ++ ws

/-- `x15 :=` the mask of bit `k` of the shift in header slot `sl`, counted in words (`words`: the
bit count's `⌊/ 64⌋`), and `x7 := 0`. -/
def stageMask (sl : Nat) (words : Bool) (k : Nat) : List Instr :=
  [ldh .x10 sl] ++ (if words then [.lsr .x .x10 .x10 6] else []) ++
    [.lsr .x .x3 .x10 k, movi .x4 1, .logic .and .x .x3 .x3 .x4, movi .x7 0, .sub .x .x15 .x7 .x3]

/-- A word of a masked move: `[x16] := mask ? [x17] : [x16]`; then both pointers down (`up`) or up. -/
def wMove (up : Bool) : List Instr :=
  [ld .x3 .x17, ld .x4 .x16, .logic .eor .x .x3 .x3 .x4, .logic .and .x .x3 .x3 .x15, .logic .eor .x .x4 .x4 .x3,
    st .x4 .x16] ++ (if up then [.subImm .x .x16 .x16 8, .subImm .x .x17 .x17 8] else [next .x16, next .x17])

/-- A word of a masked clear: `[x16] := mask ? 0 : [x16]`; then the pointer down (`up`) or up. -/
def wClear (up : Bool) : List Instr :=
  [ld .x4 .x16, .logic .and .x .x3 .x4 .x15, .logic .eor .x .x4 .x4 .x3, st .x4 .x16] ++
    (if up then [.subImm .x .x16 .x16 8] else [next .x16])

/-- A word of a masked shift by `2^k` bits, up (`up`, the pointer up) or down (the pointer down), the bits
shifted out carried in `x2`. -/
def bWord (up : Bool) (k : Nat) : List Instr :=
  (if up then [ld .x3 .x16, .lsl .x .x4 .x3 (2 ^ k), .logic .orr .x .x4 .x4 .x2, .lsr .x .x2 .x3 (64 - 2 ^ k)]
    else [ld .x3 .x16, .lsr .x .x4 .x3 (2 ^ k), .logic .orr .x .x4 .x4 .x2, .lsl .x .x2 .x3 (64 - 2 ^ k)]) ++
  [.logic .eor .x .x4 .x4 .x3, .logic .and .x .x4 .x4 .x15, .logic .eor .x .x3 .x3 .x4, st .x3 .x16] ++
    (if up then [next .x16] else [.subImm .x .x16 .x16 8])

/-- Word stage `k` of a shift of `[j]` by the words of slot `sl` (`words`: its bits' `⌊/ 64⌋`), up
(`up`) or down by `2^k` words where its bit `k` is set, by masks; only for `2^k < v`, as the shift is
below `v` words. -/
def wstage (j : Nat) (wide up : Bool) (sl : Nat) (words : Bool) (k : Nat) : Prog isa :=
  .seq (.block (setNar ++ ctxOf wide ++ [.subImm .x .x3 .x12 1, .lsr .x .x3 .x3 k]))
    (.ite (.zero .x .x3) (.block setNar) (seqs (if up then [
      .block (ctxOf wide ++ base j .x8 ++ stageMask sl words k ++
        [.lsl .x .x3 .x12 3, .add .x .x16 .x8 .x3, .subImm .x .x16 .x16 8,
          .subImm .x .x17 .x16 (8 * 2 ^ k), .subImm .x .x13 .x12 (2 ^ k)]),
      countLoop .x13 (wMove true),
      .block [movi .x13 (2 ^ k)],
      countLoop .x13 (wClear true),
      .block setNar] else [
      .block (ctxOf wide ++ base j .x16 ++ stageMask sl words k ++
        [.addImm .x .x17 .x16 (8 * 2 ^ k), .subImm .x .x13 .x12 (2 ^ k)]),
      countLoop .x13 (wMove false),
      .block [movi .x13 (2 ^ k)],
      countLoop .x13 (wClear false),
      .block setNar])))

/-- Bit stage `k < 6` of a shift of `[j]` by the bits of slot `sl` (mod 64), up (`up`) or down by `2^k`
bits where its bit `k` is set, by masks: a pass with the bits shifted out carried to the next word. -/
def bstage (j : Nat) (wide up : Bool) (sl : Nat) (k : Nat) : Prog isa := seqs (if up then [
    .block (ctxOf wide ++ base j .x16 ++ stageMask sl false k ++ [mov .x14 .x12, movi .x2 0]),
    countLoop .x14 (bWord true k),
    .block setNar] else [
    .block (ctxOf wide ++ base j .x16 ++ stageMask sl false k ++
      [.lsl .x .x3 .x12 3, .add .x .x16 .x16 .x3, .subImm .x .x16 .x16 8, mov .x14 .x12, movi .x2 0]),
    countLoop .x14 (bWord false k),
    .block setNar])

/-- `[j] := ⌊[j] / 2^t⌋` (`up`: `[j] 2^t` modulo its width) for `t < 64 v` in slot `sl`. -/
def shiftBy (j : Nat) (wide up : Bool) (sl : Nat) : List (Prog isa) :=
  (List.range 9).map (wstage j wide up sl true) ++ (List.range 6).map (bstage j wide up sl)

/-! ## The halvings

`u` in narrow array 2, `x` in 3, the wide `X` in wide array 6. -/

def nU : Nat := 2
def nXn : Nat := 3

/-- Header slots of the halvings' counts: `t₁ = tz(u ∨ x)` and `t₂ = tz(u)`. -/
def sT1 : Nat := sFn 13
def sT2 : Nat := sFn 14

/-- A word of `ctzOr`'s scan: `y = [x16] ∨ [x17]`; where `y ≠ 0` and none was found before (`x6`),
`x5 := 64 i + ctz y` (`x8 = 64 i`). -/
def ctzScan : List Instr :=
  [ld .x3 .x16, ld .x4 .x17, .logic .orr .x .x3 .x3 .x4, .rbit .x .x4 .x3, .clz .x .x4 .x4,
    .add .x .x4 .x4 .x8, .subs .x .x9 .x7 .x3, .adc .x .x9 .x7 .x7, .subImm .x .x9 .x9 1,
    .logic .eor .x .x10 .x6 .x15, .logic .and .x .x10 .x10 .x9, .logic .eor .x .x4 .x4 .x5,
    .logic .and .x .x4 .x4 .x10, .logic .eor .x .x5 .x5 .x4, .logic .orr .x .x6 .x6 .x9,
    .addImm .x .x8 .x8 64, next .x16, next .x17]

/-- `tz([A] ∨ [B])` (narrow, not zero) into slot `sl`: a scan of every word, the first nonzero
word's `64 i + ctz` kept by masks. -/
def ctzOr (A B sl : Nat) : Prog isa := seqs [
  .block (setNar ++ ws ++ base A .x16 ++ base B .x17 ++
    [movi .x7 0, .subImm .x .x15 .x7 1, movi .x5 0, movi .x6 0, movi .x8 0, mov .x14 .x12]),
  countLoop .x14 ctzScan,
  .block [sth .x5 sl]]

/-- The halvings: `t₁ = tz(u ∨ x)`, `t₂ = tz(u)`; `u := u / 2^t₂`, `x := x / 2^t₁` and the wide
`X := X 2^t₁`, which `64 v` steps of halving `u` while even, and `x` (doubling `X`) while both are,
give. -/
def twos : Prog isa := seqs ([.block setNar] ++ oneA nOne ++
  [zeroA nU, subA nU aN nOne, zeroA nXn, copyA nXn (2 * wX), ctzOr nU nXn sT1, ctzOr nU nU sT2] ++
  shiftBy nU false false sT2 ++ shiftBy nXn false false sT1 ++ shiftBy wX true true sT1 ++ [.block setNar])

/-! ## The GCD -/

def gM : Nat := 4
def gX₁ : Nat := 5
def gX₂ : Nat := 6
def gT : Nat := 7

/-- The gcd-only start: `x1`, `x2` saved, `f = m` (its word `n` cleared, word 0 or'ed with 1),
`g = a + (m if a is even)`, `d = 1`, and the batches `x15 := 3 n + 2`. -/
def batchInitG (iF iG iM : Nat) : List (Prog isa) := [
  .block ([.vop (.ins .d2 .v19 0 .x1), .vop (.ins .d2 .v19 1 .x2)] ++ zeroTop iF ++ zeroTop iG ++ base iG .x8 ++
    ([ld .x3 .x8, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1, movi .x7 0, mov .x14 .x12,
      .adds .x .x3 .x7 .x7] : List Instr) ++ base iM .x10 ++ base iG .x5),
  countLoop .x14 addMBody,
  .block [.adc .x .x3 .x7 .x7, st .x3 .x5],
  .block ([movi .x3 1, .vop (.ins .d2 .v18 0 .x3)] ++ base iF .x16 ++
    ([ld .x4 .x16, .logic .orr .x .x4 .x4 .x3, st .x4 .x16] : List Instr) ++ batchCount)]

/-- A gcd-only batch: 59 divsteps and `(f, g) := (u f + v g, q f + r g) / 2^59`. -/
def batchG (iF iG : Nat) : Prog isa := seqs [
  .block saveHi, .block (batchHead iF iG ++ coefMasks4), fgPass iF iG, .block restoreHi]

/-- `[f] := gcd(a, m)` (`|f|` after the batches) for `[g] = a` and `[f] = [m]`. -/
def gcdB (iF iG iM : Nat) : Prog isa :=
  seqs (batchInitG iF iG iM ++ [.loop (batchG iF iG) (.nonzero .x .x15), .block (signMask iF), cnegP iF,
    .block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1,
      .vop (.movi0 .v16), .vop (.movi0 .v17), .vop (.movi0 .v18), .vop (.movi0 .v19), .vop (.movi0 .v20),
      .vop (.movi0 .v21), .vop (.movi0 .v22), .vop (.movi0 .v23), .vop (.movi0 .v24), .vop (.movi0 .v25),
      .vop (.movi0 .v26)]])

/-- `gcd(u, x)` into `u`'s array (by `gcdB` modulo `u`, and 1 for
`u = 1`), and its copy into `y`. -/
def gcd : Prog isa := seqs ([zeroA gM, copyA gM nU] ++ oneA gX₁ ++ [zeroA gX₂,
  .seq (.block (ws ++ [.lsr .x .x3 .x12 21]))
    (.ite (.zero .x .x3) (gcdB nU nXn gM) (inverseBits nXn nU gX₁ gX₂ gM gT))] ++
  eqA gM nOne ++ [.block zeroMask, selA nU nOne, zeroA gT, copyA gT nU])

/-! ## Products by rows -/

/-- Rows `[x8 + 8 i ..] += [x11]_i [x9]` over `x12 - i` words of `[x9]` for each of the `x13` words of
`[x11]`: the product modulo `2^(64 x12)` (`x7 = 0`), the rows' carries into its words `x12` and
`x12 + 1`. -/
def mulRowsLow : Prog isa :=
  .loop (.seq (.block [ld .x1 .x11, next .x11]) (.seq mulAddRow
    (.block [next .x8, .subImm .x .x12 .x12 1, .subImm .x .x13 .x13 1]))) (.nonzero .x .x13)

/-- Words `W` and `W + 1` of the wide array `j` cleared. -/
def clearTop (j : Nat) : List Instr :=
  setWid ++ ws ++ base j .x16 ++ [.lsl .x .x3 .x12 3, .add .x .x16 .x16 .x3, movi .x7 0, st .x7 .x16, st .x7 .x16 8]

/-- `a = gcd · 2^k X` modulo `2^(64 W)` into wide array 7: a row for each of the `v` words of the
gcd (narrow 7) over the low `W - i` words of `X` (wide 6). -/
def aProd : Prog isa := seqs [.block setWid, zeroA wA,
  .block (setNar ++ ws ++ base gT .x5 ++ setWid ++ ws ++ base wX .x9 ++ base wA .x8 ++
    [mov .x11 .x5, .lsr .x .x13 .x12 1, .subImm .x .x13 .x13 1, movi .x7 0]),
  mulRowsLow, .block (clearTop wA ++ setNar)]

/-! ## The divisions -/

def nN : Nat := 2 * wN
def nM1 : Nat := 2
def nD : Nat := 3
def nRem : Nat := 4
def nZ : Nat := 5

/-- A step of long division with its quotient digit: `x := (x 2^64 + u) mod m` (`R2Div`'s
normalized estimate, `quotN` and `quot3N`, from the temporary's `v`, `P`, `d'` and `d'ₗ`), the
digit `q̂ - [x was negative]` into `x1`. -/
def stepQ : Prog isa :=
  seqs [.block R2Div.quotN, .block R2Div.quot3N, R2Div.mulSubU, R2Div.addBack, .block [.add .x .x1 .x1 .x15]]

/-- `⌊[U] / [M]⌋` in place of `[U]` (`x8`, `x13 = L` words) and `[U] mod [M]` into `[R]` (`x11`, `x12 =
w_m` words, `[R]` zero), for `[M]` (`x9`) of `w_m ≥ 4` words, its top word not zero, and the
temporary `[T]` (`x6`): `[R]` from the top `w_m - 1` words of `[U]`, `normN` and `recipN`, then for each
lower word `u` of `[U]`, most significant first, `stepQ`, its digit in place of `u`. The top `w_m - 1`
words of `[U]` are left as they were. -/
def divQN : Prog isa := seqs [
  .block [.sub .x .x14 .x13 .x12, .addImm .x .x14 .x14 1, sth .x14 sCnt, .lsl .x .x3 .x14 3, .add .x .x16 .x8 .x3,
    .subImm .x .x8 .x16 8, mov .x17 .x11, .subImm .x .x12 .x12 1],
  copyWords,
  .block [.addImm .x .x12 .x12 1],
  R2Div.normN,
  R2Div.recipN,
  .loop (seqs [.block [ld .x10 .x8], stepQ,
      .block [st .x1 .x8, .subImm .x .x8 .x8 8, ldh .x13 sCnt, .subImm .x .x13 .x13 1, sth .x13 sCnt]])
    (.nonzero .x .x13)]

/-- `x14` words from `x16` cleared. -/
def clearN : Prog isa := countLoop .x14 [st .x7 .x16, next .x16]

/-- `m` and `r` (wide arrays 7 and 6), and `m < n` and'ed into the mask: `divQN` of `a` (wide 7,
`W` words) by `n`'s `h = v - 1` words (narrow `aN`; its top word not zero), the quotient's top
`h - 1` words cleared. -/
def divA : Prog isa := seqs [.block setWid, zeroA wN, .block setNar, copyA nN aN, .block setWid,
  zeroA wX, zeroA wT,
  .block (setNar ++ ws ++ base aN .x9 ++ setWid ++ ws ++ base wT .x6 ++ base wA .x8 ++ base wX .x5 ++
    [mov .x11 .x5, mov .x13 .x12, .lsr .x .x12 .x12 1, .subImm .x .x12 .x12 2, movi .x7 0]),
  divQN,
  .block (ws ++ base wA .x16 ++ [.lsr .x .x14 .x12 1, .addImm .x .x3 .x14 3, .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3,
    .subImm .x .x14 .x14 3, movi .x7 0]),
  clearN,
  .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base wA .x16 ++ base wN .x17), cmpLoop,
  .block (borrowMask ++ andMask)]

/-- A word of the scan for a number's top nonzero word: where the word at `x16` is not zero,
`x5 :=` its index `x6`. -/
def hiScan : List Instr :=
  [ld .x3 .x16, .subs .x .x4 .x7 .x3, .adc .x .x4 .x7 .x7, .subImm .x .x4 .x4 1,
    .logic .eor .x .x3 .x5 .x6, .logic .and .x .x3 .x3 .x4, .logic .eor .x .x5 .x5 .x3, .addImm .x .x6 .x6 1,
    next .x16]

/-- `m + 1` and `n - r`, their quotient into 3 and remainder into 4, and the
remainder zero and'ed into the mask. -/
def divB : Prog isa := seqs ([.block (setNar ++ ones), zeroA nM1, addA nM1 (2 * wA) nOne, zeroA nD,
  subA nD aN (2 * wX),
  -- The divisor's leading zero words `z` (`x10`), and both shifted up by them.
  .block (ws ++ base nM1 .x16 ++ [movi .x7 0, movi .x5 0, movi .x6 0, mov .x14 .x12]),
  countLoop .x14 hiScan,
  .block [.sub .x .x10 .x12 .x5, .subImm .x .x10 .x10 1, sth .x10 sCnt],
  .block setWid, zeroA wM, zeroA wT, .block setNar, copyA (2 * wM) nD] ++
  (List.range 8).flatMap (fun k => [wstage nM1 false true sCnt false k, wstage wM true true sCnt false k]) ++
  [.block (setNar ++ ws ++ topAt nM1 .x16 ++ [.subImm .x .x16 .x16 8, ld .x3 .x16, movi .x4 1, movi .x7 0,
    .subs .x .x5 .x3 .x4, .adc .x .x5 .x7 .x7, .add .x .x3 .x3 .x4, .sub .x .x3 .x3 .x5, st .x3 .x16]),
  zeroA nRem,
  .block (ws ++ base nM1 .x9 ++ base nRem .x5 ++ setWid ++ ws ++ base wT .x6 ++ base wM .x8 ++
    [mov .x11 .x5, .subImm .x .x13 .x12 2, .lsr .x .x12 .x12 1, .subImm .x .x12 .x12 1, movi .x7 0]),
  divQN, .block setNar, zeroA nD, copyA nD (2 * wM),
  zeroA nZ] ++ eqA nRem nZ ++ [.block andZero])

/-! ## `b² - 4 n` -/

def nB : Nat := 6
def wSq : Nat := 6
def wX4 : Nat := 7

/-- `b = q + 1` (narrow, and its copy), and `b²` into wide array 6. -/
def square : Prog isa := seqs [.block ones, zeroA nB, addA nB nD nOne,
  .block setWid, zeroA wSq,
  .block (ws ++ base wSq .x8 ++ setNar ++ ws ++ base nB .x9 ++ [mov .x11 .x9, mov .x13 .x12, movi .x7 0]),
  Crt.mulRows]

/-- `b² - 4 n` into wide array 7, and `b² ≥ 4 n` and `b² - 4 n ≥ 1` and'ed
into the mask. -/
def minus4n : Prog isa := seqs ([.block setWid, dblA wN c0 [], dblA wN c0 [], subA wX4 wSq wN, .block andMask] ++
  oneA wOne ++ [subA wT wX4 wOne, .block andMask])

/-! ## The square root

By words (`Proof/Bignum/SqrtRem.lean`), as on RISC-V: the radicand `X` (wide 7, `W` words, `k = W / 2`
digits) normalized by `4^c` so that its root's top word `s₀ ≥ 2^63` (`norm`), `s₀` and its remainder by
bit pairs of the top two words (`first`), then a digit a step, estimated from the remainder's top words
by `s₀`'s reciprocal, the remainder `R - q̂ (2 S β + q̂)` kept in place over `X`'s words, and three masked
corrections (`digit`). The root (wide 5) is shifted down by `c`; where `X = 0`, 0 and an exact root. -/

def wS : Nat := 5
/-- The root, narrow, for the factors. -/
def nY : Nat := 4
/-- Header slots: `s₀`'s reciprocal, `c`, the mask of `X = 0`, and `s₀`. -/
def sV : Nat := sFn 9
def sC : Nat := sFn 11
def sZ : Nat := sFn 15
def sS0 : Nat := sFn 14

/-- `X`'s top nonzero word and its index, and whether `X ≠ 0`, by a scan of every word; then
`c₂ = 2 ⌊clz(X) / 2⌋` (0 where `X = 0`) into `sT1`, `c = c₂ / 2` into `sC`, the mask of `X = 0` into
`sZ`; and `X := X 2^c₂`. -/
def norm : Prog isa := seqs ([
  .block (setWid ++ ws ++ base wX4 .x16 ++ [movi .x7 0, movi .x5 0, movi .x6 0, movi .x8 0, movi .x9 0, mov .x14 .x12]),
  countLoop .x14 [ld .x3 .x16, .subs .x .x4 .x7 .x3, .adc .x .x4 .x7 .x7, .subImm .x .x4 .x4 1,
    .logic .eor .x .x13 .x5 .x8, .logic .and .x .x13 .x13 .x4, .logic .eor .x .x5 .x5 .x13,
    .logic .eor .x .x13 .x6 .x3, .logic .and .x .x13 .x13 .x4, .logic .eor .x .x6 .x6 .x13,
    .logic .orr .x .x9 .x9 .x4, .addImm .x .x8 .x8 1, next .x16],
  .block [.clz .x .x3 .x6, .sub .x .x4 .x12 .x5, .subImm .x .x4 .x4 1, .lsl .x .x4 .x4 6, .add .x .x4 .x4 .x3,
    .lsr .x .x4 .x4 1, .lsl .x .x4 .x4 1, .logic .and .x .x4 .x4 .x9, sth .x4 sT1, .lsr .x .x3 .x4 1, sth .x3 sC,
    .subImm .x .x13 .x7 1, .logic .eor .x .x13 .x13 .x9, sth .x13 sZ]] ++
  shiftBy wX4 true true sT1)

/-- A step of the first digit's square root by bit pairs of `T` (`x2:x3`): root `x1`, remainder
`x4:x5`. -/
def pairStep : List Instr :=
  [.lsl .x .x4 .x4 2, .lsr .x .x6 .x5 62, .logic .orr .x .x4 .x4 .x6, .lsl .x .x5 .x5 2, .lsr .x .x6 .x2 62,
    .logic .orr .x .x5 .x5 .x6, .lsl .x .x2 .x2 2, .lsr .x .x6 .x3 62, .logic .orr .x .x2 .x2 .x6, .lsl .x .x3 .x3 2,
    .lsl .x .x1 .x1 1, .lsl .x .x13 .x1 1, movi .x6 1, .logic .orr .x .x13 .x13 .x6, .lsr .x .x17 .x1 63,
    .subs .x .x6 .x5 .x13, .sbcs .x .x13 .x4 .x17, .adc .x .x17 .x7 .x7, .sub .x .x15 .x7 .x17,
    .logic .eor .x .x6 .x6 .x5, .logic .and .x .x6 .x6 .x15, .logic .eor .x .x5 .x5 .x6,
    .logic .eor .x .x13 .x13 .x4, .logic .and .x .x13 .x13 .x15, .logic .eor .x .x4 .x4 .x13,
    .logic .orr .x .x1 .x1 .x17]

/-- The bases of the remainder `R` (`x10`, wide 7) and the root `S` (`x11`, wide 5), `W` (`x12`). -/
def sqBases : List Instr :=
  setWid ++ ws ++ base wX4 .x10 ++ base wS .x9 ++ [mov .x11 .x9, movi .x7 0]

/-- The first digit `s₀ = ⌊√T⌋` of `X`'s top two words `T`, their remainder in their place, `s₀` into
`S`'s word `k - 1` and `sS0`, its reciprocal into `sV`. -/
def first : Prog isa := seqs [
  .block (sqBases ++ [.lsl .x .x3 .x12 3, .add .x .x16 .x10 .x3, .subImm .x .x16 .x16 16, ld .x2 .x16 8, ld .x3 .x16,
    movi .x1 0, movi .x4 0, movi .x5 0, movi .x14 64]),
  countLoop .x14 pairStep,
  .block [st .x5 .x16, st .x4 .x16 8, sth .x1 sS0, .lsr .x .x3 .x12 1, .lsl .x .x3 .x3 3, .add .x .x3 .x11 .x3,
    .subImm .x .x3 .x3 8, st .x1 .x3, mov .x5 .x1, .sub .x .x2 .x7 .x5, .subImm .x .x2 .x2 1, movi .x10 0, movi .x4 1,
    movi .x13 64],
  countLoop .x13 R2Div.divBit,
  .block [sth .x10 sV]]

/-- `x17 :=` the root's lowest digit `S[k - m]` (`m` in `sCnt`), `x16 :=` `x8 + 8`, `x2 := 0`, and the
count `x14 := m + 1`. -/
def rowPtrs : List Instr :=
  [.addImm .x .x16 .x8 8, ldh .x6 sCnt, .lsr .x .x3 .x12 1, .sub .x .x3 .x3 .x6, .lsl .x .x3 .x3 3,
    .add .x .x17 .x11 .x3, movi .x2 0, .addImm .x .x14 .x6 1]

/-- The word of `2 S` from `S`'s word (`x3`) and the previous (`x2`), into `x4`. -/
def twoS : List Instr := [ld .x3 .x17, .lsl .x .x4 .x3 1, .lsr .x .x5 .x2 63, .logic .orr .x .x4 .x4 .x5, mov .x2 .x3]

/-- One word of `q̂ (2 S β + q̂)` subtracted (`q̂` in `x1`, the carry word `x13`). -/
def msBody : List Instr :=
  twoS ++ [.mul .x .x5 .x1 .x4, .umulh .x6 .x1 .x4, .adds .x .x5 .x5 .x13, .adc .x .x6 .x6 .x7,
    ld .x3 .x16, .subs .x .x3 .x3 .x5, st .x3 .x16, .sbc .x .x5 .x7 .x7, .sub .x .x13 .x6 .x5, next .x16, next .x17]

/-- One word of a masked correction: `2 S` masked (`x15`) added, the carry word `x13`. -/
def corBody : List Instr :=
  twoS ++ [.logic .and .x .x4 .x4 .x15, ld .x5 .x16, .adds .x .x5 .x5 .x13, .adc .x .x13 .x7 .x7,
    .adds .x .x5 .x5 .x4, .adc .x .x13 .x13 .x7, st .x5 .x16, next .x16, next .x17]

/-- A correction: where the remainder is negative (`x9`), `+ 2 S β + 2 q̂ - 1` and `q̂ - 1`; `x9` cleared
by a carry out. -/
def correct : Prog isa := seqs [
  .block ([.sub .x .x15 .x7 .x9, .logic .and .x .x4 .x1 .x15, .subImm .x .x5 .x1 1, .logic .and .x .x5 .x5 .x15,
    ld .x3 .x8, .adds .x .x3 .x3 .x4, .adc .x .x13 .x7 .x7, .adds .x .x3 .x3 .x5, .adc .x .x13 .x13 .x7, st .x3 .x8] ++
    rowPtrs),
  countLoop .x14 corBody,
  .block [ld .x3 .x16, .adds .x .x3 .x3 .x13, st .x3 .x16, .adc .x .x4 .x7 .x7, .sub .x .x1 .x1 .x9, movi .x5 1,
    .logic .eor .x .x4 .x4 .x5, .logic .and .x .x9 .x9 .x4]]

/-- A digit (`m` digits so far, in `sCnt`): the estimate `q̂` from the remainder's top three words
halved, by `quotMG` (`β - 1` where their top is at least `s₀`); `q̂ (2 S β + q̂)` off the window at word
`o = W - 2 m - 2` (`x8`); the borrow `x9`; three corrections; `q̂` into `S[k - m - 1]`. -/
def digit : Prog isa := seqs [
  .block [ldh .x8 sCnt, .sub .x .x3 .x12 .x8, .lsl .x .x3 .x3 3, .add .x .x16 .x10 .x3, .subImm .x .x16 .x16 16,
    ld .x2 .x16 16, ld .x3 .x16 8, ld .x4 .x16, .lsl .x .x5 .x2 63, .lsr .x .x6 .x3 1, .logic .orr .x .x2 .x5 .x6,
    .lsl .x .x6 .x3 63, .lsr .x .x4 .x4 1, .logic .orr .x .x3 .x6 .x4, ldh .x5 sS0, .addImm .x .x6 .x0 (8 * sV)],
  .block (R2Div.quotMG ++ [.subs .x .x4 .x2 .x5, .adc .x .x4 .x7 .x7, .sub .x .x4 .x7 .x4, .logic .orr .x .x1 .x14 .x4,
    ldh .x9 sCnt, .lsl .x .x3 .x9 4, .lsl .x .x4 .x12 3, .sub .x .x3 .x4 .x3, .subImm .x .x3 .x3 16,
    .add .x .x8 .x10 .x3,
    .mul .x .x3 .x1 .x1, .umulh .x4 .x1 .x1, ld .x5 .x8, .subs .x .x5 .x5 .x3, st .x5 .x8, .sbc .x .x6 .x7 .x7,
    .sub .x .x13 .x4 .x6] ++ rowPtrs),
  countLoop .x14 msBody,
  .block [ld .x3 .x16, .subs .x .x3 .x3 .x13, st .x3 .x16, .sbc .x .x5 .x7 .x7, .sub .x .x9 .x7 .x5],
  correct, correct, correct,
  .block [ldh .x9 sCnt, .lsr .x .x3 .x12 1, .sub .x .x3 .x3 .x9, .subImm .x .x3 .x3 1, .lsl .x .x3 .x3 3,
    .add .x .x3 .x11 .x3, st .x1 .x3, .addImm .x .x9 .x9 1, sth .x9 sCnt, .lsr .x .x3 .x12 1, .sub .x .x3 .x3 .x9]]

/-- The digits after the first: `k - 1` of them. -/
def digits : Prog isa := .seq (.block (sqBases ++ [movi .x3 1, sth .x3 sCnt])) (.loop digit (.nonzero .x .x3))

/-- The square root: `y = ⌊√X⌋` into narrow 4 (0 where `X = 0`), and `y² = X` and'ed into the mask. -/
def sqrt : Prog isa := seqs ([.block setWid, zeroA wS, norm, first, digits,
  .block (sqBases ++ [mov .x16 .x10, movi .x9 0, mov .x14 .x12]),
  countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16],
  .block ([ldh .x3 sZ, movi .x4 0, .subImm .x .x4 .x4 1, .logic .eor .x .x3 .x3 .x4, .logic .and .x .x9 .x9 .x3] ++
    andZero)] ++
  shiftBy wS true false sC ++
  [.block setNar, zeroA nY, copyA nY (2 * wS),
   .block (ws ++ base nY .x16 ++ [ldh .x15 sZ, movi .x4 0, .subImm .x .x4 .x4 1, .logic .eor .x .x15 .x15 .x4,
     mov .x14 .x12]),
   countLoop .x14 [ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x16, next .x16]])

/-! ## The factors -/

def nP : Nat := 8
def nQ : Nat := 9

def factors : List (Prog isa) := [.block ones, zeroA nP, addA nP nB nY, halfA nP nP, zeroA nQ, subA nQ nB nY,
  halfA nQ nQ] ++ storeA nP sP sK sMask ++ storeA nQ sQ sK sMask ++ [.block retMask]

/-! ## The function -/

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([.block (Keys.head ++ setNar)] ++ loadA aN sN sK ++ loadA aE sE sElen ++
  loadA aD sD sDl ++ prod ++ [deMinus, twos, gcd, aProd, divA, divB, square, minus4n, sqrt] ++ factors)

/-- `vg_rsa_recover_primes_det`. -/
def code : Prog isa := .seq (.block (entry ++ invalid)) (.ite (.zero .x .x9) fail main)

end VG.Impl.Rsa.AArch64.RecoverDet
