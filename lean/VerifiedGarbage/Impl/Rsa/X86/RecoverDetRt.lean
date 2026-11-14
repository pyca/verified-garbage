module

public import VerifiedGarbage.Impl.Rsa.X86.CrtValues
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt
public import VerifiedGarbage.Impl.Rsa.X86.GcdBatchRt
public import VerifiedGarbage.Impl.Rsa.X86.WordModRt
import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Impl.Bignum.X86.CrtRt
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # RSA prime recovery by SP 800-56B Rev. 2 Appendix C.2 at a run-time width (i686)

`RecoverRt`'s working space, arrays and inputs (`loads`, `prod`: `d e` in
the wide array `wM`), then Appendix C.2 by words, without a branch on a secret:

* `x = d e - 1` (`wX`), and whether `d e ≥ 2` (`sOkDE`);
* the odd part `u` of `n - 1` and `gcd(n - 1, x) = 2^k gcd(u, x)` by stages
  (`twos`, `Proof/Bignum/ShiftStages.lean`): with `t = tz(u ∨ x₂)`, word
  stages (`c = 128, …, 1`, where `c < w`) and bit stages (`b = 16, …, 1`),
  each testing whether the low `c` words or `b` bits of `u ∨ x₂` are zero
  and then shifting `u` and `x₂` down and `x₃` up under that mask; then the
  same on `u` alone. Each family is one loop over its sizes, kept in the
  header (`wordStagesL`, `bitStagesL`);
* the GCD of `u` and `x₂` by #4989's fused `(f, g)` batches alone
  (`gcdFused`, `batchG`: `InvBatchRt`'s rows without `(d, e)`, at
  `n = w + 2`);
* `a = (2^k x) gcd(u, x)` modulo `2^(32 W)` by word rows (`aProduct`);
* `m = ⌊a / n⌋` and `r = a mod n` (`divA`): `n` (public) and `a` doubled
  until `n`'s top bit is set (a public count), `WordModRt`'s 3-by-2 steps,
  each storing its quotient digit over the dividend word it brought down
  (`wordDivQ`), and the remainder halved back;
* `b - 1 = (n - r) / (m + 1)` and whether it is exact (`divB`): `D = m + 1`
  and `N = n - r` shifted up by `D`'s leading zeros in `W'` words (word and
  bit stages, under masks), then `wordDivQ`;
* `b²` by word rows (`square`), `b² - 4 n` (`minus4n`);
* its integer square root by words (`sqrt`, Proof/Bignum/SqrtRem.lean):
  `X` normalized under masks, the first digit by bit pairs, then a digit
  per word, each a 3-by-2 estimate and three masked corrections, and the
  root shifted back;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
  check (`RecoverRt.stores`).

Every loop's count is a public length.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Rsa.X86.Keys
open VG.Impl.Bignum.X86

def sMask : Nat := 132
def aN : Nat := 32
def aW : Nat := 37
def nArr : Nat := 44

def wZ : Nat := 0
def wE : Nat := 1
def wD : Nat := 2
def wM : Nat := 3
def wMod : Nat := 4
def wT : Nat := 5
def width (n : Nat) : Nat := 2 * n + 2
def wide (n : Nat) : Nat := 2 * width n + 2

def entry : List Instr := [.mov .eax (.mem (PublicFn.argument 10))] ++
  PublicFn.save ++ [.mov .edi (.reg .eax)]

def failure : Prog isa := seqs [CrtValues.clear 0, CrtValues.clear 2,
  .block [.mov .eax (.imm 0)]]

def prodCount : List Instr := [.mov .esi (.mem (PublicFn.argument 7)),
  .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi)]

end VG.Impl.Rsa.X86.Recover

namespace VG.Impl.Rsa.X86.RecoverRt
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Keys (aM aNM aZero hdr seqs)
open VG.Impl.Rsa.X86.KeyRt (Lay Shape arrPtr bytesB sub3 copy sel half bitOf setOne clrLow eqSFast zeroArrays
  mulMod gcd div load restoreEdi)
open VG.Impl.Rsa.X86.Recover (sMask aN aW nArr wZ wE wD wM wMod wT entry prodCount)

/-- The modulus's length (argument 5) and the working space (argument 10), with `k` words pushed. -/
def lay (shape : Shape) (k : Nat := 0) : Lay := { len := 5 + k, ws := 10 + k, shape, doubling := true }

/-- The numbers modulo `n`. -/
abbrev nar : Lay := lay .narrow
/-- The product and its halvings. -/
abbrev wid : Lay := lay .wide

/-- Narrow array `j`'s wide index: `2 j`. -/
def w (j : Nat) : Nat := 2 * j

/-! ## The numbers -/

def loads : Prog isa := seqs [zeroArrays nar nArr, load nar 4 aN, load nar 6 (w wE), load nar 8 (w wD)]

/-- The top bit of the wide `[wMod]`: the modulus `2^(32 W - 1)` of the product. -/
def setTop : List Instr :=
  arrPtr wid .eax wMod .edx ++ [.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 12),
    .mov .ecx (.imm 0x80000000), .store (at_ .eax 0) .ecx]

def prod : Prog isa := .seq (.block (setTop ++ prodCount)) (mulMod wid wZ wE wD wM wMod wT)

/-! ## The factors -/

/-- `[j]` under the mask into the big-endian bytes at argument `arg`, as many as argument `arg + 1`. -/
def store (arg j : Nat) : Prog isa := seqs [
  sel nar j aZero j sMask,
  .block ([.mov .ebx (.mem (PublicFn.argument arg)), .mov .ecx (.mem (PublicFn.argument (arg + 1)))] ++
    arrPtr nar .esi j .edx ++ [.alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]),
  reverseBytes]

def stores : Prog isa := seqs [store 0 5, store 2 6, .block [.mov .eax (.mem (sc sMask))]]

/-! ## Fused exponentiation and root search -/

/-- Boolean header operations, with zero or one in each input slot. -/
def flagNot (d a : Nat) : Prog isa := .block [
  .mov .eax (.mem (sc a)), .alu .xor .eax (.imm 1), .store (sc d) .eax]

def flagBin (op : AluOp) (d a b : Nat) : Prog isa := .block [
  .mov .eax (.mem (sc a)), .alu op .eax (.mem (sc b)), .store (sc d) .eax]

end VG.Impl.Rsa.X86.RecoverRt

namespace VG.Impl.Rsa.X86.RecoverDetRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Keys (seqs aZero)
open VG.Impl.Rsa.X86.KeyRt (arrPtr bytesB copy sel sub3 half bitOf setOne orOne chain addLow zeroWide eqSFast
  div bits)
open VG.Impl.Rsa.X86.RecoverRt (nar wid flagNot flagBin)

/-! ## Header words

The batched GCD writes the header words 16 to 100, and the division 136 and
140; the flags that live across the GCD are above them. -/

/-- `d e < 1` and `d e - 1 < 1`. -/
def sB0 : Nat := 116
def sB1 : Nat := 120
/-- `d e ≥ 2`. -/
def sOkDE : Nat := 144
/-- `m < n`. -/
def sLt : Nat := 16
/-- `(n - r) mod (m + 1) = 0`. -/
def sExact : Nat := 20
/-- `b² < 4 n`, `b² - 4 n < 1`, and `b² > 4 n`. -/
def sC1 : Nat := 24
def sC2 : Nat := 28
def sOk4 : Nat := 32
/-- The remainder of the square root is zero. -/
def sOk5 : Nat := 52
/-- A loop's count, from a public length. -/
def sK : Nat := 148

/-- The count less one, and ZF if it is zero. -/
def countNext : List Instr := [.mov .eax (.mem (sc sK)), .alu .sub .eax (.imm 1), .store (sc sK) .eax]

/-! ## Arrays

Narrow arrays (`nar`) are numbered as in `RecoverRt`; wide array `j` (`wid`)
is narrow arrays `2 j` and `2 j + 1`. -/

/-- Wide: one, `x`, `2^k x`, a temporary, a zero, the product, `n`, the
remainder and the division's temporary. -/
def wOne : Nat := 9
def wX : Nat := 10
def wX3 : Nat := 13
def wT : Nat := 14
def wOne2 : Nat := 21
def wA : Nat := 17
def wN : Nat := 19
def wR : Nat := 20
def wDt : Nat := 21
/-- Narrow: zero (the low half of the wide zero), `x` halved, one, `u`, a
temporary, `n`. -/
def aZ0 : Nat := 0
def aX2 : Nat := 20
def aOneN : Nat := 22
def aU : Nat := 24
def aTmp : Nat := 30
def aN : Nat := VG.Impl.Rsa.X86.Recover.aN
/-- The GCD's inputs and result. -/
def aGm : Nat := 8
def aGx : Nat := 0
def aG : Nat := 1
/-- After the product: the quotient's low half, one, `m + 1`, `n - r` (then
`b - 1` and `b`), the remainder's low half and the division's remainder and
temporary; the multiplier `b`. -/
def aM : Nat := 34
def aOne1 : Nat := 26
def aM1 : Nat := 28
def aD : Nat := 30
def aRlo : Nat := 40
def aY : Nat := 4
/-- The factors, as `RecoverRt.stores` takes them. -/
def aP : Nat := 5
def aQ : Nat := 6

/-! ## `d e - 1` -/

/-- A wide array zeroed with its extra word, then its low word one. -/
def wideOne (j : Nat) : Prog isa := .seq (zeroWide wid j) (.block (setOne wid j))

def deMinus : Prog isa := seqs [wideOne wOne,
  sub3 wid wX VG.Impl.Rsa.X86.Recover.wM wOne, .block [.store (sc sB0) .ebx],
  sub3 wid wT wX wOne, .block [.store (sc sB1) .ebx],
  flagBin .or sOkDE sB0 sB1, flagNot sOkDE sOkDE]

/-! ## The halvings -/

/-- `u = n - 1`, `x` halved in `aX2` (the low half of `wX`), `2^k x` in `wX3`. -/
def twosInit : Prog isa := seqs [copy nar aOneN aZ0, .block (setOne nar aOneN),
  sub3 nar aU aN aOneN, copy wid wX3 wX]

/-- The header word of a stage's flag: one where the stage shifts. -/
def sStg : Nat := 112

/-- `sStg` one where `ecx` is zero. -/
def flagZero : List Instr :=
  [.mov .eax (.imm 0), .alu .sub .eax (.reg .ecx), .alu .sbb .eax (.reg .eax), .alu .add .eax (.imm 1),
    .store (sc sStg) .eax]

/-- The header word counting a stage's bit shifts. -/
def sBc : Nat := 100

/-- The header word of a bit stage's size `b`. -/
def sB : Nat := 128

/-- The bit stages `b = bmax, bmax / 2, …, bmin` (`b` in `sB`). -/
def bitStagesL (bmax bmin : Nat) (body : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 bmax)), .store (sc sB) .eax])
    (.loop (.seq body (.block [.mov .eax (.mem (sc sB)), .shift .shr .eax 1, .store (sc sB) .eax,
      .alu .cmp .eax (.imm (BitVec.ofNat 32 bmin))])) .ae)

/-- `body` `b ≥ 1` times (`b` in `sB`), counted down in `sBc`. -/
def timesH (body : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.mem (sc sB)), .store (sc sBc) .eax])
    (.loop (.seq body (.block [.mov .eax (.mem (sc sBc)), .alu .sub .eax (.imm 1), .store (sc sBc) .eax])) .ne)

/-- `ecx` the low `b` bits of `eax` (`b` in `sB`): `eax` halved `b` times, then doubled, xor'ed. -/
def lowTest : Prog isa := seqs [
  .block [.mov .ecx (.reg .eax), .mov .edx (.mem (sc sB))],
  .loop (.block [.shift .shr .eax 1, .alu .sub .edx (.imm 1)]) .ne,
  .block [.mov .edx (.mem (sc sB))],
  .loop (.block [.alu .add .eax (.reg .eax), .alu .sub .edx (.imm 1)]) .ne,
  .block [.alu .xor .ecx (.reg .eax)]]

/-- `ecx` the top `b` bits of `eax` (`b` in `sB`), in place: `eax` doubled `b` times, then halved,
xor'ed. -/
def topTest : Prog isa := seqs [
  .block [.mov .ecx (.reg .eax), .mov .edx (.mem (sc sB))],
  .loop (.block [.alu .add .eax (.reg .eax), .alu .sub .edx (.imm 1)]) .ne,
  .block [.mov .edx (.mem (sc sB))],
  .loop (.block [.shift .shr .eax 1, .alu .sub .edx (.imm 1)]) .ne,
  .block [.alu .xor .ecx (.reg .eax)]]

/-- `[aTmp] = [j]` halved `b` times (`b` in `sB`). -/
def downBitsH (j : Nat) : Prog isa :=
  .seq (copy nar aTmp j) (timesH (.seq (.block [.mov .ebx (.imm 0)]) (half nar aTmp)))

/-- A bit stage of `twos`, its size from `sB`. -/
def stageBH (joint : Bool) : Prog isa := seqs ([
  .block (arrPtr nar .esi aU .edx ++ arrPtr nar .ebp (if joint then aX2 else aU) .edx ++
    [.mov .eax (.mem (at_ .esi 0)), .alu .or .eax (.mem (at_ .ebp 0))]),
  lowTest, .block flagZero,
  downBitsH aU, sel nar aU aU aTmp sStg] ++
  (if joint then [downBitsH aX2, sel nar aX2 aX2 aTmp sStg,
    .seq (copy wid wT wX3) (timesH (chain wid .adc wT wT wT false)), sel wid wX3 wX3 wT sStg] else []))

/-- `[j] := [j] 2^b` (wide, `b` in `sB`) where `sStg`. -/
def upBitsSelH (j : Nat) : Prog isa :=
  seqs [copy wid wT j, timesH (chain wid .adc wT wT wT false), sel wid j j wT sStg]

/-- `[j] := [j] / 2^b` (wide, `b` in `sB`) where `sStg`. -/
def downBitsSelH (j : Nat) : Prog isa :=
  seqs [copy wid wT j, timesH (.seq (.block [.mov .ebx (.imm 0)]) (half wid wT)), sel wid j j wT sStg]

/-- The header word of a word stage's size, `4 c`. -/
def sC4 : Nat := 120

/-- The word stages `c = cmax, cmax / 2, …, 1` (`4 c` in `sC4`), `body` where `4 c` is below `limit`'s
`eax` (a public branch). -/
def wordStagesL (cmax : Nat) (limit : List Instr) (body : Prog isa) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 (4 * cmax))), .store (sc sC4) .eax])
    (.loop (seqs [.block (limit ++ [.mov .ecx (.mem (sc sC4)), .alu .cmp .ecx (.reg .eax)]),
      .ite .b body (.block []),
      .block [.mov .eax (.mem (sc sC4)), .shift .shr .eax 1, .store (sc sC4) .eax, .alu .cmp .eax (.imm 4)]]) .ae)

/-- `ecx` the OR of the low `c` words of `[a]` and `[b]` (`4 c` in `sC4`). -/
def orLowH (a b : Nat) : Prog isa :=
  .seq (.block (arrPtr nar .esi a .edx ++ arrPtr nar .ebp b .edx ++ [.mov .ecx (.imm 0), .mov .edx (.mem (sc sC4))]))
    (.loop (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .or .ecx (.mem (at_ .ebp 0)), .alu .add .esi (.imm 4),
      .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne)

/-- The words of `[src]` (layout `L`) from word `c` on to `[dst]` from word `d` on, `cnt` bytes
(`[dst]` cleared first); `c`, `d`: zero or the stage's `4 c` (`sC4`). -/
def moveH (L : VG.Impl.Rsa.X86.KeyRt.Lay) (src dst : Nat) (srcOff dstOff : Bool) : Prog isa := seqs [zeroWide L dst,
  .block (arrPtr L .esi src .edx ++ (if srcOff then [.mov .edx (.mem (sc sC4)), .alu .add .esi (.reg .edx)] else []) ++
    arrPtr L .ebp dst .edx ++ (if dstOff then [.mov .edx (.mem (sc sC4)), .alu .add .ebp (.reg .edx)] else []) ++
    bytesB L .edx ++ [.mov .eax (.mem (sc sC4)), .alu .sub .edx (.reg .eax)]),
  .loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
    .alu .add .ebp (.imm 4), .alu .sub .edx (.imm 4)]) .ne]

/-- A word stage of `twos`, its size from `sC4`. -/
def stageWH (joint : Bool) : Prog isa :=
  seqs ([orLowH aU (if joint then aX2 else aU), .block flagZero, moveH nar aU aTmp true false, sel nar aU aU aTmp sStg] ++
    (if joint then [moveH nar aX2 aTmp true false, sel nar aX2 aX2 aTmp sStg, moveH wid wX3 wT false true,
      sel wid wX3 wX3 wT sStg] else []))

def stages (joint : Bool) : List (Prog isa) :=
  [wordStagesL 128 (bytesB nar .eax) (stageWH joint), bitStagesL 16 1 (stageBH joint)]

/-- The halvings by stages: `t = tz(u ∨ x₂)` off `u` and `x₂` and onto `x₃`, then the rest of
`tz u` off `u`. -/
def twos : Prog isa := seqs ([twosInit] ++ stages true ++ stages false)

/-! ## The GCD -/

def gcdSet : Prog isa := seqs [copy nar aGm aU, copy nar aGx aX2]

section
open VG.Impl.Rsa.X86.InvBatchRt (Ref Term slots halfSlot win sMu fgArr fgSz row coefMasks scatter gather nBytes
  selIn maskAt)
open VG.Impl.Weierstrass.X86.Inv (wordSteps)
open VG.Impl.Weierstrass.X86 (setConst decCounter testCounter)

/-- `4 n` for the fused rows' `n = w + 2` (even). -/
def gN : List Instr := bytesB nar .eax ++ [.alu .add .eax (.imm 8), .store (sc halfSlot) .eax]

/-- A batch of the GCD alone (#4989's fused `f, g` rows, without `d, e`), from the half `h` of the
elements to the other. -/
def batchG (h : Bool) : Prog isa :=
  let i := if h then 0 else 8
  let o := if h then 8 else 0
  let u : Term := ⟨i, win + 12, sMu⟩
  let v : Term := ⟨i + 4, win + 16, sMu + 4⟩
  let q : Term := ⟨i, win + 20, sMu + 8⟩
  let r : Term := ⟨i + 4, win + 24, sMu + 12⟩
  seqs [
    .block (VG.Impl.Rsa.X86.InvBatchRt.ptr wid .ebx { arr := fgArr, byte := fgSz } .edx ++
      [.mov .eax (.mem (at_ .ebx i)), .store (sc (win + 4)) .eax, .mov .eax (.mem (at_ .ebx (i + 4))),
       .store (sc (win + 8)) .eax] ++ setConst 2 (win + 12) (1 + 2 ^ 96)),
    wordSteps win 30,
    .block coefMasks,
    row wid false fgArr fgSz o [u, v] [u, v],
    row wid false fgArr fgSz (o + 4) [q, r] [q, r]]

/-- `gcd(m, x)` (`m = [aGm]` odd, `x = [aGx]`) into `[aG]`: `f = m`, `g = x + (m if x is even)`
interleaved, an odd number (at least `3 (w + 2)`) of fused batches, `|f|`. -/
def gcdFused : Prog isa := seqs [
  .block (slots wid ++ gN),
  zeroWide wid 7, copy nar 14 aGm, zeroWide wid 8, copy nar 16 aGx, zeroWide wid 9,
  .block (VG.Impl.Rsa.X86.GcdBatch.evenMask (VG.Impl.Rsa.X86.InvBatchRt.offset 0 0)),
  selIn wid { arr := 9 } { arr := 7 } (nBytes .edi 0),
  VG.Impl.Rsa.X86.InvBatchRt.chain wid .adc { arr := 8 } { arr := 8 } { arr := 9 } (nBytes .edx 1),
  scatter wid fgArr fgSz 0 { arr := 7 }, scatter wid fgArr fgSz 4 { arr := 8 },
  .block [.mov .eax (.imm 1), .store (sc win) .eax],
  .block (bytesB nar .eax ++ [.shift .shr .eax 2, .mov .ecx (.reg .eax), .alu .add .eax (.reg .ecx),
    .alu .add .eax (.reg .ecx), .alu .add .eax (.imm 6), .shift .shr .eax 1, .store (sc 100) .eax]),
  .loop (seqs [batchG true, batchG false,
    .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi,
      testCounter]]) .ne,
  batchG true,
  gather wid fgArr fgSz 8 { arr := 14 },
  zeroWide wid 12, VG.Impl.Rsa.X86.InvBatchRt.chain wid .sbb { arr := 12 } { arr := 12 } { arr := 14 } (nBytes .edx 0),
  .block (maskAt wid { arr := 14, half := 1 } ++ [.alu .xor .ecx (.imm (-1))]),
  selIn wid { arr := 12 } { arr := 14 } (nBytes .edi 0),
  copy nar aG 24, zeroWide nar aZero]

end

/-! ## Products: `[a] += [y] [x]` by the `32 w` bits of the narrow `[y]`,
`[x]` doubled at each, through `[t]`, with `[z]` zero (wide). -/

open VG.Impl.Rsa.X86.WordModRt (oJ) in
/-- Row `j` (header word `oJ`): `[o] += [a] b_j 2^(32 j)` over `W + 1` words; `w` rows (the narrow
words of `[b]`). -/
def rowW (o a b : Nat) : Prog isa := seqs [
  .block (arrPtr wid .ebx b .edx ++ [.mov .eax (.mem (sc oJ)), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .ebx (.reg .eax), .mov .ecx (.mem (at_ .ebx 0))] ++ arrPtr wid .ebp o .edx ++
    [.alu .add .ebp (.reg .eax)] ++ arrPtr wid .esi a .edx ++ bytesB wid .edi ++ [.mov .ebx (.imm 0)]),
  .loop (.block [.mov .eax (.mem (at_ .esi 0)), .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
    .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0), .store (at_ .ebp 0) .eax, .mov .ebx (.reg .edx),
    .alu .add .esi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]) .ne,
  .block ([.store (at_ .ebp 0) .ebx] ++ VG.Impl.Rsa.X86.KeyRt.restoreEdi wid ++
    [.mov .eax (.mem (sc oJ)), .alu .add .eax (.imm 1), .store (sc oJ) .eax] ++
    bytesB nar .ecx ++ [.shift .shr .ecx 2, .alu .cmp .eax (.reg .ecx)])]

open VG.Impl.Rsa.X86.WordModRt (oJ) in
/-- `a = 2^k x gcd(u, x)` modulo `2^(32 W)`: the GCD's result (`w` words) times `wX3`, by rows, then
the words from `W` on cleared. -/
def aProduct : Prog isa := seqs [zeroWide wid wT, copy nar (2 * wT) aG,
  zeroWide wid wA, zeroWide wid (wA + 1), .block [.mov .eax (.imm 0), .store (sc oJ) .eax],
  .loop (rowW wA wX3 wT) .ne, zeroWide wid (wA + 1),
  .block (arrPtr wid .eax wA .edx ++ bytesB wid .ecx ++ [.alu .add .eax (.reg .ecx), .mov .ecx (.imm 0),
    .store (at_ .eax 0) .ecx, .store (at_ .eax 4) .ecx])]

/-! ## The divisions -/

/-- `n` wide, its extra word zero: the wide `wN` zeroed, then its low half `n`. -/
def wideN : Prog isa := .seq (zeroWide wid wN) (copy nar (2 * wN) aN)

/-- The header words of `divA`'s shift `z` and of a step's quotient digit. -/
def sZ : Nat := 104
def sQd : Nat := 108
/-- The argument holding `n`'s length. -/
def nl : Nat := 5

/-- `ZF` clear where the top bit of `n`'s word `W' - 1` (`W' = ⌈n_len / 4⌉`) is set. -/
def topBit : List Instr :=
  VG.Impl.Rsa.X86.WordModRt.topPtr wid nl .ebx wN 1 .ecx ++
    [.mov .eax (.mem (at_ .ebx 0)), .alu .test .eax (.imm (BitVec.ofNat 32 0x80000000))]

/-- `n` and the dividend (`W + 1` words of `wA`) doubled until `n`'s top bit is set, counted in `sZ`
(public: `n` is). -/
def normA : Prog isa := seqs [
  .block ([.mov .eax (.imm 0), .store (sc sZ) .eax] ++ topBit),
  .ite .ne (.block [])
    (.loop (seqs [chain wid .adc wN wN wN false, chain wid .adc wA wA wA true,
      .block ([.mov .eax (.mem (sc sZ)), .alu .add .eax (.imm 1), .store (sc sZ) .eax] ++ topBit)]) .e)]

/-- `[wR]` halved `sZ` times. -/
def unnormA : Prog isa := seqs [
  .block [.mov .eax (.mem (sc sZ)), .alu .test .eax (.reg .eax)],
  .ite .e (.block [])
    (.loop (seqs [.block [.mov .ebx (.imm 0)], half wid wR,
      .block [.mov .eax (.mem (sc sZ)), .alu .sub .eax (.imm 1), .store (sc sZ) .eax]]) .ne)]

open VG.Impl.Rsa.X86.WordModRt hiding seqs in
/-- A step of `wordMod`, its quotient digit (`q̂`, less one where the step adds `m` back) into the
header word `sQd`. -/
def stepQ (ml r m t : Nat) : Prog isa :=
  seqs [.block (topPtr wid ml .ebx r 3 .ecx ++ topWords ++ R2Words.quot h0 ++ R2Words.refine3 h0),
    mulSub wid ml r m t,
    .block (arrPtr wid .ebp t .edx ++ width4 ml .eax ++ [.alu .add .ebp (.reg .eax), .mov .eax (.mem (at_ .ebp 0)),
      .alu .add .eax (.reg .eax), .alu .sbb .eax (.reg .eax), .alu .add .eax (.mem (sc oQ)), .store (sc sQd) .eax]),
    addBack wid ml m t, copyBack wid ml r t]

open VG.Impl.Rsa.X86.WordModRt hiding seqs in
/-- `digitStep`, the digit stored over the dividend's word it brought down. -/
def digitStepQ (ml x r m t : Nat) : Prog isa := seqs [
  .block (arrPtr wid .ebx x .edx ++ [.mov .eax (.mem (sc oSteps)), .alu .sub .eax (.imm 1), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .ebx (.reg .eax), .mov .eax (.mem (at_ .ebx 0)), .store (sc oDig) .eax]),
  stepQ ml r m t,
  .block (arrPtr wid .ebx x .edx ++ [.mov .eax (.mem (sc oSteps)), .alu .sub .eax (.imm 1), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .ebx (.reg .eax), .mov .eax (.mem (sc sQd)), .store (at_ .ebx 0) .eax]),
  .block [.mov .eax (.mem (sc oSteps)), .alu .sub .eax (.imm 1), .store (sc oSteps) .eax]]

open VG.Impl.Rsa.X86.WordModRt hiding seqs in
/-- `WordModRt.seed` for a dividend of `W + 1` words (`extra`) or `W`. -/
def seedX (ml x r : Nat) (extra : Bool) : Prog isa := seqs [
  zeroWide wid r,
  .block (arrPtr wid .esi x .edx ++ bytesB wid .ecx ++ (if extra then [.alu .add .ecx (.imm 4)] else []) ++
    [.alu .add .esi (.reg .ecx)] ++ width4 ml .ecx ++
    [.alu .sub .ecx (.imm 4), .alu .sub .esi (.reg .ecx)] ++ arrPtr wid .ebp r .edx ++
    width4 ml .edi ++ [.alu .sub .edi (.imm 4)]),
  .ite .e (.block []) (.loop (.block [.mov .eax (.mem (at_ .esi 0)), .store (at_ .ebp 0) .eax, .alu .add .esi (.imm 4),
    .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]) .ne),
  .block (VG.Impl.Rsa.X86.KeyRt.restoreEdi wid ++ bytesB wid .eax ++ (if extra then [.alu .add .eax (.imm 4)] else []) ++
    [.shift .shr .eax 2] ++ width4 ml .ecx ++
    [.shift .shr .ecx 2, .alu .sub .eax (.reg .ecx), .alu .add .eax (.imm 1), .store (sc oSteps) .eax])]

open VG.Impl.Rsa.X86.WordModRt hiding seqs in
/-- `[x] := [x] / [m]` (its words below the steps' count) and `[r] = [x] mod [m]`, for `x` of `W + 1`
words (`extra`) or `W`, and a normalized `m`. -/
def wordDivQ (ml x r m t : Nat) (extra : Bool) : Prog isa := seqs [.block (orTop wid ml m), recip wid,
  seedX ml x r extra,
  .loop (digitStepQ ml x r m t) .ne]

open VG.Impl.Rsa.X86.WordModRt (width4) in
/-- The quotient's words from `W - W' + 2` to `W + 1` (the dividend's top words, which the steps
leave) cleared. -/
def clearQTop : Prog isa := seqs [
  .block (arrPtr wid .esi wA .edx ++ bytesB wid .eax ++ [.alu .add .esi (.reg .eax)] ++ width4 nl .edx ++
    [.alu .sub .esi (.reg .edx), .alu .add .esi (.imm 8)]),
  .loop (.block [.mov .eax (.imm 0), .store (at_ .esi 0) .eax, .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne]

/-- `m` and `r`, and whether `m < n`: by word steps, after doubling `n` and `a` until `n`'s top bit
is set. -/
def divA : Prog isa := seqs [wideN, normA, wordDivQ nl wA wR wN wDt true, clearQTop, unnormA, wideN,
  sub3 wid wT wA wN, .block [.store (sc sLt) .ebx]]

/-- `divB`'s wide arrays: the divisor `D 2^s`, the dividend `N 2^s` (its quotient after), the
remainder. -/
def wDD : Nat := 7
def wNN : Nat := 8
def wRB : Nat := 6

open VG.Impl.Rsa.X86.WordModRt (width4) in
/-- A word stage of `D`'s leading zeros, its size from `sC4`: where `D`'s top `c` of `W'` words are
zero, `D` and `N` shifted up by them. -/
def stageDWH : Prog isa := seqs [
  .seq (.block (arrPtr wid .esi wDD .edx ++ width4 nl .edx ++ [.alu .add .esi (.reg .edx), .mov .edx (.mem (sc sC4)),
      .alu .sub .esi (.reg .edx), .mov .ecx (.imm 0)]))
    (.loop (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne),
  .block flagZero, moveH wid wDD wT false true, sel wid wDD wDD wT sStg, moveH wid wNN wT false true,
  sel wid wNN wNN wT sStg]

/-- A bit stage of `D`'s leading zeros, its size from `sB`. -/
def stageDBH : Prog isa := seqs [
  .block (VG.Impl.Rsa.X86.WordModRt.topPtr wid nl .esi wDD 1 .edx ++ [.mov .eax (.mem (at_ .esi 0))]),
  topTest, .block flagZero, upBitsSelH wDD, upBitsSelH wNN]

/-- `m + 1`, `n - r`; `D = m + 1` and `N = n - r` shifted up by `D`'s leading zeros in `W'` words
(stages, under masks), then `N / D` by word steps: `b - 1`, and whether the remainder (times `2^s`)
is zero. -/
def divB : Prog isa := seqs ([copy nar aOne1 aZero, .block (setOne nar aOne1), sub3 nar aD aN aRlo,
  chain nar .adc aM1 aM aOne1 false,
  zeroWide wid wDD, copy nar (2 * wDD) aM1, zeroWide wid wNN, copy nar (2 * wNN) aD] ++
  [wordStagesL 128 (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax) stageDWH, bitStagesL 16 1 stageDBH] ++
  [wordDivQ nl wNN wRB wDD wDt false, copy nar aD (2 * wNN), eqSFast nar sExact (2 * wRB) aZero])

/-! ## `b² - 4 n` -/

/-- `b` (narrow, in `aD`) and `b²` (wide, in `wA`) by rows. -/
def square : Prog isa := seqs [chain nar .adc aD aD aOne1 false,
  VG.Impl.Rsa.X86.WordModRt.mulWide nar (2 * wA) aD aD]

/-- `b² - 4 n` in `wR`, and whether `b² > 4 n`. -/
def minus4n : Prog isa := seqs [chain wid .adc wN wN wN false, chain wid .adc wN wN wN false,
  wideOne wOne2, sub3 wid wR wA wN, .block [.store (sc sC1) .ebx],
  sub3 wid wT wR wOne2, .block [.store (sc sC2) .ebx],
  flagBin .or sOk4 sC1 sC2, flagNot sOk4 sOk4]

/-! ## The square root by words

`X` (wide `sqZ`, below `2^(32 H)`, `H = 2 W'`) normalized in place to `X' = X 4^c` with its word
`H - 1` at least `2^30` (stages of words, then of even bits, under masks; `X = 0` made one); its
first digit `s₀` (from the top two words, by bit pairs), then `W' - 1` digits: a 3-by-2 estimate
`q̂` of `⌊R / 2⌋`'s top words by `s`'s top two (`R2Words.quot`, `refine3`), `T = R - q̂ D` with
`D = 2 s β + q̂` aligned at the step's word `m`, three masked corrections, `D := 2 s' β^m`. The
root `D / 2`, shifted back by `c`. -/

def sqZ : Nat := wR
def sqD : Nat := 7
def sqT : Nat := wT
def sCt : Nat := 96
def sKw : Nat := 104
def sZb : Nat := 108
def sZf : Nat := 124
def hTl : Nat := 36
def hTa : Nat := 40
def hTb : Nat := 44
def hCnt : Nat := 48

open VG.Impl.Rsa.X86.WordModRt (width4 topPtr oD oD1 oU0 oU2 oQ h0) in
/-- `r` at word `2 W' - i` of the wide array `j`, through `t`. -/
def topH (r : Reg) (j i : Nat) (t : Reg) : List Instr :=
  arrPtr wid r j t ++ width4 nl t ++
    [.alu .add r (.reg t), .alu .add r (.reg t), .alu .sub r (.imm (BitVec.ofNat 32 (4 * i)))]

open VG.Impl.Rsa.X86.WordModRt (width4) in
/-- `X`'s words `H` to `W - 1` cleared. -/
def clearAboveH : Prog isa := seqs [
  .block (topH .esi sqZ 0 .edx ++ bytesB wid .edx ++ width4 nl .eax ++
    [.alu .sub .edx (.reg .eax), .alu .sub .edx (.reg .eax)]),
  .ite .e (.block []) (.loop (.block [.mov .eax (.imm 0), .store (at_ .esi 0) .eax, .alu .add .esi (.imm 4),
    .alu .sub .edx (.imm 4)]) .ne)]

/-- `sZf := [X = 0]`, `X := X + [X = 0]`; the shifts' counts zero. -/
def zeroX : Prog isa := seqs [
  .seq (.block (arrPtr wid .esi sqZ .edx ++ bytesB wid .edx ++ [.mov .ecx (.imm 0)]))
    (.loop (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne),
  .block (flagZero ++ [.mov .eax (.mem (sc sStg)), .store (sc sZf) .eax] ++ arrPtr wid .esi sqZ .edx ++
    [.alu .or .eax (.mem (at_ .esi 0)), .store (at_ .esi 0) .eax, .mov .eax (.imm 0), .store (sc sKw) .eax,
      .store (sc sZb) .eax])]

open VG.Impl.Rsa.X86.WordModRt (width4) in
open VG.Impl.Rsa.X86.WordModRt (width4) in
/-- A word stage of `X`'s normalization, its size from `sC4`: where `X`'s top `c` of `H` words are
zero, `X` up by them and `K += c`. -/
def stageXWH : Prog isa := seqs [
  .seq (.block (arrPtr wid .esi sqZ .edx ++ width4 nl .edx ++ [.alu .add .esi (.reg .edx), .alu .add .esi (.reg .edx),
      .mov .edx (.mem (sc sC4)), .alu .sub .esi (.reg .edx), .mov .ecx (.imm 0)]))
    (.loop (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne),
  .block (flagZero ++ [.mov .edx (.imm 0), .alu .sub .edx (.mem (sc sStg)), .mov .eax (.mem (sc sC4)),
    .shift .shr .eax 2, .alu .and .edx (.reg .eax), .alu .add .edx (.mem (sc sKw)), .store (sc sKw) .edx]),
  moveH wid sqZ wT false true, sel wid sqZ sqZ wT sStg]

open VG.Impl.Rsa.X86.WordModRt (width4) in
def normX : Prog isa := seqs ([clearAboveH, zeroX] ++
  [wordStagesL 256 (width4 nl .eax ++ [.alu .add .eax (.reg .eax)]) stageXWH, bitStagesL 16 2 (seqs [
    .block (topH .esi sqZ 1 .edx ++ [.mov .eax (.mem (at_ .esi 0))]), topTest,
    .block (flagZero ++ [.mov .edx (.imm 0), .alu .sub .edx (.mem (sc sStg)), .alu .and .edx (.mem (sc sB)),
      .alu .add .edx (.mem (sc sZb)), .store (sc sZb) .edx]),
    upBitsSelH sqZ])])

/-- A bit pair of the first digit: `rem := 4 rem + ` the top two bits of `T` (`ebp`, `hTl`),
`T := 4 T`, and the root `ebx := 2 ebx + 1` with `rem := rem - (4 ebx + 1)` if that does not borrow
(`rem` in `esi:ecx`). -/
def isqBody : List Instr := [
  .mov .eax (.reg .ecx), .shift .shr .eax 30, .alu .add .esi (.reg .esi), .alu .add .esi (.reg .esi),
  .alu .add .esi (.reg .eax),
  .mov .eax (.reg .ebp), .shift .shr .eax 30, .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
  .alu .add .ecx (.reg .eax),
  .mov .edx (.mem (sc hTl)), .mov .eax (.reg .edx), .shift .shr .eax 30, .alu .add .ebp (.reg .ebp),
  .alu .add .ebp (.reg .ebp), .alu .add .ebp (.reg .eax), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx),
  .store (sc hTl) .edx,
  .mov .eax (.reg .ebx), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .or .eax (.imm 1),
  .store (sc hTa) .eax, .mov .edx (.reg .ebx), .shift .shr .edx 30, .store (sc hTb) .edx,
  .alu .cmp .ecx (.reg .eax), .mov .eax (.reg .esi), .alu .sbb .eax (.reg .edx), .alu .sbb .eax (.reg .eax),
  .alu .xor .eax (.imm (-1)),
  .mov .edx (.mem (sc hTa)), .alu .and .edx (.reg .eax), .store (sc hTa) .edx,
  .mov .edx (.mem (sc hTb)), .alu .and .edx (.reg .eax),
  .alu .and .eax (.imm 1), .alu .add .ebx (.reg .ebx), .alu .add .ebx (.reg .eax),
  .mov .eax (.mem (sc hTa)), .alu .sub .ecx (.reg .eax), .alu .sbb .esi (.reg .edx),
  .mov .eax (.mem (sc hCnt)), .alu .sub .eax (.imm 1), .store (sc hCnt) .eax]

open VG.Impl.Rsa.X86.WordModRt (topPtr oD recip) in
/-- `s₀`, the root of `X'`'s top two words, its remainder in their place; `D`'s words `W' - 1` and `W'`
from `2 s₀`; `d = s₀` and its reciprocal. -/
def firstX : Prog isa := seqs [zeroWide wid sqD,
  .block (topH .eax sqZ 1 .edx ++ [.mov .ebp (.mem (at_ .eax 0)), .alu .sub .eax (.imm 4), .mov .edx (.mem (at_ .eax 0)),
    .store (sc hTl) .edx, .mov .ebx (.imm 0), .mov .ecx (.imm 0), .mov .esi (.imm 0), .mov .eax (.imm 32),
    .store (sc hCnt) .eax]),
  .loop (.block isqBody) .ne,
  .block (topH .eax sqZ 1 .edx ++ [.store (at_ .eax 0) .esi, .alu .sub .eax (.imm 4), .store (at_ .eax 0) .ecx,
    .store (sc oD) .ebx] ++ topPtr wid nl .eax sqD 1 .edx ++ [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edx),
    .store (at_ .eax 0) .edx, .mov .edx (.reg .ebx), .shift .shr .edx 31, .store (at_ .eax 4) .edx]),
  recip wid]

open VG.Impl.Rsa.X86.WordModRt (width4) in
/-- `esi` at `Z`'s word `2 m`, `ebx` at `D`'s word `m`, `edx = 4 L` for `L = W' - m + 2`,
`m = sCt - 1`. -/
def winPtrs : List Instr :=
  [.mov .eax (.mem (sc sCt)), .alu .sub .eax (.imm 1), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)] ++
  arrPtr wid .esi sqZ .edx ++ [.alu .add .esi (.reg .eax), .alu .add .esi (.reg .eax)] ++
  arrPtr wid .ebx sqD .edx ++ [.alu .add .ebx (.reg .eax)] ++
  width4 nl .edx ++ [.alu .sub .edx (.reg .eax), .alu .add .edx (.imm 8)]

/-- `(p[k + 1], p[k]) / 2` modulo `2^32` into `eax`, through `ecx`. -/
def halfW (p : Reg) (k : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ p (4 * k + 4))), .alu .and .ecx (.imm 1), .shift .ror .ecx 1, .mov .eax (.mem (at_ p (4 * k))),
    .shift .shr .eax 1, .alu .or .eax (.reg .ecx)]

open VG.Impl.Rsa.X86.WordModRt (oD1 oU0 oU2 h0) in
/-- `q̂` into `oQ`: the 3-by-2 estimate of `⌊R / 2⌋`'s top three words by `s`'s top two. -/
def estX : List Instr :=
  winPtrs ++ [.alu .add .esi (.reg .edx), .alu .sub .esi (.imm 16), .alu .add .ebx (.reg .edx), .alu .sub .ebx (.imm 16)] ++
  halfW .esi 0 ++ [.store (sc oU0) .eax] ++ halfW .ebx 0 ++ [.store (sc oD1) .eax] ++
  halfW .esi 2 ++ [.store (sc oU2) .eax, .mov .edx (.reg .eax)] ++ halfW .esi 1 ++
  [.mov .ebp (.reg .eax), .mov .eax (.reg .edx)] ++ R2Words.quot h0 ++ R2Words.refine3 h0

open VG.Impl.Rsa.X86.WordModRt (oQ) in
/-- `D`'s word `m := q̂`; `T := R - q̂ D` into `sqT`, `L + 1` words. -/
def mulSubX : Prog isa := seqs [
  .block (winPtrs ++ [.mov .ecx (.mem (sc oQ)), .store (at_ .ebx 0) .ecx] ++ arrPtr wid .ebp sqT .eax ++
    [.mov .eax (.imm 0), .store (at_ .ebp 0) .eax, .mov .edi (.reg .edx)]),
  .loop (.block R2Words.subBody) .ne,
  .block ([.mov .edx (.mem (at_ .esi 0)), .alu .sub .edx (.mem (at_ .ebp 0)), .store (at_ .ebp 0) .edx] ++
    VG.Impl.Rsa.X86.KeyRt.restoreEdi wid)]

/-- `D`'s words `m`, `m + 1` from `(y₁, q̂)` to `E = (y₁, 0) + 2 q̂ - 1` modulo `2^64`. -/
def toE : List Instr := winPtrs ++ [.mov .eax (.mem (at_ .ebx 0)), .alu .add .eax (.reg .eax),
  .mov .edx (.mem (at_ .ebx 4)), .alu .adc .edx (.imm 0), .alu .sub .eax (.imm 1), .alu .sbb .edx (.imm 0),
  .store (at_ .ebx 0) .eax, .store (at_ .ebx 4) .edx]

/-- If `T < 0`: `T := T + E` and `E := E - 2`. -/
def fixX : Prog isa := seqs [
  .block (winPtrs ++ arrPtr wid .ebp sqT .eax ++ [.mov .eax (.reg .ebp), .alu .add .eax (.reg .edx),
    .mov .eax (.mem (at_ .eax 0)), .alu .add .eax (.reg .eax), .alu .sbb .ecx (.reg .ecx), .store (sc hCnt) .ecx,
    .mov .esi (.imm 0), .mov .edi (.reg .edx), .alu .add .edi (.imm 4)]),
  .loop (.block R2Words.addBody) .ne,
  .block (VG.Impl.Rsa.X86.KeyRt.restoreEdi wid ++ winPtrs ++ [.mov .ecx (.mem (sc hCnt)), .alu .and .ecx (.imm 2),
    .mov .eax (.mem (at_ .ebx 0)), .mov .edx (.mem (at_ .ebx 4)), .alu .sub .eax (.reg .ecx), .alu .sbb .edx (.imm 0),
    .store (at_ .ebx 0) .eax, .store (at_ .ebx 4) .edx])]

/-- `D := E + 1 = 2 s' β^m`. -/
def updX : List Instr := winPtrs ++ [.mov .eax (.mem (at_ .ebx 0)), .mov .edx (.mem (at_ .ebx 4)),
  .alu .add .eax (.imm 1), .alu .adc .edx (.imm 0), .store (at_ .ebx 0) .eax, .store (at_ .ebx 4) .edx]

/-- `T`'s `L + 1` words back into the window. -/
def copyBackX : Prog isa := seqs [
  .block (winPtrs ++ arrPtr wid .ebp sqT .eax ++ [.alu .add .edx (.imm 4)]),
  .loop (.block [.mov .eax (.mem (at_ .ebp 0)), .store (at_ .esi 0) .eax, .alu .add .ebp (.imm 4),
    .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne]

def stepX : Prog isa := seqs [.block estX, mulSubX, .block toE, fixX, fixX, fixX, .block updX, copyBackX,
  .block [.mov .eax (.mem (sc sCt)), .alu .sub .eax (.imm 1), .store (sc sCt) .eax]]

/-- Whether the remainder is zero; the root `D / 2` shifted down by `c = 16 K + z / 2` (words
`⌊K / 2⌋`, then bits `16 (K mod 2) + z / 2`), less one if `X` was zero, into `aY`. -/
def finishX : Prog isa := seqs ([
  .seq (.block (arrPtr wid .esi sqZ .edx ++ bytesB wid .edx ++ [.mov .ecx (.imm 0)]))
    (.loop (.block [.alu .or .ecx (.mem (at_ .esi 0)), .alu .add .esi (.imm 4), .alu .sub .edx (.imm 4)]) .ne),
  .block (flagZero ++ [.mov .eax (.mem (sc sStg)), .store (sc sOk5) .eax]),
  .block [.mov .ebx (.imm 0)], half wid sqD] ++
  [wordStagesL 128 (VG.Impl.Rsa.X86.WordModRt.width4 nl .eax) (seqs [
    .block [.mov .eax (.mem (sc sKw)), .shift .shr .eax 1, .mov .edx (.mem (sc sC4)), .shift .shr .edx 2,
      .alu .and .eax (.reg .edx), .alu .cmp .eax (.imm 1), .alu .sbb .eax (.reg .eax), .alu .add .eax (.imm 1),
      .store (sc sStg) .eax],
    moveH wid sqD wT true false, sel wid sqD sqD wT sStg])] ++
  [.block [.mov .eax (.mem (sc sKw)), .alu .and .eax (.imm 1), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .mov .edx (.mem (sc sZb)), .shift .shr .edx 1,
    .alu .add .eax (.reg .edx), .store (sc sZb) .eax]] ++
  [bitStagesL 16 1 (.seq (.block [.mov .eax (.mem (sc sZb)), .alu .and .eax (.mem (sc sB)), .alu .cmp .eax (.imm 1),
      .alu .sbb .eax (.reg .eax), .alu .add .eax (.imm 1), .store (sc sStg) .eax]) (downBitsSelH sqD))] ++
  [.block (arrPtr wid .esi sqD .edx ++ [.mov .eax (.mem (at_ .esi 0)), .alu .sub .eax (.mem (sc sZf)),
    .store (at_ .esi 0) .eax]),
   copy nar aY (2 * sqD)])

open VG.Impl.Rsa.X86.WordModRt (width4) in
def sqrt : Prog isa := seqs [normX, firstX,
  .block (width4 nl .eax ++ [.shift .shr .eax 2, .alu .sub .eax (.imm 1), .store (sc sCt) .eax]),
  .ite .e (.block []) (.loop stepX .ne), finishX]

/-! ## The factors -/

def factors : Prog isa := seqs [
  chain nar .adc aP aD aY false, .block [.mov .ebx (.imm 0)], half nar aP,
  sub3 nar aQ aD aY, .block [.mov .ebx (.imm 0)], half nar aQ,
  flagBin .and VG.Impl.Rsa.X86.Recover.sMask sOkDE sLt, flagBin .and VG.Impl.Rsa.X86.Recover.sMask VG.Impl.Rsa.X86.Recover.sMask sExact,
  flagBin .and VG.Impl.Rsa.X86.Recover.sMask VG.Impl.Rsa.X86.Recover.sMask sOk4,
  flagBin .and VG.Impl.Rsa.X86.Recover.sMask VG.Impl.Rsa.X86.Recover.sMask sOk5]

/-! ## The function -/

def det : Prog isa := seqs [deMinus, twos, gcdSet, gcdFused, aProduct, divA, divB,
  square, minus4n, sqrt, factors]

def sized : Prog isa := seqs [VG.Impl.Rsa.X86.RecoverRt.loads, VG.Impl.Rsa.X86.RecoverRt.prod, det,
  VG.Impl.Rsa.X86.RecoverRt.stores]

def body : Prog isa := .seq
  (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 4)) (.seq (.block modulusCheck) (.ite .e sized VG.Impl.Rsa.X86.Recover.failure))

def code : Prog isa := .seq (.block VG.Impl.Rsa.X86.Recover.entry) (.seq body (.block PublicFn.restore))

end VG.Impl.Rsa.X86.RecoverDetRt
