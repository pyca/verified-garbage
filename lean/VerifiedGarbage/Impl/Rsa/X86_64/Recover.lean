import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-!
# `vg_rsa_recover_primes` on x86-64

`vg_rsa_recover_primes(p, p_len, q, q_len, n, n_len, e, e_len, d, d_len,
scratch, scratch_len)`: the first six arguments in registers, the others on
the stack, in the working space of `Keys.lean` (`vg_rsa_public`'s, with
16 arrays). `n` is checked as `vg_rsa_public` checks it (it is public).
Then, with Montgomery multiplication `mul` (`[o] = [a] [b] R⁻¹ mod n`):

* `M = d e` over two arrays (`prod`), by `mulAddRow` once per word of `e`;
  if `M` is even or 1 (`d e - 1` odd or not positive), no candidate is
  tried and zeros are written. Otherwise `m = M - 1` (`M` with its low bit
  cleared), and `64 Bw` masked halvings (`Bw` the words of `d` and `e`
  together, public) leave `r = m / 2^t` with `r` odd and `t` counted
  (`halving`).
* `-n⁻¹`, `R² mod n`, `R mod n` and `n - R mod n` (the Montgomery forms of
  1 and `-1`).
* For the candidates `g = 2, 3, …`, until one gives the factors or 100 are
  tried (`candLoop`, whose number of iterations is the number of tries,
  which the contract lets leak): `y = g^r` by a square and a multiplication
  per bit of `r` (all `64 Bw` of them), the multiplicand `g` or 1 chosen by
  a mask (`expLoop`); then `64 Bw` squarings under masks that stop at
  `y² = 1` (found), at `y² = -1` or after `t` of them (not found)
  (`sqBody`).
* `p = gcd(y - 1, n)` by `inverse`, `q = n / p` by `divmod`, the larger
  first, written masked by whether a candidate gave them (`fin`).
-/

namespace VG.Impl.Rsa.X86_64.Keys.Recover

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Keys

/-! ## The layout -/

/-- Header slots: `p` and `q`'s pointers, `d`'s pointer and length (`n`
and `e` in `vg_rsa_public`'s `sN`, `sK`, `sE` and `sElen`), the candidate's
number, `t`, and three slots for the loops' counters and masks (the first
also `R² mod n`'s counter). -/
def sP : Nat := sOut
def sQ : Nat := sIn
def sD : Nat := sI
def sDl : Nat := sBit
def sCand : Nat := sV
def sC1 : Nat := sCnt
def sT : Nat := sFn 11
def sC2 : Nat := sFn 14
def sC3 : Nat := sFn 15

/-- Arrays, after `vg_rsa_public`'s 0 to 7: `e` (8), `d` (9), `M` over 10
and 11, `g R mod n` (12), `R mod n` (13), `n - R mod n` (14), and the
halvings' temporary over 14 and 15. At the end: `gcd`'s `u`, `v`, `x₁`,
`x₂` and working array (8, 9, 12, 13, 15), and `n / p` (14) and
`n mod p` (10). -/
def aE : Nat := 8
def aD : Nat := 9
def aM : Nat := 10
def aG : Nat := 12
def aO : Nat := 13
def aNg : Nat := 14
def aH : Nat := 14
def fU : Nat := 8
def fV : Nat := 9
def fX₁ : Nat := 12
def fX₂ : Nat := 13
def fT : Nat := 15
def fQ : Nat := 14
def fR : Nat := 10

/-- The stack argument `i` (from 1). -/
def stk (i : Nat) : MemOp := { base := .rsp, disp := 8 * i }

/-- `Bw = w + ⌈e_len / 8⌉` into `rax`. -/
def bw : List Instr :=
  [.mov .rax (.mem (hdr sElen)), .alu .add .rax (.imm 7), .shift .shr .rax 3, .alu .add .rax (.mem (hdr sW))]

/-! ## The entry and the exits -/

/-- Save the callee-saved registers and the arguments in the header at
`scratch`, with its base in `rdi`. `p_len` and `q_len` are `n_len`. -/
def entry : List Instr :=
  [.mov .r11 (.mem (stk 5))] ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  [.store { base := .r11, disp := 8 * sP } .rdi, .store { base := .r11, disp := 8 * sQ } .rdx,
    .store { base := .r11, disp := 8 * sN } .r8, .store { base := .r11, disp := 8 * sK } .r9,
    .mov .rax (.mem (stk 1)), .store { base := .r11, disp := 8 * sE } .rax,
    .mov .rax (.mem (stk 2)), .store { base := .r11, disp := 8 * sElen } .rax,
    .mov .rax (.mem (stk 3)), .store { base := .r11, disp := 8 * sD } .rax,
    .mov .rax (.mem (stk 4)), .store { base := .r11, disp := 8 * sDl } .rax, .mov .rdi (.reg .r11)]

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [zeroOut sP sK, zeroOut sQ sK, .block ([.mov32 .rax (.imm 0)] ++ exit)]

/-! ## `d e` -/

/-- The bases of `e`, `M` and `d` into `rbx`, `r10` and `r15`, the words of
`e` into `r11`, and the row counter `r13 := 0`. -/
def prodInit : List Instr :=
  ws ++ base aE .rbx ++ base aM .r10 ++ base aD .r15 ++
    [.mov .r11 (.mem (hdr sElen)), .alu .add .r11 (.imm 7), .shift .shr .r11 3, .mov32 .r13 (.imm 0)]

/-- Row `r13`: `rcx := e[r13]`, the accumulator at word `r13` of `M`, and
`d`'s base in `r9`. -/
def rowHead : List Instr :=
  [.mov .rcx (.mem (ix .rbx .r13)), .mov .r8 (.reg .r13), .alu .add .r8 (.reg .r8), .alu .add .r8 (.reg .r8),
    .alu .add .r8 (.reg .r8), .alu .add .r8 (.reg .r10), .mov .r9 (.reg .r15)]

/-- The row counter against `r11`. -/
def rowNext : List Instr := [.alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r11)]

/-- `M := d e`: `M += e_j d` at word `j`, for each word `j` of `e`. -/
def prod : List (Prog isa) :=
  [zeroA aM, zeroA (aM + 1),
    .seq (.block prodInit) (.loop (.seq (.block rowHead) (.seq mulAddRow (.block rowNext))) .ne)]

/-- `rbp |= [rbx]`, a word at a time. -/
def orBody : List Instr := [.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)]

/-- The mask of `M` even into `sC2`, and `m := M` with its low bit cleared
(`M - 1` for an odd `M`); then `w`, `rbp := 0` and `r12 := Bw` for the test
of `m = 0`. -/
def skipBlk : List Instr :=
  ws ++ base aM .rbx ++
    [.mov .rax (.mem (at0 .rbx)), .mov .rdx (.reg .rax), .alu .and .rdx (.imm 1), .alu .sub .rax (.reg .rdx),
      .store (at0 .rbx) .rax, .alu .sub .rdx (.imm 1), .store (hdr sC2) .rdx, .mov32 .rbp (.imm 0)] ++ bw ++
    [.mov .r12 (.reg .rax)]

/-- `ZF := ¬(M even ∨ m = 0)`: the mask of `m = 0` or'ed with `sC2`. -/
def skipTest : List Instr :=
  [.alu .cmp .rbp (.imm 1), .alu .sbb .rax (.reg .rax), .alu .or .rax (.mem (hdr sC2)), .alu .test .rax (.reg .rax)]

/-! ## `m = 2^t r` -/

/-- `r11 := 64 Bw` halvings, counted by `r13`, and `t := 0`. -/
def halfInit : List Instr :=
  bw ++ [.mov .r11 (.reg .rax)] ++ List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
    [.mov32 .r13 (.imm 0), .mov32 .rax (.imm 0), .store (hdr sT) .rax]

/-- `m`'s and the temporary's bases, `r12 := Bw`, and `rbp` the mask of `m`
odd. -/
def halfHead : List Instr :=
  ws ++ base aM .r8 ++ base aH .rsi ++ bw ++
    [.mov .r12 (.reg .rax), .mov .rax (.mem (at0 .r8)), .alu .and .rax (.imm 1), .mov32 .rbp (.imm 0),
      .alu .sub .rbp (.reg .rax)]

/-- `t += 1` if `m` was even, and the counter. -/
def halfNext : List Instr :=
  [.mov .rax (.reg .rbp), .alu .add .rax (.imm 1), .alu .add .rax (.mem (hdr sT)), .store (hdr sT) .rax,
    .alu .add .r13 (.imm 1), .alu .cmp .r13 (.reg .r11)]

/-- `64 Bw` times: `m := m / 2` if `m` is even, and then `t += 1`. -/
def halving : Prog isa :=
  .seq (.block halfInit)
    (.loop (seqs [.block halfHead, wordLoop 0 shrBody, wordLoop 0 selBody, .block halfNext]) .ne)

/-! ## The candidates -/

variable (mul : Nat → Nat → Nat → Prog isa)

/-- `-n⁻¹`, for `n` in its array. -/
def minvBlk : List Instr :=
  ws ++ base aN .r10 ++ [.mov .rbx (.mem (at0 .r10))] ++ minv ++ [.store (hdr sMinv) .r15]

/-- `R² mod n` as `vg_rsa_public` computes it, the number 1, `R mod n` and
`n - R mod n`. -/
def mont : List (Prog isa) := [
  .block [.mov .r12 (.mem (hdr sW)), .mov .r10 (.mem (hdr (sArr aN)))],
  .block [.mov .rax (.mem (ix .r10 .r12 (-8)))],
  topBit,
  .block [.store (hdr sCnt) .rcx, .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  .block [.mov .rcx (.mem (hdr sCnt)), .alu .add .rcx (.mem (hdr sW))],
  doubles aN aAcc aTmp aR2 sCnt,
  mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2, mul aR2 aR2 aR2,
  .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0), .mov .r12 (.mem (hdr sW))],
  setWord aOne .rcx,
  mul aY aR2 aOne,
  copyA aO aY,
  .block (ws ++ base aN .r8 ++ base aO .r10 ++ base aNg .rsi ++ [.mov32 .rbp (.imm 0)]),
  wordLoop 0 subBody]

/-- The candidate `g = sCand + 2` into `rdx`, `rcx := 0`, and `w`. -/
def gBlk : List Instr :=
  [.mov .rdx (.mem (hdr sCand)), .alu .add .rdx (.imm 2), .mov32 .rcx (.imm 0), .mov .r12 (.mem (hdr sW))]

/-- `sC1 := Bw`, the words of `r` left. -/
def expInit : List Instr := bw ++ [.store (hdr sC1) .rax]

/-- Word `sC1 - 1` of `r` into `sC2`, and `sC3 := 64` bits left. -/
def wordHead : List Instr :=
  ws ++ base aM .rbx ++
    [.mov .rax (.mem (hdr sC1)), .alu .sub .rax (.imm 1), .mov .rax (.mem (ix .rbx .rax)), .store (hdr sC2) .rax,
      .mov32 .rax (.imm 64), .store (hdr sC3) .rax]

/-- The top bit of `sC2` out of it, and `rbp` the mask of it clear; the
bases of the multiplicand and of `g R mod n`. -/
def bitSel : List Instr :=
  [.mov .rax (.mem (hdr sC2)), .mov .rdx (.reg .rax), .shift .shr .rdx 63, .alu .add .rax (.reg .rax),
    .store (hdr sC2) .rax, .mov .rbp (.reg .rdx), .alu .sub .rbp (.imm 1)] ++ ws ++ base aXm .r8 ++ base aG .rsi

/-- The bits left. -/
def bitNext : List Instr := [.mov .rax (.mem (hdr sC3)), .alu .sub .rax (.imm 1), .store (hdr sC3) .rax]

/-- A bit of `r`: the multiplicand `g` or 1 (in Montgomery form), then
`Y := Y² · multiplicand`. -/
def bitBody : Prog isa :=
  seqs [copyA aXm aO, .block bitSel, wordLoop 0 selBody, mul aY aY aY, mul aY aY aXm, .block bitNext]

/-- The words left. -/
def wordNext : List Instr := [.mov .rax (.mem (hdr sC1)), .alu .sub .rax (.imm 1), .store (hdr sC1) .rax]

/-- `Y := Y · g^r` (in Montgomery form), over all the bits of the `Bw` words
of `r`, most significant first. -/
def expLoop : Prog isa :=
  .seq (.block expInit) (.loop (.seq (.block wordHead) (.seq (.loop (bitBody mul) .ne) (.block wordNext))) .ne)

/-- The mask of `rbp = 0` into a header slot. -/
def eqStore (slot : Nat) : List Instr := [.alu .cmp .rbp (.imm 1), .alu .sbb .rax (.reg .rax), .store (hdr slot) .rax]

/-- `done := (y = 1) ∨ (y = -1)` (`y = 1` in `sC2`), `ok := 0`, `k := 0`. -/
def chkBlk : List Instr :=
  [.alu .cmp .rbp (.imm 1), .alu .sbb .rax (.reg .rax), .alu .or .rax (.mem (hdr sC2)), .store (hdr sC2) .rax,
    .mov32 .rax (.imm 0), .store (hdr sC3) .rax, .store (hdr sC1) .rax]

/-- After `x = y²`, with `x = 1` in `sMask` and `rbp = 0` iff `x = -1`: the
squaring is live if not `done` and `k < t`; it finds `y` if `x = 1`, fails
if `x = -1` or `k + 1 = t`, and continues with `y := x` otherwise.
`done` and `ok` updated, `rbp` the mask of not continuing, and the bases
of `y` and `x`. -/
def sqLogic : List Instr :=
  [.alu .cmp .rbp (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .mov .rax (.mem (hdr sC1)), .alu .cmp .rax (.mem (hdr sT)), .alu .sbb .rcx (.reg .rcx),
    .alu .add .rax (.imm 1), .alu .xor .rax (.mem (hdr sT)), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .alu .or .rdx (.reg .rax),
    .mov .rax (.mem (hdr sC2)), .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rcx (.reg .rax),
    .mov .rax (.mem (hdr sMask)), .mov .r15 (.reg .rax), .alu .and .r15 (.reg .rcx),
    .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rcx (.reg .rax),
    .mov .rbp (.reg .rcx), .alu .and .rbp (.reg .rdx),
    .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rcx (.reg .rdx),
    .alu .or .rbp (.reg .r15), .alu .or .rbp (.mem (hdr sC2)), .store (hdr sC2) .rbp,
    .alu .or .r15 (.mem (hdr sC3)), .store (hdr sC3) .r15,
    .mov .rbp (.reg .rcx), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] ++ ws ++ base aY .r8 ++ base aX .rsi

/-- `k += 1` against `64 Bw`. -/
def sqNext : List Instr :=
  [.mov .rax (.mem (hdr sC1)), .alu .add .rax (.imm 1), .store (hdr sC1) .rax, .mov .rdx (.reg .rax)] ++ bw ++
    List.replicate 6 (.alu .add .rax (.reg .rax)) ++ [.alu .cmp .rdx (.reg .rax)]

/-- A squaring: `x := y²`, the masks of `x = ±1`, and `y := x` if the
squarings continue. -/
def sqBody : Prog isa :=
  seqs ([copyA aX aY, mul aX aX aY] ++ eqA aX aO ++ [.block (eqStore sMask)] ++ eqA aX aNg ++
    [.block sqLogic, wordLoop 0 selBody, .block sqNext])

/-- The candidates tried `+= 1`, and `ZF` set to stop if `ok` or 100 are
tried. -/
def candNext : List Instr :=
  [.mov .rax (.mem (hdr sCand)), .alu .add .rax (.imm 1), .store (hdr sCand) .rax,
    .alu .cmp .rax (.imm 100), .alu .sbb .rax (.reg .rax),
    .mov .rdx (.mem (hdr sC3)), .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.reg .rdx),
    .alu .test .rax (.reg .rax)]

/-- A candidate: `g R mod n`, `Y = g^r R mod n`, the check of `y = ±1`,
and the squarings. -/
def candBody : Prog isa :=
  seqs ([.block gBlk, setWord aX .rcx, mul aXm aX aR2, copyA aG aXm, copyA aY aO, expLoop mul] ++ eqA aY aO ++
    [.block (eqStore sC2)] ++ eqA aY aNg ++ [.block chkBlk, .loop (sqBody mul) .ne, .block candNext])

/-- The candidates, from `sCand = 0`. -/
def candLoop : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (hdr sCand) .rax]) (.loop (candBody mul) .ne)

/-- `rbp := ` the mask of `[rbx] < [r10]`, a word at a time. -/
def ltBody : List Instr :=
  [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]

/-- The mask of the last candidate's `ok`; `y` out of Montgomery form,
`p = gcd(y - 1, n)` and `q = n / p`, the larger first; both written
masked, and the mask's low bit returned. -/
def fin : List (Prog isa) :=
  [.block [.mov .rax (.mem (hdr sC3)), .store (hdr sMask) .rax],
    mul aY aY aOne, zeroA fU,
    .block (ws ++ base aY .r8 ++ base aOne .r10 ++ base fU .rsi ++ [.mov32 .rbp (.imm 0)]),
    wordLoop 0 subBody,
    zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁), zeroA fX₂, inverse fU fV fX₁ fX₂ aN fT,
    zeroA fQ, copyA fQ aN, divmod fQ fR fV fT,
    .block (ws ++ base fV .rbx ++ base fQ .r10 ++ [.mov32 .rbp (.imm 0)]),
    wordLoop 0 ltBody, .block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody] ++
  storeA fV sP sK sMask ++ storeA fQ sQ sK sMask ++ [.block retMask]

/-- After `M` is known odd and above 1. -/
def rest : Prog isa := seqs ([halving] ++ mont mul ++ [candLoop mul] ++ fin mul)

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([.block CrtValues.head] ++ loadA aN sN sK ++ loadA aE sE sElen ++ loadA aD sD sDl ++
  [.block minvBlk] ++ prod ++
  [.block skipBlk, wordLoop 0 orBody, .block skipTest, .ite .ne fail (rest mul)])

/-- `vg_rsa_recover_primes` with Montgomery multiplication `mul`. -/
def code : Prog isa :=
  .seq (.block (entry ++ [.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] ++ invalid))
    (.ite .ne fail (main mul))

end VG.Impl.Rsa.X86_64.Keys.Recover
