import VerifiedGarbage.Impl.Rsa.X86_64.Keys
import VerifiedGarbage.Impl.Rsa.X86_64.Crt
import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Candidate

/-!
# An RSA key from its two primes on x86-64

`vg_rsa_keygen_key(n, n_len, d, d_len, p, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, e, e_len, scratch, scratch_len)`: the first six
arguments in registers, the others on the stack.

The working space is `vg_rsa_public`'s (`Impl/Bignum/X86_64.lean`): a header
of 32 words and arrays of `W + 2` words after it, for the `W = n_len / 8`
words of `n` (the primes have `w = W / 2`). Every array's base is computed
from `rdi` and the stride `8 (W + 2)` in the header, as in
`Impl/Rsa/X86_64/Keys.lean`, whose routines (`divmod`, `inverse`, `loadA`,
`storeA`, …) do the arithmetic; the products are `mulRows` and
`mulAddRow`. The public exponent `e` (`e_len ≤ 8` octets) is a word,
public: the code branches on it. Its timing depends on nothing else but the
lengths and the status returned.

1. `p` and `q` are loaded, and swapped (under the mask of `p < q`) so that
   `p ≥ q`.
2. `p − 1` and `q − 1` (0 for 0): the number minus the mask of its being
   nonzero, and'ed with 1.
3. `lcm(p − 1, q − 1)`: their product `φ` (`w` words each, so `W + 2` words
   for the product); then `64 W` steps that halve `u`, `v` (copies of
   `p − 1` and `q − 1`) and `φ` while `u` and `v` are both even, so that
   `φ = 2^k u v` with `2^k` the power of two of `gcd(p − 1, q − 1)`; `v`
   made odd by a swap (if only `u` is odd); `gcd(u, v)` by `inverse`
   (modulo `v`, 3 for `v ≤ 1`, whose gcd is 1 or `v` itself); and `φ`
   divided by it (1 for `v ≤ 1`).
4. `d = e⁻¹ mod L`, and the mask `dOk` of its existence:
   * `e = 0`: none.
   * `e = 1`: `d = 1`, for `L ≠ 1`.
   * `e` odd: `L = e Q + R` by `divmod`; `x = R⁻¹ mod e` by `inverse`, for
     `gcd(R, e) = 1` and `L ≥ 2`; then with `t = e − x`,
     `d = Q t + (1 + R t) / e`, the last a word: `(1 + R t) e⁻¹ mod 2⁶⁴`
     (`minv`'s inverse of `e`).
   * `e` even: `d = (e mod L)⁻¹ mod L` by `inverse`, for an odd `L ≥ 3`
     (the modulus 3 otherwise).
5. If `dOk` and `d ≤ 2^(64 w)`: zeros to all seven outputs, and 2.
6. Otherwise `qInv` by `inverse` (modulo `p`, or 3 for a `p` not odd and at
   least 3), `dP = d mod (p − 1)` and `dQ = d mod (q − 1)` by `divmod`, and
   `n = p q`; the mask of `dOk`, `gcd(q, p) = 1`, `n`'s top bit, `p` and `q`
   odd and `e` valid (`Rsa.exponentValid`); the seven outputs stored under
   it, and its low bit returned.
-/

namespace VG.Impl.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Keys
open VG.Impl.RsaKeyGen.X86_64.Candidate (loadE kE kElen)

/-! ## Header slots

`kE` and `kElen` are the candidate's (for `loadE`), `sMask` is
`vg_rsa_public`'s, `sStride` and `sMo` are the key routines'. -/

def kNo : Nat := sFn 0
def kNl : Nat := sFn 1
def kDo : Nat := sFn 2
def kPp : Nat := sFn 5
def kPl : Nat := sFn 7
def kQp : Nat := sFn 8
def kDp : Nat := sFn 9
def kDq : Nat := sFn 10
def kQi : Nat := sFn 11
/-- `e`'s value. -/
def kEv : Nat := sFn 14
/-- The mask `dOk`, then the final mask. -/
def kOk : Nat := sFn 15

/-! ## Arrays -/

def aPa : Nat := 0
def aQa : Nat := 1
def aU : Nat := 2
def aV : Nat := 3
def aPm : Nat := 4
def aQm : Nat := 5
def aX₁ : Nat := 6
def aX₂ : Nat := 7
def aT : Nat := 8
def aM : Nat := 9
def aL : Nat := 10
def aQt : Nat := 11
def aR : Nat := 12
def aDd : Nat := 13
def aC : Nat := 14
def aE : Nat := 15

/-! ## Entry and exit -/

/-- The stack argument `i` (from 1). -/
def stk (i : Nat) : MemOp := { base := .rsp, disp := 8 * i }

/-- Header slot `i` of the working space at `r11`. -/
def ws11 (i : Nat) : MemOp := { base := .r11, disp := 8 * i }

/-- Save the callee-saved registers and the arguments in the header at
`scratch`, with its base in `rdi`. `d_len` is `n_len`; `q_len`, `dp_len`,
`dq_len` and `qinv_len` are `p_len`. -/
def entry : List Instr :=
  [.mov .r11 (.mem (stk 11))] ++
  (saved.zipIdx.map fun (r, i) => .store (ws11 i) r) ++
  [.store (ws11 kNo) .rdi, .store (ws11 kNl) .rsi, .store (ws11 kDo) .rdx, .store (ws11 kPp) .r8,
    .store (ws11 kPl) .r9,
    .mov .rax (.mem (stk 1)), .store (ws11 kQp) .rax, .mov .rax (.mem (stk 3)), .store (ws11 kDp) .rax,
    .mov .rax (.mem (stk 5)), .store (ws11 kDq) .rax, .mov .rax (.mem (stk 7)), .store (ws11 kQi) .rax,
    .mov .rax (.mem (stk 9)), .store (ws11 kE) .rax, .mov .rax (.mem (stk 10)), .store (ws11 kElen) .rax,
    .mov .rdi (.reg .r11)]

/-- `W = n_len / 8` into `sW`, the bases of arrays 0 to 7, and the stride
`8 (W + 2)` into `sStride`. -/
def head : List Instr :=
  [.mov .rcx (.mem (hdr kNl)), .mov .r12 (.reg .rcx), .shift .shr .r12 3, .store (hdr sW) .r12] ++ setBases ++
  [.mov .rax (.reg .r12), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .store (hdr sStride) .rax]

/-- Zeros to the seven outputs, and the status `st` returned. -/
def zeros (st : Nat) : Prog isa := seqs [zeroOut kNo kNl, zeroOut kDo kNl, zeroOut kPp kPl, zeroOut kQp kPl,
  zeroOut kDp kPl, zeroOut kDq kPl, zeroOut kQi kPl, .block ([.mov32 .rax (.imm (BitVec.ofNat 32 st))] ++ exit)]

/-! ## Masks -/

/-- `rbp := ` the mask of `[a] < [b]` over `W` words (the borrow of
`[a] - [b]`). -/
def ltA (a b : Nat) : List (Prog isa) :=
  [.block (ws ++ base a .rbx ++ base b .r10 ++ [.mov32 .rbp (.imm 0)]),
    wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]]

/-- `rbp := ` the mask of `rbp = 0`. -/
def isZero : List Instr := [.alu .cmp .rbp (.imm 1), .alu .sbb .rbp (.reg .rbp)]

/-- `rbp := ` the mask of `[a] = [b]` over `W` words. -/
def eqMask (a b : Nat) : List (Prog isa) := eqA a b ++ [.block isZero]

/-- `[aC] := x`, a word, over `W + 2` words. -/
def constA (x : BitVec 32) : List (Prog isa) :=
  [zeroA aC, .block (ws ++ base aC .rbx ++ [.mov32 .rax (.imm x), .store (at0 .rbx) .rax])]

/-- `[j] := rbp ? [j] : [aC]` over `W` words. -/
def selC (j : Nat) : List (Prog isa) :=
  [.block (ws ++ base j .r8 ++ base aC .rsi), wordLoop 0 selBody]

/-- `[o] := [a] - ([aC] & r15)` over `W` words (no borrow out, for `r15` 0
or `[aC] ≤ [a]`). -/
def subC (o a : Nat) : List (Prog isa) :=
  [.block (ws ++ base a .r8 ++ base aC .r10 ++ base o .rsi ++ [.mov32 .rbp (.imm 0)]), wordLoop 0 subMBody]

/-- `rax := ` the mask of `[j]` odd. -/
def oddMask (j : Nat) : List Instr :=
  ws ++ base j .rbx ++ [.mov .rax (.mem (at0 .rbx)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0),
    .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx)]

/-! ## The primes -/

/-- `p` and `q` swapped under the mask of `p < q`. -/
def order : List (Prog isa) :=
  ltA aPa aQa ++ [.block [.mov .r15 (.reg .rbp)], wordLoop 0 cswapBody]

/-- `[o] := [j] - 1`, or 0 for `[j] = 0`: `[j]` minus the mask of
`[j] ≠ 0` and'ed with `[aC] = 1`. -/
def decTo (o j : Nat) : List (Prog isa) :=
  [zeroA o, copyA o j] ++ constA 0 ++ eqMask j aC ++
    [.block [.mov .r15 (.reg .rbp), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))]] ++ constA 1 ++
    [.block (ws ++ base o .r8 ++ base aC .r10 ++ base o .rsi ++ [.mov32 .rbp (.imm 0)]), wordLoop 0 subMBody]

/-! ## `lcm(p − 1, q − 1)` -/

/-- `[aL] := [aPm] [aQm]`, `w = W / 2` words each. -/
def phi : List (Prog isa) :=
  [zeroA aL, .block (ws ++ base aPm .r11 ++ base aQm .rax ++ base aL .r8 ++
    [.mov .r9 (.reg .rax), .mov .r10 (.reg .r12), .shift .shr .r10 1, .alu .sub .r12 (.reg .r10)]), Crt.mulRows]

/-- `[j] := [j] / 2` if the header's `sMo` is all ones (`[aT]` working
space). -/
def halfIf (j : Nat) : List (Prog isa) :=
  [.block (ws ++ base j .r8 ++ base aT .rsi), wordLoop 0 shrBody,
    .block ([.mov .rbp (.mem (hdr sMo)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))] ++ base j .r8 ++
      base aT .rsi),
    wordLoop 0 selBody]

/-- One step of the halving: the mask of `u` and `v` both even into `sMo`,
then `u`, `v` and `φ` halved under it. -/
def twoStep : Prog isa := seqs ([
  .block (ws ++ base aU .rbx ++ base aV .r10 ++ [.mov .rax (.mem (at0 .rbx)), .alu .or .rax (.mem (at0 .r10)),
    .alu .and .rax (.imm 1), .alu .sub .rax (.imm 1), .store (hdr sMo) .rax])] ++
  halfIf aU ++ halfIf aV ++ halfIf aL ++ [.block countP])

/-- `64 W` steps of the halving. -/
def twos : List (Prog isa) := [.block (divInit aT), .loop twoStep .ne]

/-- `[aV] := gcd(u, v)`, or 1 for `v ≤ 1`, after the halving: `v` made odd
by a swap, `inverse` modulo `v` (3 for `v ≤ 1`), and the result 1 for
`v ≤ 1` (whose mask `kOk` holds, as `inverse` uses `sMo`). -/
def gcdUV : List (Prog isa) :=
  [.block (oddMask aV ++ [.mov .r15 (.reg .rax), .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1)))] ++ base aU .rbx ++
      base aV .r10),
    wordLoop 0 cswapBody] ++
  constA 2 ++ ltA aV aC ++ [.block [.store (hdr kOk) .rbp, .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] ++
  constA 3 ++ selC aV ++
  [zeroA aM, copyA aM aV, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂, inverse aU aV aX₁ aX₂ aM aT] ++
  constA 1 ++ [.block [.mov .rbp (.mem (hdr kOk)), .alu .xor .rbp (.imm (BitVec.ofInt 32 (-1)))]] ++ selC aV

/-- `[aL] := lcm(p − 1, q − 1)`. -/
def lcmPart : List (Prog isa) :=
  phi ++ [zeroA aU, copyA aU aPm, zeroA aV, copyA aV aQm] ++ twos ++ gcdUV ++ [divmod aL aR aV aT]

/-! ## `d = e⁻¹ mod L` -/

/-- `[aE] := e`. -/
def loadEv : List (Prog isa) :=
  [zeroA aE, .block (ws ++ base aE .rbx ++ [.mov .rax (.mem (hdr kEv)), .store (at0 .rbx) .rax])]

/-- `kOk := ` the mask of `L ≥ 2`. -/
def lGe2 : List (Prog isa) :=
  constA 2 ++ ltA aL aC ++ [.block [.alu .xor .rbp (.imm (BitVec.ofInt 32 (-1))), .store (hdr kOk) .rbp]]

/-- `e = 0`: no inverse. -/
def dZero : List Instr := [.mov32 .rax (.imm 0), .store (hdr kOk) .rax]

/-- `e = 1`: `d = 1`, for `L ≠ 1`. -/
def dOne : List (Prog isa) :=
  constA 1 ++ eqMask aL aC ++ [.block [.alu .xor .rbp (.imm (BitVec.ofInt 32 (-1))), .store (hdr kOk) .rbp],
    zeroA aDd, .block (setOneA aDd)]

/-- `inverse`'s start for `[aU]` modulo `[j]`: `v := [j]`, `x₁ := 1`,
`x₂ := 0`. -/
def invFrom (j : Nat) : List (Prog isa) :=
  [zeroA aV, copyA aV j, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂]

/-- `kOk &= ` the mask of `[aV] = 1`. -/
def gcdIsOne : List (Prog isa) :=
  constA 1 ++ eqMask aV aC ++ [.block [.alu .and .rbp (.mem (hdr kOk)), .store (hdr kOk) .rbp]]

/-- `e` odd, at least 3: `L = e Q + R`, `x = R⁻¹ mod e`, `t = e − x`, then
`d = Q t + c` with `c = (1 + R t) e⁻¹ mod 2⁶⁴`. -/
def dOdd : List (Prog isa) :=
  loadEv ++ [zeroA aQt, copyA aQt aL, divmod aQt aR aE aT, zeroA aU, copyA aU aR] ++ invFrom aE ++
  [inverse aU aV aX₁ aX₂ aE aT] ++ lGe2 ++ gcdIsOne ++
  [.block ([.mov .rbx (.mem (hdr kEv))] ++ minv),
    .block (ws ++ base aX₂ .rbx ++ base aR .r10 ++
      [.mov .rsi (.mem (hdr kEv)), .alu .sub .rsi (.mem (at0 .rbx)), .mov .rax (.mem (at0 .r10)), .mul .rsi,
        .alu .add .rax (.imm 1), .mul .rcx, .mov .r15 (.reg .rax), .store (hdr sMo) .rsi]),
    zeroA aDd,
    .block (ws ++ base aDd .r8 ++ [.store (at0 .r8) .r15] ++ base aQt .rax ++
      [.mov .r9 (.reg .rax), .mov .rcx (.mem (hdr sMo))]),
    mulAddRow]

/-- `e` even: `d = (e mod L)⁻¹ mod L` for an odd `L ≥ 3`. -/
def dEven : List (Prog isa) :=
  loadEv ++
  -- `[aM] := L`, or 1 for `L = 0`.
  [zeroA aM, copyA aM aL] ++ constA 0 ++ eqMask aL aC ++ [.block [.mov .r15 (.reg .rbp)]] ++ constA 1 ++
  [.block (ws ++ base aM .rbx ++ base aC .r10 ++ [.mov .rax (.mem (at0 .rbx)), .mov .rdx (.reg .r15),
      .alu .and .rdx (.imm 1), .alu .or .rax (.reg .rdx), .store (at0 .rbx) .rax]),
    zeroA aQt, copyA aQt aE, divmod aQt aR aM aT, zeroA aU, copyA aU aR] ++
  -- `kOk := ` the mask of `L` odd and at least 3; `[aM] := L`, or 3.
  constA 3 ++ ltA aL aC ++
  [.block ([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] ++ oddMask aL ++
      [.alu .and .rax (.reg .rcx), .store (hdr kOk) .rax, .mov .rbp (.reg .rax)]),
    zeroA aM, copyA aM aL] ++ selC aM ++ invFrom aM ++ [inverse aU aV aX₁ aX₂ aM aT] ++ gcdIsOne ++
  [zeroA aDd, copyA aDd aX₂]

/-- `d` and `kOk`, by `e`. -/
def dPart : Prog isa :=
  .seq (.block [.mov .rax (.mem (hdr kEv)), .alu .cmp .rax (.imm 1)])
    (.ite .b (.block dZero)
      (.ite .e (seqs dOne)
        (.seq (.block [.mov .rax (.mem (hdr kEv)), .alu .and .rax (.imm 1)])
          (.ite .ne (seqs dOdd) (seqs dEven)))))

/-! ## The key -/

/-- `rbp := kOk & ` the mask of `d ≤ 2^(64 w)` (`d < 2^(64 w) + 1`). -/
def smallMask : List (Prog isa) :=
  constA 1 ++
  [.block (ws ++ base aC .rbx ++ [.mov .rax (.reg .r12), .shift .shr .rax 1, .mov32 .rdx (.imm 1),
      .store (ix .rbx .rax) .rdx])] ++
  ltA aDd aC ++ [.block [.alu .and .rbp (.mem (hdr kOk)), .alu .test .rbp (.reg .rbp)]]

/-- `qInv` into `aX₂` (modulo `p`, or 3 for a `p` not odd and at least 3)
and `kOk &= ` the mask of `gcd(q, p) = 1`. -/
def qinvPart : List (Prog isa) :=
  [zeroA aU, copyA aU aQa] ++ constA 3 ++ ltA aPa aC ++
  [.block ([.mov .rcx (.reg .rbp), .alu .xor .rcx (.imm (BitVec.ofInt 32 (-1)))] ++ oddMask aPa ++
      [.alu .and .rax (.reg .rcx), .mov .rbp (.reg .rax)]),
    zeroA aM, copyA aM aPa] ++ selC aM ++ invFrom aM ++ [inverse aU aV aX₁ aX₂ aM aT] ++
  constA 1 ++ eqMask aV aC ++ [.block [.alu .and .rbp (.mem (hdr kOk)), .store (hdr kOk) .rbp]]

/-- `[aM] := [j]`, or 1 for `[j] = 0`. -/
def divisorOf (j : Nat) : List (Prog isa) :=
  [zeroA aM, copyA aM j] ++ constA 0 ++ eqMask j aC ++
  [.block (ws ++ base aM .rbx ++ [.mov .rax (.mem (at0 .rbx)), .alu .and .rbp (.imm 1), .alu .or .rax (.reg .rbp),
      .store (at0 .rbx) .rax])]

/-- `dP` into `aX₁` and `dQ` into `aV`. -/
def crtPart : List (Prog isa) :=
  divisorOf aPm ++ [zeroA aU, copyA aU aDd, divmod aU aV aM aT, zeroA aX₁, copyA aX₁ aV] ++
  divisorOf aQm ++ [zeroA aU, copyA aU aDd, divmod aU aV aM aT]

/-- `n = p q` into `aQt`. -/
def nPart : List (Prog isa) :=
  [zeroA aQt, .block (ws ++ base aPa .r11 ++ base aQa .rax ++ base aQt .r8 ++
    [.mov .r9 (.reg .rax), .mov .r10 (.reg .r12), .shift .shr .r10 1, .alu .sub .r12 (.reg .r10)]), Crt.mulRows]

/-- `kOk &= ` the masks of `n`'s top bit, `p` and `q` odd, and `e` valid
(`Rsa.exponentValid`: odd, at least 3 and below `2^33`). -/
def finalMask : List Instr :=
  ws ++ base aQt .rbx ++
  [.mov .rax (.mem (ix .rbx .r12 (-8))), .shift .shr .rax 63, .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
    .alu .and .rdx (.mem (hdr kOk)), .mov .rcx (.reg .rdx)] ++
  oddMask aPa ++ [.alu .and .rcx (.reg .rax)] ++ oddMask aQa ++ [.alu .and .rcx (.reg .rax),
    -- `e`: odd, `e − 3` without a borrow, `e >> 33` zero.
    .mov .rax (.mem (hdr kEv)), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
    .alu .and .rcx (.reg .rdx),
    .mov .rax (.mem (hdr kEv)), .alu .cmp .rax (.imm 3), .alu .sbb .rdx (.reg .rdx),
    .alu .xor .rdx (.imm (BitVec.ofInt 32 (-1))), .alu .and .rcx (.reg .rdx),
    .mov .rax (.mem (hdr kEv)), .shift .shr .rax 33, .alu .cmp .rax (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .and .rcx (.reg .rdx), .store (hdr kOk) .rcx]

/-- The seven outputs under `kOk`, and its low bit returned. -/
def outputs : List (Prog isa) :=
  storeA aQt kNo kNl kOk ++ storeA aDd kDo kNl kOk ++ storeA aPa kPp kPl kOk ++ storeA aQa kQp kPl kOk ++
  storeA aX₁ kDp kPl kOk ++ storeA aV kDq kPl kOk ++ storeA aX₂ kQi kPl kOk ++
  [.block ([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] ++ exit)]

/-- Once `d` is not too small, or does not exist. -/
def keyPart : Prog isa :=
  seqs (qinvPart ++ crtPart ++ nPart ++ [.block finalMask] ++ outputs)

/-- `vg_rsa_keygen_key`. -/
def code : Prog isa :=
  seqs ([.block (entry ++ head)] ++ loadA aPa kPp kPl ++ loadA aQa kQp kPl ++ loadE ++
    [.block [.store (hdr kEv) .rbx]] ++ order ++ decTo aPm aPa ++ decTo aQm aQa ++ lcmPart ++ [dPart] ++
    smallMask ++ [.ite .ne (zeros 2) keyPart])

end VG.Impl.RsaKeyGen.X86_64.Key
