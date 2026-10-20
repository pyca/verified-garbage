module

public import VerifiedGarbage.Impl.Rsa.Arm.Recover

/-! # An RSA key from its two primes on ARMv7

`vg_rsa_keygen_key(n, n_len, d, d_len, p, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, e, e_len, scratch, scratch_len)`: the first four
arguments in `r0`–`r3`, the others on the stack. The function pushes a frame
of 56 bytes (`r0`–`r12` and `lr`), as `vg_rsa_public_checked` does: `n`,
`n_len` and `d` are then frame words 0, 1 and 2, and the stack arguments
start at byte 56.

The numbers live in the key working space at `scratch`
(`Impl/Rsa/Arm/KeyWs.lean`) with `W = p_len / 2 + 4` words of 32 bits: room
for `n`, of `16 p_len` bits, and for `L t + 1` below, of up to
`16 p_len + 64` bits, below the modulus `2^(32 W − 1)` of the products
(`mulMod`). `p`, `q` and `e` are read into arrays, and then, piece by
piece, as AArch64 computes the key (`Impl/RsaKeyGen/AArch64/Key.lean`):

1. `p` and `q` swapped, by selections under the borrow of `p − q`, so that
   `p ≥ q`.
2. `p − 1` and `q − 1` (0 for 0): the difference with 1, or 0 under its
   borrow.
3. `L = lcm(p − 1, q − 1)`: their product `φ` (`mulMod`, over `8 p_len`
   bits); `8 p_len` steps that halve `u`, `v` (copies of `p − 1` and
   `q − 1`) and `φ` while `u` and `v` are both even; `v` made odd by a swap
   (if it is even); `gcd(u, v)` by `inverse` (modulo `v`, 3 for `v < 2`)
   and 1 for `v < 2`; and `φ` divided by it (`Impl/Rsa/Arm/Div.lean`).
   Every divisor is nonzero.
4. `d = e⁻¹ mod L`, and the flag `sOk` of its existence, by `e`, which is
   public (the only branches before the status):
   * `e = 0`: none.
   * `e = 1`: `d = 1`, for `L ≠ 1`.
   * `e` odd: `x = L⁻¹ mod e` by `inverse` (`gcd(L, e) = 1`, for `L ≥ 2`);
     then with `t = e − x`, `d = (L t + 1) / e`, an exact division: the
     product by `mulMod` from 1 over 64 bits of `t`, then the division.
   * `e` even: `d = e⁻¹ mod L` by `inverse` for an odd `L ≥ 3` (the modulus
     3 otherwise).
5. If `sOk` and `d ≤ 2^(8 p_len)` (`d < 2^(8 p_len) + 1`): zeros to all
   seven outputs, and 2.
6. Otherwise `qInv` by `inverse` (modulo `p`, or 3 for a `p` even or below
   3), `dP = d mod (p − 1)` and `dQ = d mod (q − 1)` by the division (by 1
   for `p − 1` or `q − 1` zero, which the mask then rules out), and
   `n = p q` by `mulMod`; the mask of `sOk`, `gcd(q, p) = 1`,
   `n ≥ 2^(16 p_len − 1)`, `p` and `q` odd and `e` valid
   (`Rsa.exponentValid`: odd, at least 3 and below `2^33`); the seven
   outputs written under it (`CrtValues.store`), and it returned.

Every choice on secrets is a selection (`sel`) or a flag computed with
`and`, `orr` and `eor`; addresses and loop counts depend only on the
pointers and the lengths, and the branches on `e` and the status.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.Arm.Key
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

/-! ## The frame

After the push, `n`, `n_len` and `d` are frame bytes 0, 4 and 8; the stack
arguments start at byte 56: `p`, `p_len`, `q`, `q_len`, `dp`, `dp_len`,
`dq`, `dq_len`, `qinv`, `qinv_len`, `e`, `e_len`, `scratch`,
`scratch_len`. -/

def aoN : Nat := 0
def aoNl : Nat := 4
def aoD : Nat := 8
def aoP : Nat := 56
def aoPl : Nat := 60
def aoQ : Nat := 64
def aoDp : Nat := 72
def aoDq : Nat := 80
def aoQi : Nat := 88
def aoE : Nat := 96
def aoEl : Nat := 100
def aoS : Nat := 104

/-! ## The arrays

0–14 are `inverse`'s (`aM` its modulus, `aNM` the negated modulus, `aZero`
zero); then the inputs, the constants, the numbers, the division's four and
`mulMod`'s, whose four temporaries come last. -/

def aP0 : Nat := 15
def aQ0 : Nat := 16
def aE : Nat := 17
def aP : Nat := 18
def aQ : Nat := 19
def aPm : Nat := 20
def aQm : Nat := 21
def aOne : Nat := 22
def aTwo : Nat := 23
def aThree : Nat := 24
/-- `2^(32 W − 1)`, the modulus of the products. -/
def aMod : Nat := 25
def aU : Nat := 26
def aV : Nat := 27
/-- `φ`, halved. -/
def aF : Nat := 28
def aU2 : Nat := 29
def aV2 : Nat := 30
def aG : Nat := 31
def aL : Nat := 32
def aD : Nat := 33
/-- `2^(8 p_len) + 1`. -/
def aC : Nat := 34
def aQd : Nat := 35
def aDr : Nat := 36
def aDv : Nat := 37
def aDt : Nat := 38
def aQi : Nat := 39
def aDP : Nat := 40
def aDQ : Nat := 41
def aN : Nat := 42
/-- `2^(16 p_len − 1)`. -/
def aTop : Nat := 43
/-- `2^33`. -/
def aC33 : Nat := 44
def aTmp : Nat := 45
def aTmp2 : Nat := 46
def aTt : Nat := 47
def aMy : Nat := 48
def aMx : Nat := 49
def aMa : Nat := 50
def aMt : Nat := 51
/-- The number of arrays. -/
def nArr : Nat := 55

/-! ## The header

Bytes 0–19 are the division's (16: `W`), 100–112 the shared routines', and
132 the mask of the result (`CrtValues.sMask`, which `CrtValues.store`
reads). -/

def sLt : Nat := 20
def sPz : Nat := 24
def sQz : Nat := 28
def sBu : Nat := 32
def sBv : Nat := 36
def sH : Nat := 40
def sVe : Nat := 44
def sV2 : Nat := 48
def sE0 : Nat := 52
def sE1 : Nat := 56
def sEo : Nat := 60
def sOk : Nat := 64
def sG : Nat := 68
def sL2 : Nat := 72
def sLo : Nat := 76
def sL3 : Nat := 80
def sGood : Nat := 84
def sSm : Nat := 88
def sFl : Nat := 92
def sPo : Nat := 96
def sP3 : Nat := 116
def sQg : Nat := 120
def sGq : Nat := 124
def sTop : Nat := 128
def sMask : Nat := 132
def sQo : Nat := 136
def sE3 : Nat := 140
def sEv : Nat := 144
def sZ : Nat := 148
/-- The halving's count. -/
def sHc : Nat := 152

/-! ## Contexts -/

/-- The base of the working space into `r8`. -/
def ctxB : List Instr := [.ldrSp .r8 aoS]

/-- `W` (header byte 16) into `r9` and the stride into `r7`. -/
def ctxW : List Instr := [.ldr .r9 .r8 16] ++ stride

/-! ## Words of arrays -/

/-- Word `o / 4` of `[j]` := `x`. -/
def setWd (j o x : Nat) : List Instr := ptr .r0 j ++ [.mov .r1 (.imm (BitVec.ofNat 32 x)), .str .r1 .r0 o]

/-- The word at byte `(W << sh) − c` of `[j]` := `x`. -/
def setHi (j sh c x : Nat) : List Instr :=
  ptr .r0 j ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl sh), .dp .sub .r0 .r0 (.imm (BitVec.ofNat 32 c)),
    .mov .r1 (.imm (BitVec.ofNat 32 x)), .str .r1 .r0 0]

/-- The slot `d` := the slot `a` xor'ed with 1. -/
def notS (d a : Nat) : List Instr := [.ldr .r1 .r8 a, .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 d]

/-- The slot `d` := not `a`, and `b`. -/
def andNotS (d a b : Nat) : List Instr :=
  [.ldr .r1 .r8 a, .dp .eor .r1 .r1 (.imm 1), .ldr .r2 .r8 b, .dp .and .r1 .r1 (.reg .r2), .str .r1 .r8 d]

/-- The slot `d` := `[a] < [b]`, the borrow of `[a] − [b]` (`[aTmp]` scratch). -/
def ltS (d a b : Nat) : List (Prog isa) := [sub3 aTmp a b, .block [.str .r11 .r8 d]]

/-! ## Setup and the inputs -/

/-- `W = p_len / 2 + 4`, the stride, `W` into the division's header, and
every array zeroed. -/
def setupK : List Instr :=
  ctxB ++ [.ldrSp .r9 aoPl, .mov .r9 (.shifted .r9 .lsr 1), .dp .add .r9 .r9 (.imm 4)] ++ stride ++
  [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
    .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

/-- `[j] :=` the bytes of the stack arguments at `o` and `o + 4`. -/
def loadArg (o j : Nat) : List (Prog isa) := [.block [.ldrSp .r4 o, .ldrSp .r6 (o + 4)], Rsa.Arm.CrtValues.load j]

/-- The constants 1, 2, 3, `2^(32 W − 1)`, `2^(16 p_len − 1)` and `2^33`. -/
def consts : List Instr :=
  setWd aOne 0 1 ++ setWd aTwo 0 2 ++ setWd aThree 0 3 ++ setHi aMod 2 4 0x80000000 ++
    setHi aTop 2 20 0x80000000 ++ setWd aC33 4 2

/-- The working space, `p`, `q`, `e` and the constants. -/
def loads : Prog isa :=
  seqs ([.block setupK, zero] ++ loadArg aoP aP0 ++ loadArg aoQ aQ0 ++ loadArg aoE aE ++ [.block consts])

/-! ## The primes -/

/-- `p ≥ q`, `p − 1` and `q − 1`. -/
def primes : Prog isa := seqs (ltS sLt aP0 aQ0 ++ [sel aP aP0 aQ0 sLt, sel aQ aQ0 aP0 sLt] ++
  ltS sPz aP aOne ++ [sel aPm aTmp aZero sPz] ++ ltS sQz aQ aOne ++ [sel aQm aTmp aZero sQz])

/-- `r6 := 8 p_len`. -/
def cnt8 : List Instr := [.ldrSp .r6 aoPl, .mov .r6 (.shifted .r6 .lsl 3)]

/-- `[o] := ([a] [b]) mod 2^(32 W − 1)` over the `r6` low bits of `[b]`,
through `mulMod`'s arrays, from `[o] = [c]`. -/
def mulFrom (o a b c : Nat) (k : List Instr) : Prog isa :=
  seqs [copy aMy b, copy aMx a, copy aMa c, .block k, mulMod aZero aMy aMx aMa aMod aMt, copy o aMa]

/-! ## `lcm(p − 1, q − 1)` -/

/-- `[j]` halved under the slot `sH` (through `aTmp` and `aTmp2`). -/
def halfSel (j : Nat) : Prog isa :=
  seqs [copy aTmp j, copy aTmp2 j, .block [.mov .r11 (.imm 0)], half aTmp2, sel j aTmp aTmp2 sH]

/-- The mask of `u` and `v` both even. -/
def bothEven : List Instr :=
  bitOf sBu aU ++ bitOf sBv aV ++
    [.ldr .r1 .r8 sBu, .ldr .r2 .r8 sBv, .dp .orr .r1 .r1 (.reg .r2), .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 sH]

/-- The halving's count decremented: Z when it reaches 0. -/
def cntDown : List Instr := [.ldr .r1 .r8 sHc, .subs .r1 .r1 (.imm 1), .str .r1 .r8 sHc]

/-- One step of the halving, counted down in `sHc`. -/
def halfStep : Prog isa := seqs [.block bothEven, halfSel aU, halfSel aV, halfSel aF, .block cntDown]

/-- `φ`, and `8 p_len` steps of the halving. -/
def halving : Prog isa :=
  seqs [mulFrom aF aPm aQm aZero cnt8, copy aU aPm, copy aV aQm, .block (cnt8 ++ [.str .r6 .r8 sHc]),
    .loop halfStep .ne]

/-- `inverse`'s start for `[a]` modulo `[m]` (copied into `aM`): `(u, v, x₁,
x₂) = (a, m, 1, 0)` and the negated modulus. -/
def invOf (a m : Nat) : Prog isa :=
  seqs [copy aM m, copy 0 a, copy 1 aM, copy 2 aOne, copy 3 aZero, sub3 aNM aZero aM, inverse]

/-- `v` odd by a swap, `[aG] := gcd(u, v)` (1 for `v < 2`). -/
def gcdUV : Prog isa := seqs ([.block (bitOf sVe aV ++ notS sVe sVe), sel aU2 aU aV sVe, sel aV2 aV aU sVe] ++
  ltS sV2 aV2 aTwo ++ [sel aTmp2 aV2 aThree sV2, invOf aU2 aTmp2, sel aG 1 aOne sV2])

/-- `[q] := [q] / [d]` (`[aDr] := [q] mod [d]`), and the context. -/
def divBy (q d : Nat) : Prog isa :=
  seqs [copy aDv d, .block (Rsa.Arm.Recover.clrW aDv ++ Rsa.Arm.CrtValues.divHdr q aDr aDv aDt), Rsa.Arm.Div.code,
    .block ctxW]

/-- `[aL] := lcm(p − 1, q − 1)`. -/
def lcmPart : Prog isa := seqs [halving, gcdUV, copy aL aF, divBy aL aG]

/-! ## `d = e⁻¹ mod L` -/

/-- Whether `e` is 0, 1, odd. -/
def eFlags : Prog isa := seqs [eqS sE0 aE aZero aTmp, eqS sE1 aE aOne aTmp, .block (bitOf sEo aE)]

/-- `e = 0`: none. -/
def dZero : List Instr := [.mov .r1 (.imm 0), .str .r1 .r8 sOk]

/-- `e = 1`: `d = 1`, for `L ≠ 1`. -/
def dOne : Prog isa := seqs [eqS sG aL aOne aTmp, .block (notS sOk sG), copy aD aOne]

/-- `e` odd, at least 3: `x = L⁻¹ mod e`, `t = e − x`, `d = (L t + 1) / e`. -/
def dOdd : Prog isa := seqs ([invOf aL aE, eqS sG 1 aOne aTmp] ++ ltS sL2 aL aTwo ++
  [.block (andNotS sOk sL2 sG), sub3 aTt aE 3, mulFrom aQd aL aTt aOne [.mov .r6 (.imm 64)], divBy aQd aE,
    copy aD aQd])

/-- `e` even: `d = e⁻¹ mod L` for an odd `L ≥ 3`. -/
def dEven : Prog isa := seqs ([.block (bitOf sLo aL)] ++ ltS sL3 aL aThree ++
  [.block (andNotS sGood sL3 sLo), sel aTmp2 aThree aL sGood, invOf aE aTmp2, eqS sG 1 aOne aTmp,
    .block (andS sOk sGood sG), copy aD 3])

/-- Z iff the slot `d` holds 1. -/
def isOne (d : Nat) : List Instr := [.ldr .r1 .r8 d, .cmp .r1 (.imm 1)]

/-- `d` and `sOk`, by `e`. -/
def dPart : Prog isa :=
  .seq (.block (isOne sE0))
    (.ite .eq (.block dZero)
      (.seq (.block (isOne sE1))
        (.ite .eq dOne
          (.seq (.block (isOne sEo)) (.ite .eq dOdd dEven)))))

/-- Z iff `sOk` and `d ≤ 2^(8 p_len)`. -/
def smallPart : Prog isa := seqs ([copy aC aOne, .block (setHi aC 1 8 1)] ++ ltS sSm aD aC ++
  [.block (andS sFl sSm sOk ++ isOne sFl)])

/-! ## The key -/

/-- Zeros to the output whose pointer and length are at frame bytes `o`
and `ol`. -/
def zeroOut (o ol : Nat) : Prog isa := .seq (.block [.ldrSp .r0 o, .ldrSp .lr ol, .mov .r2 (.imm 0)]) maskBytes

/-- Zeros to the seven outputs, and 2 returned. -/
def zeros : Prog isa := seqs [zeroOut aoN aoNl, zeroOut aoD aoNl, zeroOut aoP aoPl, zeroOut aoQ aoPl,
  zeroOut aoDp aoPl, zeroOut aoDq aoPl, zeroOut aoQi aoPl, .block [.mov .r0 (.imm 2)]]

/-- `qInv` into `aQi` (modulo `p`, or 3 for a `p` even or below 3), and
`sGq` the flag of `gcd(q, p) = 1`. -/
def qinvPart : Prog isa := seqs ([.block (bitOf sPo aP)] ++ ltS sP3 aP aThree ++
  [.block (andNotS sQg sP3 sPo), sel aTmp2 aThree aP sQg, invOf aQ aTmp2, eqS sGq 1 aOne aTmp, copy aQi 3])

/-- `[aTmp2] := [j]`, or 1 for `[j] = 0`. -/
def divisorOf (j : Nat) : Prog isa := seqs [eqS sZ j aZero aTmp, sel aTmp2 j aOne sZ]

/-- `dP` into `aDP` and `dQ` into `aDQ` (divisors 1 for `p − 1` or `q − 1` zero). -/
def crtPart : Prog isa := seqs [divisorOf aPm, copy aQd aD, divBy aQd aTmp2, copy aDP aDr, divisorOf aQm,
  copy aQd aD, divBy aQd aTmp2, copy aDQ aDr]

/-- `n = p q` into `aN`. -/
def nPart : Prog isa := mulFrom aN aP aQ aZero cnt8

/-- The mask of the checks into `sMask`. -/
def maskPart : Prog isa := seqs (ltS sTop aN aTop ++ [.block (bitOf sQo aQ)] ++ ltS sE3 aE aThree ++
  ltS sEv aE aC33 ++ [.block (andNotS sMask sTop sOk ++ andS sMask sMask sGq ++ andS sMask sMask sPo ++
    andS sMask sMask sQo ++ andS sMask sMask sEo ++ andNotS sE3 sE3 sEv ++ andS sMask sMask sE3)])

/-- The array `j`'s low bytes to the output at frame bytes `o` and `ol`. -/
def storeTo (o ol j : Nat) : List (Prog isa) := [.block [.ldrSp .r10 o, .ldrSp .r11 ol], Rsa.Arm.CrtValues.store j]

/-- The seven outputs under the mask, and the mask returned. -/
def stores : Prog isa := seqs (storeTo aoN aoNl aN ++ storeTo aoD aoNl aD ++ storeTo aoP aoPl aP ++
  storeTo aoQ aoPl aQ ++ storeTo aoDp aoPl aDP ++ storeTo aoDq aoPl aDQ ++ storeTo aoQi aoPl aQi ++
  [.block [.ldr .r0 .r8 sMask]])

/-- Once `d` is not too small, or does not exist. -/
def keyPart : Prog isa := seqs [qinvPart, crtPart, nPart, maskPart, stores]

def body : Prog isa := seqs [loads, primes, lcmPart, eFlags, dPart, smallPart, .ite .eq zeros keyPart]

/-- `vg_rsa_keygen_key`. -/
def code : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq body (.block PcFn.restore)) (.pop .r12 56)

end VG.Impl.RsaKeyGen.Arm.Key
