module

public import VerifiedGarbage.Impl.Rsa.Arm.Recover

/-!
# A prepared Miller–Rabin round on ARMv7

`vg_miller_rabin_round(ws, ws_len)` (`Spec/MillerRabin.lean`), in the compact
representation, with the frame of `vg_rsa_public_checked`: `r0`–`r12` and
`lr` pushed (56 bytes), so that frame word 0 holds `ws`, as Montgomery
multiplication (`montOp`) needs it.

The working space is read as the key working space of the RSA key
operations (`Impl/Rsa/Arm/KeyWs.lean`) with its base `r8 = ws + 96` and
`W = 2 w + 2` words of 32 bits: then its stride `4 (W + 2) = 8 (w + 2)` is
that of the 64-bit arrays, and its array `j` is the 64-bit array `j`. Its
header slots used here are the header words 23, 26 and 29 of `ws`, which the
contract lets the round change.

Binary exponentiation rather than windows of four bits, over the bits of
`c − 1` from the top (`Proof/RsaKeyGen/MillerRabin.lean`'s `mrRun`): the
bits of `c` but its lowest, which is shifted out of a copy of `c` (array
11) one at a time, from its `64 w`th bit down to bit 1. Each bit squares `y`
(array 6, in Montgomery form), multiplies it by the witness (a copy in array
8) or by 1 (a copy in array 12), selected under the bit, and sets the flag
to `y = 1 ∨ y = −1` for a set bit, or or's `y = −1` (a copy in array 13)
into it for a clear one. The copies have their words above the `w` of 64
bits cleared, as each product has, so that the comparisons are of numbers.
The number of steps depends only on `w`.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.Arm

open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

/-! ## The key working space's view -/

/-- The key working space's base: `ws + 96`. -/
def kOff : Nat := 96

/-- `r8 := ws + 96`, `r9 := W = 2 w + 2` and `r7 :=` the stride, from `ws` in
`r0`. -/
def ctx : List Instr :=
  [.dp .add .r8 .r0 (.imm (BitVec.ofNat 32 kOff)), .ldr .r9 .r0 48, .mov .r9 (.shifted .r9 .lsl 1),
    .dp .add .r9 .r9 (.imm 2)] ++ stride

/-! ## Slots: offsets from `r8`, in the header words 23, 26 and 29 of `ws` -/

def sE1 : Nat := 88
def sE2 : Nat := 92
def sBit : Nat := 116
def sF : Nat := 136
def sK : Nat := 140

/-! ## Arrays -/

/-- The witness (in Montgomery form), and the multiplicand. -/
def aX : Nat := 5
/-- `y`. -/
def aY : Nat := 6
/-- The witness's copy. -/
def aB : Nat := 8
/-- `c`'s copy, shifted left one bit a step. -/
def aE : Nat := 11
/-- `1` and `−1` (Montgomery forms), copied. -/
def aOne : Nat := 12
def aM1 : Nat := 13
/-- The comparisons' temporary. -/
def aT : Nat := 14

/-! ## The round -/

/-- `[o] := [a]`, its words above the low `2 w` cleared. -/
def copyClr (o a : Nat) : List (Prog isa) := [copy o a, .block (Rsa.Arm.Recover.clrTop o)]

/-- The copies, `y := 1`, the flag 0 and the count `64 w − 1`. -/
def prep : List (Prog isa) :=
  [.block ctx, seqs (copyClr aE 0), seqs (copyClr aB aX), seqs (copyClr aOne 9), seqs (copyClr aM1 10),
   copy aY aOne,
   .block [.mov .r1 (.imm 0), .str .r1 .r8 sF, .mov .r1 (.shifted .r9 .lsl 5), .dp .sub .r1 .r1 (.imm 65),
     .str .r1 .r8 sK]]

/-- The top bit of `c`'s copy shifted out into the slot `sBit`. -/
def bitOut : List (Prog isa) :=
  [.block (ptr .r0 aE ++ [.dp .sub .lr .r9 (.imm 2), .mov .r11 (.imm 0)]), shiftLeft,
   .block [.str .r11 .r8 sBit]]

/-- `[aY] := [aY] [b] R⁻¹ mod c`, then the context and `[aY]`'s top words cleared. -/
def mulY (b : Nat) : List (Prog isa) :=
  [.block [.ldrSp .r0 0], montOp aY aY b, .block (ctx ++ Rsa.Arm.Recover.clrTop aY)]

/-- The flag: `y = 1 ∨ y = −1` for a set bit, or'ed with `y = −1` for a clear one. -/
def flagUpd : List Instr :=
  [.ldr .r1 .r8 sBit, .ldr .r2 .r8 sE1, .ldr .r3 .r8 sE2, .ldr .r4 .r8 sF, .dp .and .r2 .r2 (.reg .r1),
   .dp .eor .r1 .r1 (.imm 1), .dp .and .r4 .r4 (.reg .r1), .dp .orr .r2 .r2 (.reg .r3),
   .dp .orr .r2 .r2 (.reg .r4), .str .r2 .r8 sF]

/-- The count decremented: Z when it reaches 0. -/
def cntNext : List Instr := [.ldr .r1 .r8 sK, .subs .r1 .r1 (.imm 1), .str .r1 .r8 sK]

/-- One bit. -/
def step : Prog isa := seqs [seqs bitOut, seqs (mulY aY), sel aX aOne aB sBit, seqs (mulY aX),
  eqS sE1 aY aOne aT, eqS sE2 aY aM1 aT, .block (flagUpd ++ cntNext)]

/-- The round's body: the flag returned in `r0`. -/
def body : Prog isa := seqs [seqs prep, .loop step .ne, .block [.ldr .r0 .r8 sF]]

/-- `vg_miller_rabin_round`. -/
def code : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq body (.block PcFn.restore)) (.pop .r12 56)

end VG.Impl.MillerRabin.Arm
