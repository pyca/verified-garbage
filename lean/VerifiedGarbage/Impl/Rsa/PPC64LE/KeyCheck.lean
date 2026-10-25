module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.MulMod
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-! # The checks of an RSA private key on PPC64LE

What `vg_rsa_check_crt_key` and `vg_rsa_check_key` share, as on ARMv7
(`Impl/Rsa/Arm/KeyCheck.lean`). The entry saves the nonvolatile registers it
uses in the header of the working space (`Impl/Rsa/PPC64LE/KeyWs.lean`,
`w = ⌈n_len / 4⌉`) and keeps the pointers and lengths in nonvolatile
registers, so that no address or count is loaded from memory: `n` and its
length in `r14` and `r15`, `d` and its length in `r16` and `r17`, `p` and
`p_len` in `r18` and `r19`, `q` and `q_len` in `r20` and `r21`, `dp`, `dq`
and `qinv` in `r22`, `r23` and `r26`. It reads `e` as
`vg_rsa_public_checked` does, saturated at `2^33`, and checks it; then `n`
as `vg_rsa_crt_values` checks it. These are the only branches on data, both
on the public key; either refusal returns 0 at once. `e`, below `2^33`, is
then written to its array from the register.

Then every check is computed whatever its outcome, and and'ed into the
header's `sMask`, which is returned:

* `p q = n`: `p` odd, `n / p = q` and `n mod p = 0`, by the fixed-iteration
  division (`Impl/Rsa/PPC64LE/Div.lean`). Then `p` and `q` are odd, and
  clearing their low bits gives `p - 1` and `q - 1`.
* `dP < p - 1`, `dQ < q - 1` and `qInv < p`: the borrow of a subtraction.
* `e dP ≡ 1 (mod p - 1)`, `e dQ ≡ 1 (mod q - 1)`: `mulMod` over the 33 bits
  of `e`, compared with 1; `q qInv ≡ 1 (mod p)`: `mulMod` over the
  `8 q_len` bits of `q`.

`vg_rsa_check_key` then checks `d < n` (a borrow), and `d ≡ 1/e` modulo
`p - 1` and `q - 1` by comparing `d mod (p - 1)` and `d mod (q - 1)` (two
more divisions) with `dP` and `dQ`: once the checks above hold, `dP` is the
inverse of `e` modulo `p - 1`, and `d e ≡ 1 (mod p - 1)` exactly when
`d ≡ dP`.

Addresses and branches depend only on the pointers, the lengths, `n` and `e`.
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.KeyCheck

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys VG.Impl.Rsa.PPC64LE.Div

/-! ## The header

Bytes 0–119 hold the saved `r14`–`r24`, `r26` and `r29`–`r31`, 124–132 the
slots of the shared routines, 136 the check just computed and 140 the mask. -/

def sF : Nat := 136
def sMask : Nat := 140

/-! ## The arrays -/

def aZ : Nat := 0
def aOne : Nat := 1
def aN : Nat := 2
def aE : Nat := 3
def aP : Nat := 4
def aQ : Nat := 5
def aDP : Nat := 6
def aDQ : Nat := 7
def aQI : Nat := 8
def aD : Nat := 9
def aM1 : Nat := 10
def aM2 : Nat := 11
/-- The division's quotient, remainder, divisor and temporary. -/
def aVQ : Nat := 12
def aVR : Nat := 13
def aVD : Nat := 14
def aVT : Nat := 15
/-- `mulMod`'s multiplier, multiplicand, accumulator, and its four
temporaries 19–22. -/
def aY : Nat := 16
def aX : Nat := 17
def aA : Nat := 18
def aT : Nat := 19
/-- The temporary of the comparisons. -/
def aW : Nat := 23
/-- The number of arrays. -/
def nArr : Nat := 24

/-! ## Entry -/

/-- The working space's base into `r11` from the stack argument `oS`, the
nonvolatile registers saved there, and the base into `r31`. -/
def save (oS : Nat) : List Instr :=
  CrtValues.stackArg .r11 oS ++
  [.store .d .r14 .r11 0, .store .d .r15 .r11 8, .store .d .r16 .r11 16, .store .d .r17 .r11 24,
    .store .d .r18 .r11 32, .store .d .r19 .r11 40, .store .d .r20 .r11 48, .store .d .r21 .r11 56,
    .store .d .r22 .r11 64, .store .d .r23 .r11 72, .store .d .r24 .r11 80, .store .d .r26 .r11 88,
    .store .d .r29 .r11 96, .store .d .r30 .r11 104, .store .d .r31 .r11 112, .addi .r31 .r11 0]

/-- The entry: `save`, the register arguments `moves` kept, and `e` (in
`r5` and `r6`) read and checked: `r26` is all ones if it is valid, else 0,
and `r24` holds `e · 2^31`. -/
def entry (oS : Nat) (moves : List Instr) : Prog isa :=
  .seq (.block (save oS ++ moves ++ [.addi .r7 .r5 0, .addi .r8 .r6 0]))
    (.seq Bignum.PPC64LE.PublicChecked.readE (.block Bignum.PPC64LE.PublicChecked.checkE))

/-- `n` checked (0 in `r0` if it is valid). -/
def nCheck : Prog isa := .seq (.block [.addi .r9 .r14 0, .addi .r10 .r15 0]) CrtValues.check

/-- `w` and the stride, and every array zeroed. -/
def setup : Prog isa :=
  .seq (.block ([.addi .r29 .r15 3, .lsr .d .r29 .r29 2] ++ stride ++
      [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2]))
    (zeroArrays .r8)

/-- `e` (below `2^33`) into its array, from `r24 = e · 2^31`. -/
def eArr : List Instr :=
  ptr .r5 aE ++ [.lsr .d .r0 .r24 31, .store .w .r0 .r5 0, .lsr .d .r0 .r0 32, .store .w .r0 .r5 4]

/-- `[j] :=` the bytes at `rP`, `rL` of them. -/
def loadR (rP rL : Reg) (j : Nat) : List (Prog isa) :=
  [.block [.addi .r6 rP 0, .addi .r8 rL 0], CrtValues.load j]

/-! ## The checks -/

/-- The mask and'ed with the check `sF`. -/
def acc : List Instr := andS sMask sMask sF

/-- `[a] < [b]`. -/
def ltA (a b : Nat) : List (Prog isa) := [sub3 aW a b, .block (stBorrow sF ++ acc)]

/-- `[a] = [b]`. -/
def eqA (a b : Nat) : List (Prog isa) := [eqS sF a b, .block acc]

/-- The division of `[a]` by `[d]`. -/
def divA (a d : Nat) : List (Prog isa) := [copy aVQ a, copy aVD d, div aVQ aVR aVD aVT]

/-- `[aA] := ([y] mod 2^r4) [x] mod [m]`, `r4` set by `cnt`. -/
def mulA (y x m : Nat) (cnt : List Instr) : List (Prog isa) :=
  [copy aY y, copy aX x, copy aA aZ, .block cnt, mulMod aZ aY aX aA m aT]

/-- `33` steps, for `e < 2^33`. -/
def cnt33 : List Instr := [.li .r4 33]
/-- `8 q_len` steps, for `q < 2^(8 q_len)`. -/
def cntQ : List Instr := [.lsl .r4 .r21 3]

/-- `1`, the mask `p` odd, and `n` divided by `p`. -/
def start : List (Prog isa) := [.block (setOne aOne ++ bitOf sMask aP)] ++ divA aN aP

/-- After the division: `n / p = q`, `n mod p = 0`, `p - 1` and `q - 1`, and
the checks of `dP`, `dQ` and `qInv`. -/
def crtChecks : List (Prog isa) := eqA aVQ aQ ++ eqA aVR aZ ++
  [copy aM1 aP, .block (clrLow aM1), copy aM2 aQ, .block (clrLow aM2)] ++
  ltA aDP aM1 ++ mulA aE aDP aM1 cnt33 ++ eqA aA aOne ++
  ltA aDQ aM2 ++ mulA aE aDQ aM2 cnt33 ++ eqA aA aOne ++
  ltA aQI aP ++ mulA aQ aQI aP cntQ ++ eqA aA aOne

/-- The checks of `d`: `d < n`, `d mod (p - 1) = dP` and `d mod (q - 1) = dQ`. -/
def dChecks : List (Prog isa) :=
  ltA aD aN ++ divA aD aM1 ++ eqA aVR aDP ++ divA aD aM2 ++ eqA aVR aDQ

/-! ## Exit -/

/-- The mask returned. -/
def ret : List Instr := [.load .w .r3 .r31 sMask]

/-- 0 returned. -/
def ret0 : List Instr := [.li .r3 0]

/-- The saved registers restored, `r31` last. -/
def restore : List Instr :=
  [.load .d .r14 .r31 0, .load .d .r15 .r31 8, .load .d .r16 .r31 16, .load .d .r17 .r31 24,
    .load .d .r18 .r31 32, .load .d .r19 .r31 40, .load .d .r20 .r31 48, .load .d .r21 .r31 56,
    .load .d .r22 .r31 64, .load .d .r23 .r31 72, .load .d .r24 .r31 80, .load .d .r26 .r31 88,
    .load .d .r29 .r31 96, .load .d .r30 .r31 104, .load .d .r31 .r31 112]

/-- A function: the entry (the working space the stack argument `oS`, the
register arguments kept by `moves`), the stack arguments read by `stk`, the
checks of `n` and `e`, then if both are valid the arrays set up, the
numbers read by `loads` and the checks `body`, and the exit. -/
def fn (oS : Nat) (moves stk : List Instr) (loads body : List (Prog isa)) : Prog isa :=
  .seq (entry oS moves)
    (.seq (.ite (.zero .d .r26) (.block ret0)
      (.seq (.block stk) (.seq nCheck
        (.ite (.zero .d .r0) (seqs ([setup, .block eArr] ++ loads ++ body ++ [.block ret])) (.block ret0)))))
    (.block restore))

end VG.Impl.Rsa.PPC64LE.KeyCheck
