module

public import VerifiedGarbage.Impl.Rsa.Arm.MulMod
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Impl.Bignum.Arm.ExponentCheck

/-! # The checks of an RSA private key on ARMv7

What `vg_rsa_check_crt_key` and `vg_rsa_check_key` share. Both are
frameless: the entry saves `r4`–`r11` and `lr` in the header of the working
space (`Impl/Rsa/Arm/KeyWs.lean`, `w = ⌈n_len / 4⌉`), with `e` and `e_len`,
zeroes every array, reads the numbers into arrays (`e` and `n` from the
registers, the others from the stack arguments) and checks `n` as
`vg_rsa_public_checked` checks it. If it is valid, `e` is checked as
`vg_rsa_public_checked` checks it. These are the only branches on data, both
on the public key; either refusal returns 0 at once.

Then every check is computed whatever its outcome, and and'ed into the
header's `sMask`, which is returned:

* `p q = n`: `p` odd, `n / p = q` and `n mod p = 0`, by the fixed-iteration
  division (`Impl/Rsa/Arm/Div.lean`). Then `p` and `q` are odd, and clearing
  their low bits gives `p - 1` and `q - 1`.
* `dP < p - 1`, `dQ < q - 1` and `qInv < p`: the borrow of a subtraction.
* `e dP ≡ 1 (mod p - 1)`, `e dQ ≡ 1 (mod q - 1)`: `mulMod` over the 33 bits
  of `e` (it is below `2^33`), compared with 1; `q qInv ≡ 1 (mod p)`: `mulMod`
  over the `32 w` bits of `q`.

`vg_rsa_check_key` then checks `d < n` (a borrow), and `d ≡ 1/e` modulo
`p - 1` and `q - 1` by comparing `d mod (p - 1)` and `d mod (q - 1)` (two
more divisions) with `dP` and `dQ`: once the checks above hold, `dP` is the
inverse of `e` modulo `p - 1`, and `d e ≡ 1 (mod p - 1)` exactly when
`d ≡ dP`.

Addresses and branches depend only on the pointers, the lengths, `n` and `e`.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.KeyCheck
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

/-! ## The header

Bytes 0–19 are the division's (16: `w`); 20–52 hold `r4`–`r11` and `lr`,
56 and 60 `e` and `e_len`, 100–112 the slots of the shared routines, 116
the check just computed and 120 the mask. -/

def sE : Nat := 56
def sEl : Nat := 60
def sF : Nat := 116
def sMask : Nat := 120

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

/-- `r4`–`r11` and `lr`, `e` and `e_len` saved at `r12`; the base into `r8`,
`n` and `n_len` into `r10` and `r11`, `e` and `e_len` into `r4` and `r6`. -/
def entrySave : List Instr :=
  [.str .r4 .r12 20, .str .r5 .r12 24, .str .r6 .r12 28, .str .r7 .r12 32, .str .r8 .r12 36,
   .str .r9 .r12 40, .str .r10 .r12 44, .str .r11 .r12 48, .str .lr .r12 52,
   .str .r2 .r12 sE, .str .r3 .r12 sEl, .mov .r8 (.reg .r12), .mov .r10 (.reg .r0), .mov .r11 (.reg .r1),
   .mov .r4 (.reg .r2), .mov .r6 (.reg .r3)]

/-- `w = ⌈n_len / 4⌉` into `r9` from `n_len` in `r11`, and the stride into `r7`. -/
def ctxK : List Instr := [.dp .add .r9 .r11 (.imm 3), .mov .r9 (.shifted .r9 .lsr 2)] ++ stride

/-- `w` into the division's header, and every array zeroed. -/
def setup : List Instr :=
  ctxK ++ [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
   .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

/-- `[j] :=` the stack argument at `o` (`o + 4` bytes long). -/
def loadArg (o j : Nat) : List (Prog isa) := [.block (CrtValues.args o (o + 4)), CrtValues.load j]

/-- The entry, for the working space at the stack offset `oS` and the
numbers at the stack offsets `args` (pointer offset, array): every array
zero, then `e`, the stack arguments and `n` read, and `n` checked (Z if it is
valid). -/
def entry (oS : Nat) (args : List (Nat × Nat)) : Prog isa := seqs ([
  .block ([.ldrSp .r12 oS] ++ entrySave ++ setup), zero, CrtValues.load aE] ++
  (args.flatMap fun a => loadArg a.1 a.2) ++ [
  .block [.mov .r4 (.reg .r10), .mov .r6 (.reg .r11)], CrtValues.load aN, .block modulusCheck])

/-- `e` checked: Z if it is valid. -/
def eCheck : Prog isa := seqs [.block [.ldr .r1 .r8 sE, .ldr .lr .r8 sEl], exponentCheck,
  .block [.cmp .r7 (.imm 1)]]

/-! ## The checks -/

/-- `r7`–`r9` again after a division, which keeps only `r8`: `w` from its header. -/
def ctxDiv : List Instr := [.ldr .r9 .r8 16] ++ stride

/-- The mask and'ed with the check `sF`. -/
def acc : List Instr := andS sMask sMask sF

/-- `[a] < [b]`. -/
def ltA (a b : Nat) : List (Prog isa) := [sub3 aW a b, .block ([.str .r11 .r8 sF] ++ acc)]

/-- `[a] = [b]`. -/
def eqA (a b : Nat) : List (Prog isa) := [eqS sF a b aW, .block acc]

/-- The division of `[a]` by `[d]` set up. -/
def divSet (a d : Nat) : List (Prog isa) :=
  [copy aVQ a, copy aVD d, .block (CrtValues.divHdr aVQ aVR aVD aVT)]

/-- `[a] := ([y] mod 2^r6) [x] mod [m]`, `r6` set by `cnt`. -/
def mulA (y x m : Nat) (cnt : List Instr) : List (Prog isa) :=
  [copy aY y, copy aX x, copy aA aZ, .block cnt, mulMod aZ aY aX aA m aT]

/-- `33` steps, for `e < 2^33`. -/
def cnt33 : List Instr := [.mov .r6 (.imm 33)]
/-- `32 w` steps. -/
def cntW : List Instr := [.mov .r6 (.shifted .r9 .lsl 5)]

/-- From the arrays read: `w` again, `1`, the mask `p` odd, and the division
of `n` by `p` set up. -/
def start : Prog isa := seqs ([.block (ctxK ++ setOne aOne ++ bitOf sMask aP)] ++ divSet aN aP)

/-- After the division: `n / p = q`, `n mod p = 0`, `p - 1` and `q - 1`, and
the checks of `dP`, `dQ` and `qInv`. -/
def crtChecks : Prog isa := seqs (eqA aVQ aQ ++ eqA aVR aZ ++
  [copy aM1 aP, .block (clrLow aM1), copy aM2 aQ, .block (clrLow aM2)] ++
  ltA aDP aM1 ++ mulA aE aDP aM1 cnt33 ++ eqA aA aOne ++
  ltA aDQ aM2 ++ mulA aE aDQ aM2 cnt33 ++ eqA aA aOne ++
  ltA aQI aP ++ mulA aQ aQI aP cntW ++ eqA aA aOne)

/-- The checks of `vg_rsa_check_crt_key`. -/
def crtBody : Prog isa := seqs [start, Rsa.Arm.Div.code, .block ctxDiv, crtChecks]

/-- `d < n`, and the division of `d` by `p - 1` set up. -/
def dChecks1 : Prog isa := seqs (ltA aD aN ++ divSet aD aM1)
/-- `d mod (p - 1) = dP`, and the division of `d` by `q - 1` set up. -/
def dChecks2 : Prog isa := seqs (eqA aVR aDP ++ divSet aD aM2)
/-- `d mod (q - 1) = dQ`. -/
def dChecks3 : Prog isa := seqs (eqA aVR aDQ)

/-- The checks of `vg_rsa_check_key`. -/
def keyBody : Prog isa := seqs [crtBody, dChecks1, Rsa.Arm.Div.code, .block ctxDiv, dChecks2,
  Rsa.Arm.Div.code, .block ctxDiv, dChecks3]

/-! ## Exit -/

/-- The mask returned. -/
def ret : List Instr := [.ldr .r0 .r8 sMask]

/-- 0 returned. -/
def ret0 : List Instr := [.mov .r0 (.imm 0)]

/-- `r4`–`r11` and `lr` restored, the working space at the stack offset `oS`. -/
def restore (oS : Nat) : List Instr :=
  [.ldrSp .r12 oS, .ldr .r4 .r12 20, .ldr .r5 .r12 24, .ldr .r6 .r12 28, .ldr .r7 .r12 32,
   .ldr .r8 .r12 36, .ldr .r9 .r12 40, .ldr .r10 .r12 44, .ldr .r11 .r12 48, .ldr .lr .r12 52]

/-- A function: the entry, the checks `body` if `n` and `e` are valid, the exit. -/
def fn (oS : Nat) (args : List (Nat × Nat)) (body : Prog isa) : Prog isa := seqs [
  entry oS args,
  .ite .eq (.seq eCheck (.ite .eq (.seq body (.block ret)) (.block ret0))) (.block ret0),
  .block (restore oS)]

end VG.Impl.Rsa.Arm.KeyCheck
