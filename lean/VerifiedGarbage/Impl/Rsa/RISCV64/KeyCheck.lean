module

public import VerifiedGarbage.Impl.Rsa.RISCV64.MulMod
public import VerifiedGarbage.Impl.Rsa.RISCV64.Div
public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked
public import VerifiedGarbage.Impl.Rsa.RISCV64.RecoverDet

/-! # The checks of an RSA private key on RISC-V

What `vg_rsa_check_crt_key` and `vg_rsa_check_key` share, as on PPC64LE
(`Impl/Rsa/PPC64LE/KeyCheck.lean`), in words of 64 bits. The entry saves the
callee-saved registers in the header of the working space
(`Impl/Rsa/RISCV64/KeyWs.lean`, `w = ⌈n_len / 8⌉`) and keeps the pointers and
lengths in registers, so that no address or count is loaded from memory:
`n` and its length in `s1` and `s2`, `p` and `p_len` in `s3` and `s4`, `q`
and `q_len` in `s5` and `s6`, `d` and its length in `a0` and `a1`, `dp`,
`dq` and `qinv` in `a2`, `a3` and `a6`, and `e` and `e_len` in `a4` and
`a5`. It reads `e` as `vg_rsa_public_precomputed_checked` does
(`PublicChecked.readE`), saturated at `2^33`, and checks it
(`PublicChecked.checkE`); then `n` as `vg_rsa_public_precompute` checks it
(`Precompute.check`). The one branch on data is on both, the public key; a
refusal returns 0 at once. `e`, below `2^33`, is then written to its array
from the register.

Then every check is computed whatever its outcome, and and'ed into the
header's `sMask`, which is returned:

* `p q = n`: `p` odd, `p` divides `n` and `p q ≡ n (mod 2^(64 w))`, which
  with `p` odd and `n, q < 2^(64 w)` give `p q = n`. Whether `p` divides `n`
  is whether the Montgomery product `n · 1 · R⁻¹ mod m` (`MontMul.tail`,
  `R = 2^(64 w)`) is 0, for the modulus `m = p | 1 | 2 [p | 1 = 1]`, which
  is odd and at least 3, and is `p` when `p` is odd and at least 3 (as the
  mask needs: `dP < p - 1` fails for `p = 1`); `p q mod 2^(64 w)` is
  `RecoverDet.mulLow`'s. Then `p` and `q` are odd, and clearing their low
  bits gives `p - 1` and `q - 1`.
* `dP < p - 1`, `dQ < q - 1` and `qInv < p`: the borrow of a subtraction.
* `q qInv ≡ 1 (mod p)`: the Montgomery products `q qInv' R⁻¹ mod m` and
  `1 · 1 · R⁻¹ mod m` equal, `qInv'` being `qInv` if `qInv < p` and 0
  otherwise, so that it is below `m`, as `tail` needs.
* `e dP ≡ 1 (mod p - 1)`, `e dQ ≡ 1 (mod q - 1)`: `mulMod` over the 33 bits
  of `e`, compared with 1.

`tail` runs on the arrays 16–23, which it sees as its own arrays 0–7 (the
key working space's arrays and header are laid out as `tail`'s, with a
base `16` arrays further), before `mulMod` uses them.

`vg_rsa_check_key` then checks `d < n` (a borrow), and `d ≡ 1/e` modulo
`p - 1` and `q - 1` by comparing `d mod (p - 1)` and `d mod (q - 1)` (two
more divisions) with `dP` and `dQ`.

Addresses and branches depend only on the pointers, the lengths, `n` and `e`.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.KeyCheck

open VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.Div

/-! ## The header

Bytes 0–95 hold the caller's `s0`–`s11`, 128–144 the slots of the shared
routines, 152 the check just computed and 160 the mask. -/

def sF : Nat := 152
def sMask : Nat := 160

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

/-- The entry: the working space (the stack argument at `sp + oS`) and the
registers saved there, the arguments kept by `moves`, then `e` read and
checked and `n` checked: `t0` is 0 if both are valid. `a4` keeps
`e · 2^31`. -/
def entry (oS : Nat) (moves : List Instr) : Prog isa :=
  .seq (.block (save oS ++ moves))
    (.seq PublicChecked.readE
      (.seq (.block (PublicChecked.checkE ++ [mov .a5 .s9, mov .a4 .s7, mov .s7 .s1, mov .s8 .s2]))
        (.seq Precompute.check (.block [.addi .t0 .a5 1, .logic .or .t0 .t0 .s0]))))

/-- `w` and the stride, and every array zeroed. -/
def setup : Prog isa := .seq (.block (setW .s2)) (zeroArrays nArr)

/-- `e` (below `2^33`) into its array, from `a4 = e · 2^31`. -/
def eArr : List Instr := ptr .t0 aE ++ [.shift .srl .d .t5 .a4 31, .store .d .t5 .t0 0]

/-! ## The checks -/

/-- The mask and'ed with the check `sF`. -/
def acc : List Instr := andS sMask sMask sF

/-- `[a] < [b]`. -/
def ltA (a b : Nat) : List (Prog isa) := [sub3 aW a b, .block (stBorrow sF ++ acc)]

/-- `[a] = [b]`. -/
def eqA (a b : Nat) : List (Prog isa) := [eqS sF a b, .block acc]

/-- The division of `[a]` by `[d]`. -/
def divA (a d : Nat) : List (Prog isa) := [copy aVQ a, copy aVD d, div aVQ aVR aVD aVT]

/-- `[aA] := ([y] mod 2^s7) [x] mod [m]`, `s7` set by `cnt`. -/
def mulA (y x m : Nat) (cnt : List Instr) : List (Prog isa) :=
  [copy aY y, copy aX x, copy aA aZ, .block cnt, mulMod aZ aY aX aA m aT]

/-- `33` steps, for `e < 2^33`. -/
def cnt33 : List Instr := [.li .s7 33]

/-! ## The Montgomery products -/

/-- `tail`'s modulus, its operands and its results: arrays 16, 17, 20, 21 and
22 (its arrays 0, 1, 4, 5 and 6); its accumulator and temporary are arrays
18 and 19. -/
def mM : Nat := 16
def mA : Nat := 17
def mB : Nat := 20
def mO : Nat := 21
def mO2 : Nat := 22

/-- `[o] := [a] [b] R⁻¹ mod [mM]`: `-[mM]⁻¹ mod 2⁶⁴` into `t1`
(`Precompute.minv`), `w` into `t0`, the arrays' addresses, then `tail`. -/
def mont (o a b : Nat) : Prog isa :=
  .seq (.block (ptr .a7 mM ++ Precompute.minv ++ [mov .t0 .s9] ++ ptr .a5 (mM + 2) ++ ptr .a6 (mM + 3) ++
    ptr .a2 o ++ ptr .a3 a ++ ptr .a4 b)) tail

/-- The low word of `[j]` or'ed with the slot `sl` shifted left by one. -/
def orSlot2 (j sl : Nat) : List Instr :=
  ptr .t0 j ++ [.load .d .t5 .t0 0, .load .d .t6 .s11 sl, .shift .sll .d .t6 .t6 1,
    .logic .or .t5 .t5 .t6, .store .d .t5 .t0 0]

/-- `[mM] := p | 1 | 2 [p | 1 = 1]`: odd and at least 3, and `p` if `p` is
odd and at least 3. -/
def setM : List (Prog isa) :=
  [copy mM aP, .block (orOne mM), eqS sF mM aOne, .block (orSlot2 mM sF)]

/-- `p` divides `n` (`n · 1 · R⁻¹ mod m = 0`) and `p q ≡ n (mod 2^(64 w))`. -/
def pqChecks : List (Prog isa) :=
  setM ++ [copy mA aN, copy mB aOne, mont mO mA mB] ++ eqA mO aZ ++
    [copy mO2 aZ, RecoverDet.mulLow mO2 aP aQ] ++ eqA mO2 aN

/-- `qInv < p`, then `q qInv' R⁻¹ ≡ 1 · 1 · R⁻¹ (mod m)`, for `qInv'` :=
`qInv` if `qInv < p`, else 0. -/
def qiChecks : List (Prog isa) :=
  ltA aQI aP ++ [sel mB aZ aQI sF, copy mA aQ, mont mO mA mB, copy mA aOne, mont mO2 mA mA] ++
    eqA mO mO2

/-- `1`, and the mask `p` odd. -/
def start : List (Prog isa) := [.block (setOne aOne ++ bitOf sMask aP)]

/-- The checks of `p q = n`, of `qInv`, then `p - 1` and `q - 1` and the
checks of `dP` and `dQ`. -/
def crtChecks : List (Prog isa) := pqChecks ++ qiChecks ++
  [copy aM1 aP, .block (clrLow aM1), copy aM2 aQ, .block (clrLow aM2)] ++
  ltA aDP aM1 ++ mulA aE aDP aM1 cnt33 ++ eqA aA aOne ++
  ltA aDQ aM2 ++ mulA aE aDQ aM2 cnt33 ++ eqA aA aOne

/-- The checks of `d`: `d < n`, `d mod (p - 1) = dP` and `d mod (q - 1) = dQ`. -/
def dChecks : List (Prog isa) :=
  ltA aD aN ++ divA aD aM1 ++ eqA aVR aDP ++ divA aD aM2 ++ eqA aVR aDQ

/-! ## Exit -/

/-- The mask returned. -/
def ret : List Instr := [.load .d .a0 .s11 sMask]

/-- 0 returned. -/
def ret0 : List Instr := [.li .a0 0]

/-- A function: the entry (the working space the stack argument at `sp +
oS`, the arguments kept by `moves`), then if `e` and `n` are valid the
arrays set up, the numbers read by `loads` and the checks `body`, and the
exit. -/
def fn (oS : Nat) (moves : List Instr) (loads body : List (Prog isa)) : Prog isa :=
  .seq (entry oS moves)
    (.seq (.ite (.zero .t0) (seqs ([setup, .block eArr] ++ loads ++ body ++ [.block ret]))
        (.block ret0))
      (.block restore))

end VG.Impl.Rsa.RISCV64.KeyCheck
