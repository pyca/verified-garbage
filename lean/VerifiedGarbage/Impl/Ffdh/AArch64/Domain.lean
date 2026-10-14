module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Impl.Rsa.AArch64.Keys

/-!
# Finite-field Diffie–Hellman on AArch64: the domain operations

`vg_ffdh_check_domain`, `vg_ffdh_check_public`, `vg_ffdh_check_private`,
`vg_ffdh_generate_key` and `vg_ffdh_exchange` (`Spec/Ffdh/Contract.lean`),
on the working spaces of RSA's CRT operation (`Impl/Rsa/AArch64/Crt.lean`):

* the outer workspace at `scratch` (`w = ⌈p_len / 8⌉` words, its base in
  `x0` between the steps), whose header holds the arguments, the pointers
  to g and q and the exponent's pointer and length; its array 1 holds
  `p − 1` for the check that q divides it;
* an inner workspace after its eight arrays (`Crt.wsNew`), followed by the
  32 entries of a window's table, which holds the modulus of the Montgomery
  arithmetic: p, or q while checking that it divides `p − 1`.

In the inner workspace for p (`pSetup`): p in `aN`, `-p⁻¹`, the number 1;
`R² mod p` (`r2Steps`) when an exponentiation follows. `pow` raises the
number of the bytes at a pointer and length in the outer header to the
exponent at another: the base and the accumulator (`R mod p`) in
Montgomery form, `R² mod p` kept in array `aX` meanwhile, then RSA's
five-bit fixed-window exponentiation (`WindowFive.expLoop`, the windows by
`vg_rsa_square_window5`), over every byte of the exponent; the result out
of Montgomery form in `aY`.

The checks of a value (`gt1`, `ltP`, `isOne`, `isZero`, `eqArr`, `ltArr`)
leave 1 or 0 in `x9` from a comparison's carry by `csel`, over all the
words of the arrays. The code branches on the domain and the public values,
which are public, and on the status returned; the comparisons of secret
values (a private scalar, a generated public value, a shared value) are
computed over all their words, and only the status they make is branched
on. Every loop counts down a register from a public count, but the scan for
q's first nonzero octet, which is public. No callee-saved register is
written; the return address is kept by the calls' wrappers.
-/

@[expose] public section

namespace VG.Impl.Ffdh.AArch64.Domain

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK)
open VG.Impl.Rsa.AArch64.Crt (ldw stw wsEnd wsNew loadArr copyArr zeroArr leave)

/-! ## The outer header -/

def sDom : Nat := sFn 0
def sDomLen : Nat := sFn 1
-- `sK = sFn 2`: `p_len`.
/-- `y`, the peer's value, or the generated public value's output. -/
def sY : Nat := sFn 3
/-- `x`, or the generated scalar's output. -/
def sX : Nat := sFn 4
def sXl : Nat := sFn 5
def sOut : Nat := sFn 6
/-- The exponent of a check of the subgroup: q's octets from its first
nonzero one, and their number. -/
def sEp : Nat := sFn 7
def sEl : Nat := sFn 8
def sRand : Nat := sFn 9
/-- The generated scalar's octets from the first of its bound's length. -/
def sXe : Nat := sFn 10
def sG : Nat := sFn 11
def sQ : Nat := sFn 12
/-- The inner workspace's base. -/
def sWs : Nat := sFn 13
/-- A flag kept across a call. -/
def sF : Nat := sFn 14
/-- The mask of the generated scalar's first octet. -/
def sMsk : Nat := sFn 15

/-! ## Entry, exit -/

/-- `x9` zero if p (`p_len` octets at `domain`) is not valid
(`Rsa.AArch64.invalid`: its first octet zero, even, or below `2^511`); `g`
and `q`'s pointers into their slots. -/
def domHead : List Instr :=
  [ldh .x2 sDom, ldh .x3 sK, .add .x .x4 .x2 .x3, sth .x4 sG, .add .x .x4 .x4 .x3, sth .x4 sQ] ++ invalid

/-- Return `r`. -/
def ret (r : Nat) : Prog isa := .block [movi .x0 r]

/-- `x3 := domain_len − 2 p_len`: zero iff there is no q. -/
def qTest : List Instr := [ldh .x3 sDomLen, ldh .x4 sK, .sub .x .x3 .x3 .x4, .sub .x .x3 .x3 .x4]

/-- Into the inner workspace. -/
def enter : Instr := ldh .x0 sWs

/-! ## The inner workspace -/

/-- The inner workspace after the outer one's arrays, for a modulus whose
length is in slot `sl` (`w = max(2, ⌈len / 8⌉)`); `x0` stays the outer. -/
def wsSetup (sl : Nat) : List Instr := [mov .x5 .x0] ++ wsEnd ++ wsNew sWs sl

/-- In the inner workspace: the modulus (pointer and length in the outer
slots `sp` and `sl`) into `aN`, `-m⁻¹`, and the number 1. -/
def modSetup (sp sl : Nat) : List (Prog isa) :=
  loadArr aN sp sl ++
  [.block ([ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++ [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]),
    setWord aOne]

/-- The inner workspace for p, entered. -/
def pSetup : List (Prog isa) := [.block (wsSetup sK ++ [enter])] ++ modSetup sDom sK

/-! ## Exponentiation -/

variable (window select : Prog isa) (mul : Nat → Nat → Nat → Prog isa)

/-- In the inner workspace for p, with `R² mod p` in `aR2`: `[aY] := b^e mod p`
for the base `b` (pointer and length in the outer slots `bp` and `bl`) and
the exponent `e` (`ep` and `el`); `R² mod p` stays in `aR2`. -/
def pow (bp bl ep el : Nat) : List (Prog isa) :=
  loadArr aXm bp bl ++ [mul aY aR2 aOne, mul aXm aXm aR2] ++ copyArr aX aR2 ++ copyArr Crt.aXc aXm ++
  [WindowFive.expLoop window mul select ep el, mul aY aY aOne] ++ copyArr aR2 aX

/-! ## Checks -/

/-- `x9 := 1` if the carry flag is set, else 0. -/
def carry1 : List Instr := [movi .x7 0, movi .x8 1, .csel .x .x9 .x8 .x7]

/-- `x9 := 1` if the carry flag is clear (a borrow), else 0. -/
def borrow1 : List Instr := [movi .x7 0, movi .x8 1, .csel .x .x9 .x7 .x8]

/-- `w` into `x12`, and the bases of arrays `a` and `b` into `x16` and `x17`. -/
def ptrs (a b : Nat) : List Instr := [ldh .x12 sW, ldh .x16 (sArr a), ldh .x17 (sArr b)]

/-- The borrow of `[a] − [b]` over `w` words (`cmpLoop`, from the carry set). -/
def cmpArr (a b : Nat) : List (Prog isa) :=
  [.block (ptrs a b ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7]), cmpLoop]

/-- `x9 := 1` if `[a] < [b]`, else 0. -/
def ltArr (a b : Nat) : List (Prog isa) := cmpArr a b ++ [.block borrow1]

/-- `x9 := 1` if `[a] ≥ [b]`, else 0. -/
def geArr (a b : Nat) : List (Prog isa) := cmpArr a b ++ [.block carry1]

/-- `x9 := 1` if `[a] = [b]`, else 0: the `OR` of the words of their `XOR`
(`Keys.xorBody`) is zero. -/
def eqArr (a b : Nat) : List (Prog isa) :=
  [.block (ptrs a b ++ [movi .x9 0, mov .x14 .x12]), countLoop .x14 Keys.xorBody,
    .block [movi .x7 0, movi .x8 1, .subs .x .x3 .x9 .x8, .csel .x .x9 .x7 .x8]]

/-- With the number 1 in `aOne`: `x9 := 1` if `[a] > 1`. -/
def gt1 (a : Nat) : List (Prog isa) := ltArr aOne a

/-- `x9 := 1` if `[a] = 1`. -/
def isOne (a : Nat) : List (Prog isa) := eqArr a aOne

/-- `x9 := 1` if `[a] = 0` (`[a] < 1`). -/
def isZero (a : Nat) : List (Prog isa) := ltArr a aOne

/-- `x9 := 1` if `[a] ≠ 0` (`[a] ≥ 1`). -/
def isNonzero (a : Nat) : List (Prog isa) := geArr a aOne

/-- `x9 := 1` if `[a] | 1 < m` (for an odd `m`, `[a] < m − 1`): `[a]` into the
temporary array, its low bit set, and compared. -/
def ltP (a : Nat) : List (Prog isa) :=
  copyArr aTmp a ++ [.block [ldh .x16 (sArr aTmp)], .block [ld .x3 .x16, movi .x4 1, .logic .orr .x .x3 .x3 .x4,
    st .x3 .x16]] ++ ltArr aTmp aN

/-- `x9 := 1` if `[a]` is odd. -/
def isOdd (a : Nat) : List (Prog isa) :=
  [.block [ldh .x16 (sArr a)], .block [ld .x3 .x16, movi .x4 1, .logic .and .x .x9 .x3 .x4]]

/-- `x9 := x9 & [sF]`, and into `sF`. -/
def andF : List Instr := [ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF]

/-- `1 < [a] < p − 1` into `x9` (and `sF`). -/
def range (a : Nat) : List (Prog isa) :=
  gt1 a ++ [.block [sth .x9 sF]] ++ ltP a ++ [.block andF]

/-! ## The first nonzero octet -/

/-- In the outer workspace: from the octets at the pointer in slot `sp`
(`p_len` of them), the pointer to its first nonzero octet, or its last, into
`sEp`, and the number of octets from it into `sEl`; that octet in `x3`. -/
def scan (sp : Nat) : List (Prog isa) := [
  .block [ldh .x1 sp, ldh .x2 sK],
  .loop (.block [.ldrb .x4 .x1 0, movi .x7 0, movi .x8 1, .subs .x .x3 .x4 .x8, .csel .x .x5 .x7 .x8,
      movi .x9 2, .subs .x .x3 .x2 .x9, .csel .x .x6 .x8 .x7, .logic .and .x .x5 .x5 .x6, .add .x .x1 .x1 .x5,
      .sub .x .x2 .x2 .x5])
    (.nonzero .x .x5),
  .block [sth .x1 sEp, sth .x2 sEl, .ldrb .x3 .x1 0]]

/-! ## `vg_ffdh_check_public` -/

namespace CheckPublic

/-- `(domain, domain_len, p_len, y, y_len, scratch, scratch_len)`: the
arguments into the header at `scratch` (`x5`), whose base goes in `x0`. -/
def entry : List Instr :=
  [stw .x0 .x5 sDom, stw .x1 .x5 sDomLen, stw .x2 .x5 sK, stw .x3 .x5 sY, mov .x0 .x5]

/-- With q: `y^q mod p = 1`. -/
def subgroup : List (Prog isa) :=
  scan sQ ++ [.block [enter]] ++ r2Steps mul ++ pow window select mul sY sK sEp sEl ++
  isOne aY ++ [.block [mov .x0 .x9]]

def main : Prog isa :=
  seqs ([.block head] ++ pSetup ++ loadArr aXm sY sK ++ range aXm ++
    [.ite (.zero .x .x9) (ret 0) (.seq (.block (leave :: qTest)) (.ite (.zero .x .x3) (ret 1)
      (seqs (subgroup window select mul))))])

/-- `vg_ffdh_check_public`. -/
def code : Prog isa :=
  .seq (.block (entry ++ domHead)) (.ite (.zero .x .x9) (ret 0) (main window select mul))

end CheckPublic

/-! ## `vg_ffdh_check_domain` -/

namespace CheckDomain

/-- `(domain, domain_len, p_len, scratch, scratch_len)`. -/
def entry : List Instr := [stw .x0 .x3 sDom, stw .x1 .x3 sDomLen, stw .x2 .x3 sK, mov .x0 .x3]

/-- In the outer workspace: `p − 1` into array `aX`. -/
def pMinus1 : List (Prog isa) := [
  zeroArr aX,
  .block [ldh .x1 sDom, ldh .x2 sK, ldh .x8 (sArr aX)],
  loadBE,
  .block [ld .x3 .x8, .subImm .x .x3 .x3 1, st .x3 .x8]]

/-- With q, once `1 < g < p − 1` (in the inner workspace for p): q odd,
`2 < q < p − 1`; `q ∣ p − 1`, by Montgomery reduction modulo q of `p − 1`
(`Crt.redc`), zero iff q divides it; `g^q mod p = 1`. -/
def withQ : List (Prog isa) :=
  [.block [enter]] ++ loadArr aXm sQ sK ++ isOdd aXm ++ [.block [sth .x9 sF]] ++ gt1 aXm ++ [.block andF] ++ ltP aXm ++
  [.block andF,
    .ite (.zero .x .x9) (ret 0) (seqs (
      [.block [leave]] ++ scan sQ ++ pMinus1 ++ [.block (wsSetup sEl ++ [enter])] ++ modSetup sEp sEl ++
      Crt.redc mul aX ++ isZero Crt.aXc ++
      [.ite (.zero .x .x9) (ret 0) (seqs (
        [.block [leave]] ++ pSetup ++ r2Steps mul ++ pow window select mul sG sK sEp sEl ++ isOne aY ++
        [.block [mov .x0 .x9]]))]))]

def main : Prog isa :=
  seqs ([.block head] ++ pSetup ++ loadArr aXm sG sK ++ range aXm ++
    [.ite (.zero .x .x9) (ret 0) (.seq (.block (leave :: qTest)) (.ite (.zero .x .x3) (ret 1)
      (seqs (withQ window select mul))))])

/-- `vg_ffdh_check_domain`. -/
def code : Prog isa :=
  .seq (.block (entry ++ domHead)) (.ite (.zero .x .x9) (ret 0) (main window select mul))

end CheckDomain

/-! ## `vg_ffdh_exchange` -/

namespace Exchange

/-- `(out, out_len, domain, domain_len, p_len, x, x_len, peer, peer_len,
scratch, scratch_len)`: `scratch` the second stack argument. -/
def entry : List Instr :=
  [.ldrSp .x8 8, stw .x0 .x8 sOut, stw .x2 .x8 sDom, stw .x3 .x8 sDomLen, stw .x4 .x8 sK, stw .x5 .x8 sX,
    stw .x6 .x8 sXl, stw .x7 .x8 sY, mov .x0 .x8]

/-- With z in `aY`, its flag `1 < z < p − 1` in `x9` and `sF`: z masked by
the flag to `out` (zeros for 0), and the flag returned, without a branch. -/
def main : Prog isa :=
  seqs ([.block head] ++ pSetup ++ r2Steps mul ++ pow window select mul sY sK sX sXl ++ range aY ++
    [.block [ldh .x12 sW, ldh .x8 (sArr aY), ldh .x5 Crt.sLink, ldw .x1 .x5 sOut, ldw .x9 .x5 sK,
      .add .x .x1 .x1 .x9, movi .x7 0, ldh .x3 sF, .sub .x .x15 .x7 .x3],
      storeBE, .block [ldh .x0 sF]])

/-- `vg_ffdh_exchange`. -/
def code : Prog isa :=
  .seq (.block (entry ++ domHead)) (.ite (.zero .x .x9) (ret 0) (main window select mul))

end Exchange

/-! ## `vg_ffdh_check_private` -/

namespace CheckPrivate

/-- `(domain, domain_len, p_len, y, y_len, x, x_len, scratch, scratch_len)`:
`scratch` in `x7`. -/
def entry : List Instr :=
  [stw .x0 .x7 sDom, stw .x1 .x7 sDomLen, stw .x2 .x7 sK, stw .x3 .x7 sY, stw .x5 .x7 sX, stw .x6 .x7 sXl,
    mov .x0 .x7]

/-- `x9 := 1` if the scalar in `aXm` is in `1..q` (`1..p − 1` without q):
not zero, and below q (in `aY`), or with `[aXm] | 1 < p`. -/
def scalarRange : List (Prog isa) :=
  isNonzero aXm ++ [.block [sth .x9 sF, leave], .block qTest,
    .ite (.zero .x .x3) (seqs ([.block [enter]] ++ ltP aXm))
      (seqs ([.block [enter]] ++ loadArr aY sQ sK ++ ltArr aXm aY)),
    .block andF]

/-- With y valid: with q, `y^q mod p = 1`; then `g^x mod p = y`. -/
def tail : List (Prog isa) :=
  r2Steps mul ++
  [.block [leave], .block qTest,
    .ite (.zero .x .x3) (.block [enter, movi .x9 1])
      (seqs (scan sQ ++ [.block [enter]] ++ pow window select mul sY sK sEp sEl ++ isOne aY)),
    .ite (.zero .x .x9) (ret 0)
      (seqs (pow window select mul sG sK sX sXl ++ loadArr aXm sY sK ++ eqArr aY aXm ++ [.block [mov .x0 .x9]]))]

def main : Prog isa :=
  seqs ([.block head] ++ pSetup ++ loadArr aXm sX sXl ++ scalarRange ++
    [.ite (.zero .x .x9) (ret 2) (seqs (loadArr aXm sY sK ++ range aXm ++
      [.ite (.zero .x .x9) (ret 0) (seqs (tail window select mul))]))])

/-- `vg_ffdh_check_private`. -/
def code : Prog isa :=
  .seq (.block (entry ++ domHead)) (.ite (.zero .x .x9) (ret 0) (main window select mul))

end CheckPrivate

/-! ## `vg_ffdh_generate_key` -/

namespace GenerateKey

/-- `(x, x_len, y, y_len, domain, domain_len, p_len, rand, rand_len,
scratch, scratch_len)`: `scratch` the second stack argument. -/
def entry : List Instr :=
  [.ldrSp .x8 8, stw .x0 .x8 sX, stw .x2 .x8 sY, stw .x4 .x8 sDom, stw .x5 .x8 sDomLen, stw .x6 .x8 sK,
    stw .x7 .x8 sRand, mov .x0 .x8]

/-- The mask `2^b − 1` of the octet in `x3` (`b` its bit length), in
`x3`. -/
def smear : List Instr :=
  [.lsr .x .x5 .x3 1, .logic .orr .x .x3 .x3 .x5, .lsr .x .x5 .x3 2, .logic .orr .x .x3 .x3 .x5,
    .lsr .x .x5 .x3 4, .logic .orr .x .x3 .x3 .x5]

/-- The bound's scan, in the outer workspace: q's, or p's, whose first
nonzero octet is `p − 1`'s; the pointer to that octet in `sEp`, the number
of octets from it (`n`) in `sEl`, the octet in `x3`. -/
def bound : List (Prog isa) := [
  .block qTest,
  .ite (.zero .x .x3) (seqs (scan sDom)) (seqs (scan sQ))]

/-- The loop's body: `rand`'s octet `x10` (at `x1`) to `x` (at `x2`): zero
before octet `x11 = p_len − n`, and'ed with the mask `x12` at it, kept
after it. -/
def cutBody : List Instr :=
  [.ldrb .x4 .x1 0, .subs .x .x5 .x10 .x11, .csel .x .x6 .x13 .x7, .logic .eor .x .x5 .x10 .x11,
    movi .x8 1, .subs .x .x5 .x5 .x8, .csel .x .x6 .x6 .x12, .logic .and .x .x4 .x4 .x6, .strb .x4 .x2 0,
    .addImm .x .x1 .x1 1, .addImm .x .x2 .x2 1, .addImm .x .x10 .x10 1]

/-- In the outer workspace: the scalar's octets to `x`: `p_len` octets of
`rand`, cut to the bound's bit length. -/
def scalar : List (Prog isa) := bound ++ [
  .block (smear ++ [mov .x12 .x3, ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11, ldh .x2 sX,
    ldh .x1 sRand, movi .x13 255, movi .x7 0, movi .x10 0, ldh .x14 sK]),
  countLoop .x14 cutBody]

/-- Zeros to `x` and `y`, and `r` returned. -/
def fail (r : Nat) : Prog isa := seqs [Keys.zeroOut sX sK, Keys.zeroOut sY sK, ret r]

/-- The `p_len` octets at the outer slot `sPtr` and'ed with the mask in
`x15`: kept for all ones, zeros for 0. -/
def maskOut (sPtr : Nat) : Prog isa :=
  .seq (.block [ldh .x1 sPtr, ldh .x2 sK])
    (countLoop .x2 [.ldrb .x4 .x1 0, .logic .and .x .x4 .x4 .x15, .strb .x4 .x1 0, .addImm .x .x1 .x1 1])

/-- With the scalar in range: the bound's scan again, for the scalar's
significant octets in `x` (`sEp`, `sEl`); `y = g^x mod p` to `y`; the flag
of `1 < y < p − 1` and, with q, `y^q mod p = 1`, in the outer `sF`; then x
and y masked by the flag (zeros for 0) and `3 − 2 flag` returned, without a
branch. -/
def tail : List (Prog isa) :=
  r2Steps mul ++ [.block [leave]] ++ bound ++
  [.block [ldh .x10 sK, ldh .x11 sEl, .sub .x .x11 .x10 .x11, ldh .x2 sX, .add .x .x3 .x2 .x11, sth .x3 sEp,
    enter]] ++
  pow window select mul sG sK sEp sEl ++ range aY ++
  [.block [ldh .x12 sW, ldh .x8 (sArr aY), ldh .x5 Crt.sLink, ldw .x1 .x5 sY, ldw .x9 .x5 sK,
    .add .x .x1 .x1 .x9, movi .x7 0, .subImm .x .x15 .x7 1],
    storeBE,
    .block [ldh .x9 sF, leave, sth .x9 sF], .block qTest,
    .ite (.zero .x .x3) (.block [])
      (seqs (scan sQ ++ [.block [enter]] ++ pow window select mul sY sK sEp sEl ++ isOne aY ++
        [.block [leave, ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF]])),
    .block [ldh .x9 sF, movi .x7 0, .sub .x .x15 .x7 .x9],
    maskOut sX, maskOut sY,
    .block [ldh .x9 sF, movi .x0 3, .lsl .x .x9 .x9 1, .sub .x .x0 .x0 .x9]]

def main : Prog isa :=
  seqs ([.block head] ++ pSetup ++ [.block [leave]] ++ scalar ++ [.block [enter]] ++ loadArr aXm sX sK ++
    CheckPrivate.scalarRange ++
    [.ite (.zero .x .x9) (.seq (.block [leave]) (fail 2)) (seqs (tail window select mul))])

/-- `vg_ffdh_generate_key`. -/
def code : Prog isa :=
  .seq (.block (entry ++ domHead)) (.ite (.zero .x .x9) (ret 0) (main window select mul))

end GenerateKey

end VG.Impl.Ffdh.AArch64.Domain
