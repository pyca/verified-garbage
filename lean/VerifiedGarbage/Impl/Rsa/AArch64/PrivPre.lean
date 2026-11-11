module

public import VerifiedGarbage.Impl.Rsa.AArch64.Crt

/-!
# An RSA private key's precomputed values on AArch64

`vg_rsa_private_precompute(pre, pre_len, n, n_len, p, p_len, q, q_len,
scratch, scratch_len)`: the first eight arguments in `x0`–`x7`, `scratch`
and `scratch_len` on the stack (AAPCS64). With the modulus `n` (`k = n_len`
bytes) of `w = ⌈k / 8⌉` words and its factors `p` and `q`, writes `n` and
`R² mod n` (`w` words each), then `R_p² mod p` (`w_p = max(2, ⌈p_len / 8⌉)`
words) and `R_q² mod q` to `pre` and returns 1 if `n` is valid and
`p q = n`, and otherwise writes zeros and returns 0.

* `pre` is zeroed first (`zeroPre`), so that a modulus that is not valid
  leaves it zero, and so that `vg_rsa_private_crt`'s setup and checks
  (`Crt.nSetup`, `Crt.primesSetup`, `Crt.checks`), run with `pre` as the
  input and as `qInv` (and `p`, `q` as `dP`, `dQ`, which they do not read),
  find them zero: their mask is then that of `n` valid and `p q = n`, and
  `p` and `q` are kept under it, else 3.
* In each prime's workspace, `R_X² mod X` from `R² mod n` (`r2X`): reduced
  modulo `X` by `Crt.redc` (`x R_X^(-K)`, `K = ⌈w / w_X⌉`) and then by
  `R_X⁻¹` (Montgomery multiplications by 1) while more than `2 w_X` of its
  `2 w` words are left, it is `2^(64 e)` modulo `X` when `X` divides `n`
  (which the mask's being set implies), for the `e` words left; then
  doublings (`addMod`) to `2^(128 w_X)`, or, if `e ≤ w_X`, to
  `2^(64 w_X + w_X)` and six Montgomery squarings. It is written to `pre`
  and-ed with the mask (`phase`). For factors of half `n`'s words there are
  no further reductions, doublings or squarings. Every count depends only on
  `w` and `w_X` (`Proof/Bignum/PrimeR2.lean`).
* `n` and `R² mod n` (as `vg_rsa_public_precompute` computes them, in `n`'s
  workspace) are written to `pre` and-ed with the mask, and `mask & 1`
  returned (`outN`).

Nothing branches on `p` or `q`: the loops count lengths, and the code
branches only on `n` (its validity, and in `Crt.nSetup`).
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.PrivPre

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt
open VG.Impl.Bignum.Public hiding sI sBit sV
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Crt

/-- The arguments in the header at `scratch` (the first stack argument, into
`x8`): `pre` as the output, the input and `qInv`, `p` and `q` also as `dP`
and `dQ`; `x9 := 0` and `x10 := pre`, for `zeroPre`. -/
def entry : List Instr :=
  [.ldrSp .x8 0, stw .x0 .x8 sOut, stw .x2 .x8 sN, stw .x3 .x8 sK, stw .x0 .x8 sIn, stw .x4 .x8 sP,
    stw .x5 .x8 sPlen, stw .x6 .x8 sQ, stw .x7 .x8 sQlen, stw .x4 .x8 sDp, stw .x6 .x8 sDq, stw .x0 .x8 sQinv,
    movi .x9 0, mov .x10 .x0]

/-- `pre_len` (`x1`) words of `pre` := 0. -/
def zeroPre : Prog isa := countLoop .x1 [st .x9 .x10, next .x10]

/-- `x12` words from `[x16]` to `[x17]`, each and-ed with `x15`; both
pointers advanced past them. -/
def maskCopy : Prog isa :=
  .seq (.block [mov .x14 .x12]) (countLoop .x14 [ld .x3 .x16, .logic .and .x .x3 .x3 .x15, st .x3 .x17,
    next .x16, next .x17])

/-- `x4 := 1` if `2 w_X < x3`, else 0, for `w_X` in `x13` (`x7 = 0`,
`x8 = 1`). -/
def gtTest : List Instr := [.lsl .x .x6 .x13 1, .subs .x .x6 .x6 .x3, .csel .x .x4 .x7 .x8]

/-- `w` (`n`'s) into `x12` and `w_X` into `x5`, for the loop `x3 += w_X` while
`x3 < w` from `x3 = 0` (`Crt.gPow`'s). -/
def r2Load : List Instr :=
  [ldh .x5 sLink, ldw .x12 .x5 sW, ldh .x5 sW, movi .x3 0, movi .x7 0, movi .x8 1]

/-- `x3 += w_X` while `x3 < w`: `x3 := K w_X`. -/
def kLoop : Prog isa :=
  .loop (.block [.add .x .x3 .x3 .x5, .subs .x .x4 .x3 .x12, .csel .x .x4 .x7 .x8]) (.nonzero .x .x4)

/-- The words left, `e = 2 w - K w_X`, into slot `sV` and `x3`, and whether
more than `2 w_X` are (`gtTest`). -/
def eInit : List Instr := [.lsl .x .x4 .x12 1, .sub .x .x3 .x4 .x3, sth .x3 Crt.sV, mov .x13 .x5] ++ gtTest

/-- A further reduction: `[aXc] := [aXc] R_X⁻¹` and `e -= w_X`, and whether
more than `2 w_X` words are left. -/
def zTail : List Instr :=
  [ldh .x3 Crt.sV, ldh .x13 sW, .sub .x .x3 .x3 .x13, sth .x3 Crt.sV, movi .x7 0, movi .x8 1] ++ gtTest

def zBody (mul : Nat → Nat → Nat → Prog isa) : Prog isa := .seq (mul aXc aXc aOne) (.block zTail)

/-- From the words `e` left (slot `sV`): the doublings, `64 (w_X - e) + w_X`
if `e ≤ w_X`, else `64 (2 w_X - e)`, into slot `sBit` and `x3`, and into
`sV` 1 if `e ≤ w_X` (six squarings follow), else 0. -/
def cntBlk : List Instr :=
  [ldh .x3 Crt.sV, ldh .x13 sW, movi .x7 0, movi .x8 1, .subs .x .x5 .x13 .x3, .csel .x .x6 .x7 .x13,
    .add .x .x6 .x6 .x13, .sub .x .x6 .x6 .x3, .lsl .x .x6 .x6 6, .csel .x .x4 .x13 .x7, .add .x .x3 .x6 .x4,
    sth .x3 Crt.sBit, .csel .x .x4 .x8 .x7, sth .x4 Crt.sV]

/-- A doubling, `Y := Y + Y mod X` (`addMod`, which, unlike `double`, is
constant time for any modulus), counted down in `sBit`. -/
def r2Body : Prog isa :=
  .seq (addMod aY aY aY) (.block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit])

/-- In a prime's workspace: `[aY] := R_X² mod X` when `X` divides `n` (see
the file's description). -/
def r2X (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  redc mul aR2 ++ [
  .block r2Load,
  kLoop,
  .block eInit,
  .ite (.nonzero .x .x4) (.loop (zBody mul) (.nonzero .x .x4)) (.block [])] ++
  copyArr aY aXc ++ [
  .block cntBlk,
  .ite (.nonzero .x .x3) (.loop r2Body (.nonzero .x .x3)) (.block []),
  .block [ldh .x3 Crt.sV],
  .ite (.nonzero .x .x3) (seqs [mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY,
    mul aY aY aY]) (.block [])]

/-- In `n`'s workspace: the cursor into `pre` (`n`'s slot `sD`, which
`Crt.main` uses only in `gPow`) `:= pre + 16 w`, past `n`'s values. -/
def setCursor : List Instr := [ldh .x17 sOut, ldh .x4 sW, .lsl .x .x4 .x4 4, .add .x .x17 .x17 .x4, sth .x17 sD]

/-- The prime whose workspace's base is in `n`'s slot `sl`: `R_X² mod X`
(`r2X`), its `w_X` words and-ed with the mask (`n`'s `sMask`) to `pre` at
the cursor, which is advanced past them. -/
def phase (mul : Nat → Nat → Nat → Prog isa) (sl : Nat) : List (Prog isa) :=
  [.block [ldh .x0 sl]] ++ r2X mul ++
  [.block [ldh .x5 sLink, ldw .x17 .x5 sD, ldw .x15 .x5 sMask, ldh .x12 sW, ldh .x16 (sArr aY)], maskCopy,
    .block [ldh .x5 sLink, stw .x17 .x5 sD, leave]]

/-- `R_p² mod p` to `pre + 16 w`, then `R_q² mod q` after it. -/
def primes (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [.block setCursor] ++ phase mul sWsP ++ phase mul sWsQ

/-- `n` and `R² mod n` and-ed with the mask to `pre`, and `mask & 1` into
`x0`. -/
def outN : List (Prog isa) := [
  .block [ldh .x15 sMask, ldh .x12 sW, ldh .x16 (sArr aN), ldh .x17 sOut],
  maskCopy,
  .block [ldh .x16 (sArr aR2)],
  maskCopy,
  .block [ldh .x0 sMask, movi .x3 1, .logic .and .x .x0 .x0 .x3]]

/-- The computation, once `n` is known valid. -/
def main (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  seqs (nSetup mul ++ primesSetup ++ checks ++ primes mul ++ outN)

/-- The entry, `pre := 0` and the modulus' check (into `x9`), from `n`'s
base. -/
def head : Prog isa := .seq (.block entry) (.seq zeroPre (.block ([mov .x0 .x8] ++ invalid)))

/-- `vg_rsa_private_precompute`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq head (.ite (.zero .x .x9) (.block [movi .x0 0]) (main mul))

end VG.Impl.Rsa.AArch64.PrivPre
