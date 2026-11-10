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
* In each prime's workspace, `R_X² mod X` is the number 1 doubled
  `128 w_X` times modulo `X` (`r2X`, `Y + Y mod X` by `addMod`), written to `pre` and-ed
  with the mask (`phase`).
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

/-- In a prime's workspace: `[aY] := R_X² mod X`, the number 1 doubled
`128 w_X` times modulo `X` (`addMod`, which, unlike `double`, is constant
time for any modulus), counted in `sBit`. -/
def r2X : List (Prog isa) :=
  copyArr aY aOne ++ [
  .block [ldh .x3 sW, .lsl .x .x3 .x3 7, sth .x3 sBit],
  .loop (.seq (addMod aY aY aY) (.block [ldh .x3 sBit, .subImm .x .x3 .x3 1, sth .x3 sBit]))
    (.nonzero .x .x3)]

/-- In `n`'s workspace: the cursor into `pre` (`n`'s slot `sD`, which
`Crt.main` uses only in `gPow`) `:= pre + 16 w`, past `n`'s values. -/
def setCursor : List Instr := [ldh .x17 sOut, ldh .x4 sW, .lsl .x .x4 .x4 4, .add .x .x17 .x17 .x4, sth .x17 sD]

/-- The prime whose workspace's base is in `n`'s slot `sl`: `R_X² mod X`
(`r2X`), its `w_X` words and-ed with the mask (`n`'s `sMask`) to `pre` at
the cursor, which is advanced past them. -/
def phase (sl : Nat) : List (Prog isa) :=
  [.block [ldh .x0 sl]] ++ r2X ++
  [.block [ldh .x5 sLink, ldw .x17 .x5 sD, ldw .x15 .x5 sMask, ldh .x12 sW, ldh .x16 (sArr aY)], maskCopy,
    .block [ldh .x5 sLink, stw .x17 .x5 sD, leave]]

/-- `R_p² mod p` to `pre + 16 w`, then `R_q² mod q` after it. -/
def primes : List (Prog isa) := [.block setCursor] ++ phase sWsP ++ phase sWsQ

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
  seqs (nSetup mul ++ primesSetup ++ checks ++ primes ++ outN)

/-- The entry, `pre := 0` and the modulus' check (into `x9`), from `n`'s
base. -/
def head : Prog isa := .seq (.block entry) (.seq zeroPre (.block ([mov .x0 .x8] ++ invalid)))

/-- `vg_rsa_private_precompute`. -/
def code (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq head (.ite (.zero .x .x9) (.block [movi .x0 0]) (main mul))

end VG.Impl.Rsa.AArch64.PrivPre
