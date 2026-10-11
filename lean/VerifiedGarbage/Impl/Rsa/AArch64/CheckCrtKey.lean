module

public import VerifiedGarbage.Impl.Rsa.AArch64.CheckKey

/-!
# `RSA_check_key`'s checks of the CRT form on AArch64

`vg_rsa_check_crt_key(n, n_len, e, e_len, p, p_len, q, q_len, dp, dp_len,
dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the first eight
arguments in `x0`–`x7`, the others on the stack.

`vg_rsa_check_key`'s code (`Impl/Rsa/AArch64/CheckKey.lean`) without the
checks of `d`, in its layout: the entry stores the arguments in its header
slots, with `p` also in `d`'s, which nothing reads. `e` and `n` are checked
first, and are the only branches; every other check is and'ed into the mask.

The remainders are shorter than `vg_rsa_check_key`'s `divmod`, which runs
`64 W` steps of restoring division over the layout's width `W`. Each
remainder here needs a small quotient when the comparison before it holds:
`e dX < 2^64 (X - 1)` when `dX < X - 1`, and `q qInv < 2^(64 c) p` when
`qInv < p`, for `c = ⌈q_len / 8⌉`. So `reduceTop` starts the remainder at
the product's words from `c` up (`c = 1` for the first), which are below the
divisor, puts its low `c` words at the top of the quotient's register, and
runs only `64 c` of `divmod`'s steps. When the comparison fails, the mask is
already clear and the remainder is not used.
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.CheckCrtKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Rsa.AArch64.CheckKey (sD sE sElen sDlen sP sPlen sQ sQlen sDP sDQ sQI aX aR aM aA aRem aT aOne aE
  ltA mulE mulXR)

/-- The quotient's register of `reduceTop`. -/
def aQ : Nat := 9

/-! ## Entry -/

/-- The arguments in `vg_rsa_check_key`'s header slots at `scratch` (the
seventh stack argument), `p` also in `d`'s, whose base goes in `x0`; then
`e` and `e_len` into `x4` and `x5` for `expCheck`. -/
def entry : List Instr :=
  [.ldrSp .x8 48, .str .x .x0 .x8 (8 * Public.sN), .str .x .x1 .x8 (8 * Public.sK), .str .x .x2 .x8 (8 * sE),
    .str .x .x3 .x8 (8 * sElen), .str .x .x4 .x8 (8 * sD), .str .x .x5 .x8 (8 * sDlen), .str .x .x4 .x8 (8 * sP),
    .str .x .x5 .x8 (8 * sPlen), .str .x .x6 .x8 (8 * sQ), .str .x .x7 .x8 (8 * sQlen),
    .ldrSp .x9 0, .str .x .x9 .x8 (8 * sDP), .ldrSp .x9 16, .str .x .x9 .x8 (8 * sDQ),
    .ldrSp .x9 32, .str .x .x9 .x8 (8 * sQI), mov .x0 .x8, mov .x4 .x2, mov .x5 .x3]

/-! ## The shortened remainder -/

/-- `x13 := 1`: the words above which `e dX` is below `2^64 (X - 1)`. -/
def topE : List Instr := [movi .x13 1]

/-- `x13 := ⌈q_len / 8⌉`: those above which `q qInv` is below
`2^(64 c) p`. -/
def topQ : List Instr := [ldh .x13 sQlen, .addImm .x .x13 .x13 7, .lsr .x .x13 .x13 3]

/-- After `base aA .x16` and `base aRem .x17`: `[aA]`'s words from `c` (`x13`)
up, `w - c` of them. -/
def hiTail : List Instr := [.lsl .x .x3 .x13 3, .add .x .x16 .x16 .x3, .sub .x .x12 .x12 .x13]

/-- After `base aA .x16` and `base aQ .x17`: `[aQ]`'s top `c` words, `c` of
them. -/
def loTail : List Instr := [.sub .x .x3 .x12 .x13, .lsl .x .x3 .x3 3, .add .x .x17 .x17 .x3, mov .x12 .x13]

/-- `x6 := 64 c`, the steps. -/
def cntTail : List Instr := [.lsl .x .x6 .x13 6]

/-- `[aRem] := [aA] mod [aM]` when the words of `[aA]` from `c` up (`c` in
`x13` by `top`) are below `[aM]`: `[aRem]` starts as those words, the
top `c` words of `[aQ]` as the low ones, then `64 c` steps of `divmod`. -/
def reduceTop (top : List Instr) : List (Prog isa) := [
  zeroA aRem,
  zeroA aQ,
  .seq (.block (ws ++ top ++ base aA .x16 ++ base aRem .x17 ++
    hiTail)) copyWords,
  .seq (.block (ws ++ top ++ base aA .x16 ++ base aQ .x17 ++
    loTail)) copyWords,
  .seq (.block (ws ++ top ++ cntTail)) (.loop (divStep aQ aRem aM aT) (.nonzero .x .x6))]

/-- `sMask &= ` the mask of `[aA] mod [aM] = 1`, by `reduceTop top`. -/
def modOne (top : List Instr) : List (Prog isa) := reduceTop top ++ eqA aRem aOne ++ [.block andZero]

/-- The checks modulo `X - 1` for the prime `X` (pointer and length in
slots `sX` and `sXlen`) and its exponent `dX` (pointer in `sDX`):
`dX < X - 1` and `e dX ≡ 1`. -/
def modChecks (sX sXlen sDX : Nat) : List (Prog isa) :=
  loadA aM sX sXlen ++ [.block (decA aM)] ++
  loadA aX sDX sXlen ++ ltA aX aM ++ mulE ++ modOne topE

/-- The computation, once `n` and `e` are known valid. -/
def main : Prog isa := seqs (
  [.block CheckKey.head] ++ loadA 0 Public.sN Public.sK ++ loadA aE sE sElen ++ [zeroA aOne, .block (setOneA aOne)] ++
  -- `p q = n`
  loadA aX sP sPlen ++ loadA aR sQ sQlen ++ mulXR ++ eqA aA 0 ++ [.block andZero] ++
  -- modulo `p - 1` and `q - 1`
  modChecks sP sPlen sDP ++ modChecks sQ sQlen sDQ ++
  -- `qInv < p` and `q qInv ≡ 1 (mod p)`
  loadA aM sP sPlen ++ loadA aX sQI sPlen ++ ltA aX aM ++
  loadA aR sQ sQlen ++ mulXR ++ modOne topQ ++
  [.block retMask])

/-- `vg_rsa_check_crt_key`. -/
def code : Prog isa :=
  .seq (.block entry) (.seq Checked.expCheck (.ite (.zero .x .x9) (.block CheckKey.fail)
    (.seq (.block ([ldh .x2 Public.sN, ldh .x3 Public.sK] ++ invalid)) (.ite (.zero .x .x9) (.block CheckKey.fail) main))))

end VG.Impl.Rsa.AArch64.CheckCrtKey
