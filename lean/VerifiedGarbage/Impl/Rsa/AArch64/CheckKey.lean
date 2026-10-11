module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys

/-!
# BoringSSL's `RSA_check_key` on AArch64

`vg_rsa_check_key(n, n_len, e, e_len, d, d_len, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`: the first eight
arguments in `x0`–`x7`, the others on the stack.

`e` is checked as `vg_rsa_public_checked` checks it, then `n` as
`vg_rsa_public_precompute` does: both are public, and the code returns 0 at
once if either is refused. The rest works in the layout of
`Impl/Rsa/AArch64/Keys.lean`, wide enough for the products: arrays of
`W + 2` words for `W = 2 w + 2`, `w = ⌈n_len / 8⌉`, every value loaded into
an array of `W` words. Its timing depends only on the lengths and on `n` and
`e`: each check gives a mask, and'ed into the header's `sMask`, which is
returned as 0 or 1 at the end.

* `d < n`, `dP < p - 1`, `dQ < q - 1` and `qInv < p`: the borrow of a
  subtraction (`ltA`).
* `p q = n`: the product (`mulXR`, rows of `w` words), compared with `n`
  (`eqA`).
* `d e ≡ 1 (mod p - 1)` and the others: the product `x` of `d`, `dP` or
  `dQ` and `e` (`mulE`, `e` below `2^33` a word), or of `q` and `qInv`
  (`mulXR`), is divided by `m` (`p - 1`, `q - 1` or `p`) by `divmod`, and the
  remainder compared with 1.

`p < n` and `q < n` need no computation: `p` and `q` are shorter than `n`,
which is at least `256^(n_len - 1)`.
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.CheckKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys

/-! ## Header slots and arrays

`Public.sN`, `Public.sK` and `Public.sMask` are `vg_rsa_public_precompute`'s,
`sStride` the layout's. -/

def sD : Nat := sFn 0
def sE : Nat := sFn 3
def sElen : Nat := sFn 4
def sDlen : Nat := sFn 5
def sP : Nat := sFn 7
def sPlen : Nat := sFn 8
def sQ : Nat := sFn 9
def sQlen : Nat := sFn 10
def sDP : Nat := sFn 11
def sDQ : Nat := sFn 13
def sQI : Nat := sFn 14

/-- The arrays: `n` (0), the operand `x` (1), the second factor (2), the
modulus `m` (3), the product, which `divmod` divides (4), the remainder (5),
`divmod`'s temporary (6), the number 1 (7) and `e` (8). -/
def aX : Nat := 1
def aR : Nat := 2
def aM : Nat := 3
def aA : Nat := 4
def aRem : Nat := 5
def aT : Nat := 6
def aOne : Nat := 7
def aE : Nat := 8

/-! ## Entry and exit -/

/-- The arguments in the header at `scratch` (the ninth stack argument),
whose base goes in `x0`; then `e` and `e_len` into `x4` and `x5` for
`expCheck`. -/
def entry : List Instr :=
  [.ldrSp .x8 64, .str .x .x0 .x8 (8 * Public.sN), .str .x .x1 .x8 (8 * Public.sK), .str .x .x2 .x8 (8 * sE),
    .str .x .x3 .x8 (8 * sElen), .str .x .x4 .x8 (8 * sD), .str .x .x5 .x8 (8 * sDlen), .str .x .x6 .x8 (8 * sP),
    .str .x .x7 .x8 (8 * sPlen),
    .ldrSp .x9 0, .str .x .x9 .x8 (8 * sQ), .ldrSp .x9 8, .str .x .x9 .x8 (8 * sQlen),
    .ldrSp .x9 16, .str .x .x9 .x8 (8 * sDP), .ldrSp .x9 32, .str .x .x9 .x8 (8 * sDQ),
    .ldrSp .x9 48, .str .x .x9 .x8 (8 * sQI), mov .x0 .x8, mov .x4 .x2, mov .x5 .x3]

/-- 0 returned. -/
def fail : List Instr := [movi .x0 0]

/-! ## The pieces -/

/-- `w := ⌈k / 8⌉`, the layout's width `W = 2 w + 2` into `sW`, the arrays'
bases and the stride `8 (W + 2)`, and the mask all ones. -/
def head : List Instr :=
  [ldh .x3 Public.sK, .addImm .x .x12 .x3 7, .lsr .x .x12 .x12 3, .add .x .x12 .x12 .x12, .addImm .x .x12 .x12 2,
    sth .x12 sW] ++ setBases ++
  ([.addImm .x .x3 .x12 2, .lsl .x .x3 .x3 3, sth .x3 sStride, movi .x7 0, .subImm .x .x4 .x7 1,
    sth .x4 Public.sMask] : List Instr)

/-- `x12 := w` from `W = 2 w + 2` in `x12`. -/
def narrow : List Instr := [.subImm .x .x12 .x12 2, .lsr .x .x12 .x12 1]

/-- `sMask &= ` the mask of `[a] < [b]` over `W` words: the borrow of
`[a] - [b]`. -/
def ltA (a b : Nat) : List (Prog isa) := [
  .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7]),
  .block (base a .x16 ++ base b .x17),
  cmpLoop,
  .block (borrowMask ++ [ldh .x3 Public.sMask, .logic .and .x .x15 .x15 .x3, sth .x15 Public.sMask])]

/-- `[aA] := [aX] e` over `w` words (`e` the low word of `[aE]`). -/
def mulE : List (Prog isa) := [
  zeroA aA,
  .block (ws ++ base aE .x1 ++ base aX .x9 ++ base aA .x8 ++ [ld .x1 .x1] ++ narrow ++ [movi .x7 0]),
  mulAddRow]

/-- `[aA] := [aX] [aR]`, `w` rows of `w` words. -/
def mulXR : List (Prog isa) := [
  zeroA aA,
  .block (ws ++ base aX .x5 ++ base aR .x9 ++ base aA .x8 ++ [mov .x11 .x5] ++ narrow ++
    [mov .x13 .x12, movi .x7 0]),
  Crt.mulRows]

/-- `sMask &= ` the mask of `[aA] mod [aM] = 1`. -/
def modOne : List (Prog isa) := [divmod aA aRem aM aT] ++ eqA aRem aOne ++ [.block andZero]

/-- The checks modulo `X - 1` for the prime `X` (pointer and length in
slots `sX` and `sXlen`) and its exponent `dX` (pointer in `sDX`):
`dX < X - 1`, `d e ≡ 1` and `e dX ≡ 1`. -/
def modChecks (sX sXlen sDX : Nat) : List (Prog isa) :=
  loadA aM sX sXlen ++ [.block (decA aM)] ++
  loadA aX sDX sXlen ++ ltA aX aM ++
  loadA aX sD sDlen ++ mulE ++ modOne ++
  loadA aX sDX sXlen ++ mulE ++ modOne

/-- The computation, once `n` and `e` are known valid. -/
def main : Prog isa := seqs (
  [.block head] ++ loadA 0 Public.sN Public.sK ++ loadA aE sE sElen ++ [zeroA aOne, .block (setOneA aOne)] ++
  -- `d < n`
  loadA aX sD sDlen ++ ltA aX 0 ++
  -- `p q = n`
  loadA aX sP sPlen ++ loadA aR sQ sQlen ++ mulXR ++ eqA aA 0 ++ [.block andZero] ++
  -- modulo `p - 1` and `q - 1`
  modChecks sP sPlen sDP ++ modChecks sQ sQlen sDQ ++
  -- `qInv < p` and `q qInv ≡ 1 (mod p)`
  loadA aM sP sPlen ++ loadA aX sQI sPlen ++ ltA aX aM ++
  loadA aR sQ sQlen ++ mulXR ++ modOne ++
  [.block retMask])

/-- `vg_rsa_check_key`. -/
def code : Prog isa :=
  .seq (.block entry) (.seq Checked.expCheck (.ite (.zero .x .x9) (.block fail)
    (.seq (.block ([ldh .x2 Public.sN, ldh .x3 Public.sK] ++ invalid)) (.ite (.zero .x .x9) (.block fail) main))))

end VG.Impl.Rsa.AArch64.CheckKey
