module

public import VerifiedGarbage.Impl.Rsa.AArch64.CheckCrtKey

/-! # Full RSA key checks with bounded reductions on AArch64 -/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.CheckKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys

/-- The other factor's word length plus one bounds the quotient of `e d`. -/
def topD (sl : Nat) : List Instr :=
  [ldh .x13 sl, .addImm .x .x13 .x13 7, .lsr .x .x13 .x13 3, .addImm .x .x13 .x13 1]

/-- `x12 := w_m = (W - 2) / 4`, the words of `p` and `q` under `wordGuard`. -/
def wM : List Instr := [.subImm .x .x12 .x12 2, .lsr .x .x12 .x12 2]

/-- `x16 :=` the address of `[aA]`'s word `-1` from `[aRem]`'s base (`x11`)
and `w_m` (`x12`): `[aA]` is the array below, `8 (W + 2) = 32 w_m + 32`
bytes down. -/
def aBase : List Instr := [.lsl .x .x16 .x12 5, .addImm .x .x16 .x16 40, .sub .x .x16 .x11 .x16]

/-- `sMask &=` the mask of `[aA] mod [aM] = 1`, `[aA]` of `L` words
(`lenL` into `x13` from `W` in `x12`): by `wdiv` if `wordGuard` passes, by
`modOne` (`top`) otherwise. -/
def wmodOne (top lenL : List Instr) : List (Prog isa) :=
  [.seq (.block (wordGuard sPlen sQlen)) (.ite (.zero .x .x9) (wdiv aA aM aRem aT wM lenL aBase)
    (seqs (CheckCrtKey.reduceTop top)))] ++ eqA aRem aOne ++ [.block andZero]

/-- `L = W / 2` words of `e d`. -/
def lenD : List Instr := [.lsr .x .x13 .x12 1]

/-- `L = w_m + 1` words of `e dX`. -/
def lenE : List Instr := [.subImm .x .x13 .x12 2, .lsr .x .x13 .x13 2, .addImm .x .x13 .x13 1]

/-- `L = 2 w_m` words of `q qInv`. -/
def lenQ : List Instr := [.subImm .x .x13 .x12 2, .lsr .x .x13 .x13 1]

/-- The checks modulo `X - 1` for the prime `X` (pointer and length in
slots `sX` and `sXlen`) and its exponent `dX` (pointer in `sDX`):
`dX < X - 1`, `d e ≡ 1` and `e dX ≡ 1`. -/
def modChecks (sX sXlen sDX sYlen : Nat) : List (Prog isa) :=
  loadA aM sX sXlen ++ [.block (decA aM)] ++
  loadA aX sDX sXlen ++ ltA aX aM ++
  loadA aX sD sDlen ++ mulE ++ wmodOne (topD sYlen) lenD ++
  loadA aX sDX sXlen ++ mulE ++ wmodOne CheckCrtKey.topE lenE

/-- The computation, once `n` and `e` are known valid. -/
def main : Prog isa := seqs (
  [.block head] ++ loadA 0 Public.sN Public.sK ++ loadA aE sE sElen ++ [zeroA aOne, .block (setOneA aOne)] ++
  -- `d < n`
  loadA aX sD sDlen ++ ltA aX 0 ++
  -- `p q = n`
  loadA aX sP sPlen ++ loadA aR sQ sQlen ++ mulPQ ++ eqA aA 0 ++ [.block andZero] ++
  -- modulo `p - 1` and `q - 1`
  modChecks sP sPlen sDP sQlen ++ modChecks sQ sQlen sDQ sPlen ++
  -- `qInv < p` and `q qInv ≡ 1 (mod p)`
  loadA aM sP sPlen ++ loadA aX sQI sPlen ++ ltA aX aM ++
  loadA aR sQ sQlen ++ mulXR ++ wmodOne CheckCrtKey.topQ lenQ ++
  [.block retMask])

/-- `vg_rsa_check_key`. -/
def code : Prog isa :=
  .seq (.block entry) (.seq Checked.expCheck (.ite (.zero .x .x9) (.block fail)
    (.seq (.block ([ldh .x2 Public.sN, ldh .x3 Public.sK] ++ invalid)) (.ite (.zero .x .x9) (.block fail) main))))

end VG.Impl.Rsa.AArch64.CheckKey
