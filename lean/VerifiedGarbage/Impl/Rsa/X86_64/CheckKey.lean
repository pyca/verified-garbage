module

public import VerifiedGarbage.Impl.Rsa.X86_64.CheckCrtKey

/-!
# RSA private-key validation with bounded CRT remainders

Use factor-width, bounded-quotient reductions for all five remainders.
For `e d mod (X - 1)`, `d < n = X Y` bounds the quotient by `2 e Y`,
so only the other factor's word length plus one word needs division.
Failed prerequisite checks clear the mask without changing the arithmetic
or its timing.
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64.CheckKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64

/-- The checks modulo `X - 1` for the prime `X` (pointer and length in
slots `sX` and `sXlen`) and its exponent `dX` (pointer in `sDX`):
`dX < X - 1`, `d e ≡ 1` and `e dX ≡ 1`. -/
def modChecks (sX sXlen sDX sYlen : Nat) : List (Prog isa) :=
  loadNum aM sX sXlen ++ decM ++
  loadNum aX sDX sXlen ++ ltMask aX aM ++
  loadNum aX sD sDlen ++ mulEWide ++ CheckCrtKey.reduceTop sXlen (topD sYlen) ++ eqOne ++
  loadNum aX sDX sXlen ++ mulE ++ CheckCrtKey.reduceTop sXlen CheckCrtKey.topE ++ eqOne

/-- The computation, once `n` and `e` are known valid. -/
def main : Prog isa := seqs (
  [.block head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx,
    .block [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]] ++
  -- `d < n`
  loadNum aX sD sDlen ++ ltMask aX aN ++
  -- `p q = n`
  loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ Crt.eqCheck ++
  -- modulo `p - 1` and `q - 1`
  modChecks sP sPlen sDP sQlen ++ modChecks sQ sQlen sDQ sPlen ++
  -- `qInv < p` and `q qInv ≡ 1 (mod p)`
  loadNum aM sP sPlen ++ loadNum aX sQI sPlen ++ ltMask aX aM ++
  loadNum aR sQ sQlen ++ mulXR ++ CheckCrtKey.reduceTop sPlen CheckCrtKey.topQ ++ eqOne ++
  [.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)])

/-- `vg_rsa_check_key`. -/
def code : Prog isa := seqs [
  .block entry,
  Checked.expCheck,
  .ite .ne (.block fail)
    (seqs [.block (([.store (hdr sEv) .r11, .mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid),
      .ite .ne (.block fail) main])]

end VG.Impl.Rsa.X86_64.CheckKey
