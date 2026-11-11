module

public import VerifiedGarbage.Impl.Rsa.X86_64.CheckCrtKey
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys

/-!
# RSA private-key validation with bounded CRT remainders

Use factor-width, bounded-quotient reductions for all five remainders.
For `e d mod (X - 1)`, `d < n = X Y` bounds the quotient by `2 e Y`,
so only the other factor's word length plus one word needs division.
Failed prerequisite checks clear the mask without changing the arithmetic
or its timing.

For the common shape of key, chosen by public values alone (`guard`: `w`
even, `n_len = 8 w = 2 p_len`, `p_len = q_len` and `n`'s top bit set), the
three long remainders are word-level divisions instead (`vg_rsa_crt_values`'s
`WordDivide`, normalized by setting the divisor's top bit, which a valid
factor of such an `n` already has): `d mod (X - 1)` compared with `dX`
(`wordMod`; with `dX < X - 1` and `e dX ≡ 1`, the same as `e d ≡ 1`), and
`q qInv mod p` compared with 1 (`wordQInv`).
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

/-- `sMask` all ones, and the stride `8 (w + 2)` into the header, for the
word-level divisions. -/
def strideInit : List Instr :=
  [.mov .rax (.mem (hdr sW)), .alu .add .rax (.imm 2), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
    .alu .add .rax (.reg .rax), .store (hdr Keys.sStride) .rax]

def maskSet : List Instr := [.mov32 .rax (.imm 0), .alu .sub .rax (.imm 1), .store (hdr sMask) .rax]

def maskInit : List Instr := strideInit ++ maskSet

/-- The checks with bit-serial remainders, for any shape of key. -/
def bitChecks : List (Prog isa) :=
  -- modulo `p - 1` and `q - 1`
  modChecks sP sPlen sDP sQlen ++ modChecks sQ sQlen sDQ sPlen ++
  -- `qInv < p` and `q qInv ≡ 1 (mod p)`
  loadNum aM sP sPlen ++ loadNum aX sQI sPlen ++ ltMask aX aM ++
  loadNum aR sQ sQlen ++ mulXR ++ CheckCrtKey.reduceTop sPlen CheckCrtKey.topQ ++ eqOne

/-- `sMask &= ` the mask of `d mod [aM] = [aX]`: `d` into `WordDivide`'s
dividend, `[aM]` into its divisor, the remainder compared with `[aX]`. -/
def wordRem : List (Prog isa) :=
  [Keys.copyA WordDivide.aM aM] ++ Keys.loadA WordDivide.aD sD sDlen ++
  [.seq (.block WordDivide.normalize) WordDivide.code] ++ Keys.eqA WordDivide.aR aX ++
  [.block Keys.CrtValues.andZero]

/-- `modChecks` with `d mod (X - 1) = dX` in place of `d e ≡ 1`. -/
def wordMod (sX sXlen sDX : Nat) : List (Prog isa) :=
  loadNum aM sX sXlen ++ decM ++
  loadNum aX sDX sXlen ++ ltMask aX aM ++
  wordRem ++
  mulE ++ CheckCrtKey.reduceTop sXlen CheckCrtKey.topE ++ eqOne

/-- `qInv < p` and `q qInv mod p = 1`, the product's low `w` words divided by
`WordDivide`. -/
def wordQInv : List (Prog isa) :=
  loadNum aM sP sPlen ++ loadNum aX sQI sPlen ++ ltMask aX aM ++
  loadNum aR sQ sQlen ++ mulXR ++
  [Keys.copyA WordDivide.aD aAcc] ++ [Keys.copyA WordDivide.aM aM] ++
    [.seq (.block WordDivide.normalize) WordDivide.code] ++ Keys.eqA WordDivide.aR aOne ++
  [.block Keys.CrtValues.andZero]

/-- The checks with word-level remainders, under `guard`. -/
def wordChecks : List (Prog isa) :=
  wordMod sP sPlen sDP ++ wordMod sQ sQlen sDQ ++ wordQInv

/-- `ZF` set iff `w` is even, `n_len = 8 w = 2 p_len`, `p_len = q_len` and
`n`'s top bit is set (`vg_rsa_crt_values`'s guard, from this header's
slots): all public. -/
def guardHead : List Instr := [.mov .r12 (.mem (hdr sW)), .mov .rdx (.mem (hdr sN))]

def guardTail : List Instr :=
  [.mov .rax (.reg .r12), .alu .and .rax (.imm 1),
    .mov .rcx (.reg .r12), .shift .shl .rcx 3, .alu .xor .rcx (.mem (hdr sK)), .alu .or .rax (.reg .rcx),
    .mov .rcx (.mem (hdr sPlen)), .shift .shl .rcx 1, .alu .xor .rcx (.mem (hdr sK)), .alu .or .rax (.reg .rcx),
    .mov .rcx (.mem (hdr sPlen)), .alu .xor .rcx (.mem (hdr sQlen)), .alu .or .rax (.reg .rcx),
    .movzx8 .rcx { base := .rdx }, .shift .shr .rcx 7, .alu .xor .rcx (.imm 1), .alu .or .rax (.reg .rcx)]

def guard : List Instr := guardHead ++ guardTail

/-- The computation, once `n` and `e` are known valid. -/
def main : Prog isa := seqs (
  [.block head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx, .block maskInit] ++
  -- `d < n`
  loadNum aX sD sDlen ++ ltMask aX aN ++
  -- `p q = n`
  loadNum aX sP sPlen ++ loadNum aR sQ sQlen ++ mulXR ++ Crt.eqCheck ++
  [.seq (.block guard) (.ite .e (seqs wordChecks) (seqs bitChecks)),
    .block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)])

/-- `vg_rsa_check_key`. -/
def code : Prog isa := seqs [
  .block entry,
  Checked.expCheck,
  .ite .ne (.block fail)
    (seqs [.block (([.store (hdr sEv) .r11, .mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] : List Instr) ++ invalid),
      .ite .ne (.block fail) main])]

end VG.Impl.Rsa.X86_64.CheckKey
