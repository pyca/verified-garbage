module

public import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt

/-! # Prime recovery's batched GCD at a width read at run time (i686)

`gcd(m, x)` by batches of 30 divsteps, for the modulus `m` and `x` in prime recovery's narrow
arrays 8 and 0 (`n = w` words, from `L.len`), with `InvBatchRt`'s operations on the wide
arrays (`L = RecoverRt.wid`): wide array `j` is narrow array `2 j`, and its first `n + 1`
words, `n = W / 2 = w + 1` (`InvBatchRt`'s count), are narrow array `2 j`'s `w` words and its
two words of padding. The signed values `f` and `g` are in arrays 4 and 5, their next values
in 0 and 5, the products in 11 and the corrections in 12; the window, the slots and the
batch count are `InvBatchRt`'s. As `n` is odd, the shift right by 30 takes a word on its own
after its pairs (`shr30o`). `|f|` goes to narrow array 1 (`res`), and array 5, which holds
the narrow array 10 (prime recovery's zero), is zeroed again.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.GcdBatchRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Inv
open VG.Impl.Rsa.X86.KeyRt (Lay restoreEdi)
open VG.Impl.Rsa.X86.InvBatchRt
open VG.Impl.Rsa.X86.Keys (seqs)

variable (L : Lay)

/-- `InvBatchRt.shr30` for an odd `n`: `[dst] = [src] >> 30`, signed, `n + 1` words, the first
`n - 1` two at a time, then one, then the top word from the sign. -/
def shr30o (dst src : Ref) : Prog isa :=
  .seq (.block (ptr L .ebp src .edx ++ nBytesLess .esi ++ ptr L .edi dst .edx)) <|
  .seq (.loop (.block (shrWord 0 ++ shrWord 4 ++ [.alu .add .ebp (.imm 8), .alu .add .edi (.imm 8),
      .alu .sub .esi (.imm 8)])) .ne)
  (.block (shrWord 0 ++ [.alu .add .ebp (.imm 4), .alu .add .edi (.imm 4)] ++
    [.mov .eax (.mem (at_ .ebp 0)), .shift .shr .eax 31, .mov .ecx (.imm 0), .alu .sub .ecx (.reg .eax),
      .mov .eax (.mem (at_ .ebp 0)), .mov .ebx (.reg .ecx), .shift .shr .eax 30, .alu .add .ebx (.reg .ebx),
      .alu .add .ebx (.reg .ebx), .alu .add .eax (.reg .ebx), .store (at_ .edi 0) .eax] ++ restoreEdi L))

/-- Narrow array 1, past wide array 0's first `n + 1` words. -/
def res : Ref := { arr := 0, half := 1, byte := 4 }

/-- `f = m` and `g = x + (m if x is even)`, `n + 1` words each, `δ = 1`, and the batches'
count. -/
def init : Prog isa := seqs [
  .block (slots L),
  zeros L (a 12) (nBytes .ecx 1), copy L (a 12) (a 4) (nBytesLess .edi), copy L (a 4) (a 12) (nBytes .edi 1),
  zeros L (a 5) (nBytes .ecx 1), copy L (a 5) (a 0) (nBytesLess .edi),
  zeros L (a 12) (nBytes .ecx 1),
  .block (VG.Impl.Rsa.X86.GcdBatch.evenMask (offset 0 0)), selIn L (a 12) (a 4) (nBytes .edi 0),
  chain L .adc (a 5) (a 5) (a 12) (nBytes .edx 1),
  .block [.mov .eax (.imm 1), .store (sc win) .eax],
  .block batches]

/-- The matrix applied to `f` and `g`. -/
def update : Prog isa := seqs [
  linear L (win + 12) (win + 16) (a 11) (a 4) (a 5) (a 12) 1, shr30o L (a 0) (a 11),
  linear L (win + 20) (win + 24) (a 11) (a 4) (a 5) (a 12) 1, shr30o L (a 5) (a 11),
  copy L (a 4) (a 0) (nBytes .edi 1)]

/-- `|f|` into `res`, and array 5 zeroed. -/
def finish : Prog isa := seqs [
  zeros L (a 12) (nBytes .ecx 0), chain L .sbb (a 12) (a 12) (a 4) (nBytes .edx 0),
  .block (maskAt L { arr := 4, half := 1 } ++ [.alu .xor .ecx (.imm (-1))]),
  selIn L (a 12) (a 4) (nBytes .edi 0),
  copy L res (a 12) (nBytes .edi 0),
  zeros L (a 5) (nBytes .ecx 0)]

def body : Prog isa := seqs [
  init L,
  .loop (seqs [.block (start L), wordSteps win 30, update L,
    .block [.mov .esi (.mem (sc 100)), decCounter, .store (sc 100) .esi, testCounter]]) .ne,
  finish L]

end VG.Impl.Rsa.X86.GcdBatchRt
