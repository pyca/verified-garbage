module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Impl.Rsa.X86.Inverse

/-! # Prime ordering and the totient product for native RSA key generation

These routines operate on arbitrary input integers, including zero.
Subtraction of one saturates at zero, as required by the shared contract.
Selections use masks; neither a swap nor a decrement reveals an operand.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Key
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.Keys

/-- Sort the factors into `p ≥ q`, preserving both inputs' values. -/
def order (n : Nat) : Prog isa := seqs [
  sub3 n aT1 aPa aQa,
  .block [.store (sc kFlag) .ebx],
  copy n aT2 aPa,
  sel n aPa aPa aQa kFlag,
  sel n aQa aQa aT2 kFlag]

/-- `[out] = max([a] - 1, 0)`, using the existing zero and one arrays. -/
def decTo (n out a : Nat) : Prog isa := seqs [
  eqS n kFlag a aZero aT1,
  sel n aT2 aOne aZero kFlag,
  sub3 n out a aT2]

/-- Sorted factors, predecessors, and their full unreduced product. -/
def primes (n : Nat) : Prog isa := seqs [
  order n, decTo n aPm aPa, decTo n aQm aQa, primeProduct n aPhi aPm aQm]

/-- Halve an array only while both running predecessors are even. -/
def halfIf (n j : Nat) : Prog isa := seqs [
  copy n aHalf j, .block [.mov .ebx (.imm 0)], half n aHalf,
  sel n j j aHalf kFlag]

/-- The bit of both running factors being even. -/
def bothEven (n : Nat) : List Instr :=
  [.mov .eax (.mem (sc (slot n aU))), .alu .or .eax (.mem (sc (slot n aV))),
    .alu .and .eax (.imm 1), .alu .xor .eax (.imm 1), .store (sc kFlag) .eax]

/-- Halve the running factors and product under their common-even bit. -/
def halveStep (n : Nat) : Prog isa := seqs [
  .block (bothEven n),
  halfIf n aU, halfIf n aV, halfIf n aPhi]

/-- One common-power-of-two step for the LCM calculation. -/
def twoStep (n : Nat) : Prog isa :=
  .seq (halveStep n) (.block [.alu .sub .esi (.imm 1), .alu .cmp .esi (.imm 0)])

/-- Remove one common power of two from the product per simultaneous
halving of the factors. The public schedule also handles zero factors. -/
def twos (n : Nat) : Prog isa := seqs [
  copy n aU aPm, copy n aV aQm,
  .block [.mov .esi (.imm (BitVec.ofNat 32 (32 * n)))], .loop (twoStep n) .ne]

end VG.Impl.RsaKeyGen.X86.Key
