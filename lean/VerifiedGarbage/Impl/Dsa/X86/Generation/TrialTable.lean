module
public import VerifiedGarbage.Impl.RsaKeyGen.Primes
public import VerifiedGarbage.Impl.Mont.X86

/-! # Trial divisors paired with precomputed 32-bit reciprocals

The table occupies at most 8192 bytes and is reused for every candidate in
one parameter-generation call. Its divisors match the existing RSA/DSA
trial policy, including the duplicated 3 at entry 511.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.RsaKeyGen

def trialTableEntry (i : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 (tabEntry i))), .store (sc (8 * i)) .eax,
   .mov .eax (.imm (BitVec.ofNat 32 (2 ^ 32 / tabEntry i))), .store (sc (8 * i + 4)) .eax]

def trialTable : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (trialTable n) (.block (trialTableEntry n))
end VG.Impl.Dsa.X86.Generation
