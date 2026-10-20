module

public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate

/-! Native p-candidate reduction and generator-exponent arithmetic. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def doubleArray (dst : Nat) : Prog isa :=
  .seq (.block (ws ++ [movi .x7 0, mov .x14 .x12, .adds .x .x3 .x7 .x7] ++ base dst .x16))
    (countLoop .x14 shlBody)

def incrementEven (dst : Nat) : List Instr :=
  ws ++ base dst .x16 ++ [ld .x3 .x16, .addImm .x .x3 .x3 1, st .x3 .x16]

def reduceRemainder (dst src rem : Nat) : Prog isa :=
  .seq (seqs (subA dst src rem)) (.block (incrementEven dst))

/-- X is in array 0 and 2q in array 2. Array 5 receives p, array 0 the quotient. -/
def reduceCandidate : Prog isa :=
  .seq (copyA 4 0) (.seq (divmod 0 1 2 3) (reduceRemainder 5 4 1))

end VG.Impl.Dsa.AArch64.Generation
