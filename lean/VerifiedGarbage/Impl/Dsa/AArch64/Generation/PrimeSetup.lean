module

public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate

/-! Montgomery setup for the shared round, including the padded 160-bit q. -/
@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate

def primeHead : List Instr :=
  [ldh .x8 (sArr aN), ld .x3 .x8] ++ minv ++
    [sth .x15 sMinv, ldh .x12 sW, movi .x9 1, movi .x13 0]

def primeR2 (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block primeHead) (Arithmetic.constants mul)

def primeConstants (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul aY aR2 aOne, copyA aR1 aY] ++ subA aRm1 aN aR1

def primeSetup (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (primeR2 mul) (seqs (primeConstants mul ++ expSetup))

end VG.Impl.Dsa.AArch64.Generation
