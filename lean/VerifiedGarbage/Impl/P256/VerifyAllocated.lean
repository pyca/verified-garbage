module

public import VerifiedGarbage.Impl.P256.VerifySparse
public import VerifiedGarbage.Impl.P256.VerifyAllocatedCode
public import VerifiedGarbage.Impl.P256.VerifyArithmetic

/-! Scalar-register field programs for public P-256 verification. -/

@[expose] public section

namespace VG.Impl.P256.VerifyAllocated
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VerifyArithmetic

def raw (k : Kind) : List Instr := (operations k).flatMap VerifySparse.op

def code : Kind → List Instr
  | .mixedHead => VerifyAllocatedCode.mixedHead
  | .mixedTail => VerifyAllocatedCode.mixedTail
  | .jacTail => VerifyAllocatedCode.jacTail
  | .cachedHead => VerifyAllocatedCode.cachedHead
  | k => raw k

def program (k : Kind) : Prog isa := .block (code k)

end VG.Impl.P256.VerifyAllocated
