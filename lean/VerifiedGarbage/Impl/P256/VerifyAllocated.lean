module

public import VerifiedGarbage.Impl.P256.VerifySparse
public import VerifiedGarbage.Impl.P256.VerifyRegisters
public import VerifiedGarbage.Impl.P256.VerifyAllocatedCode

/-! Scalar-register field programs for public P-256 verification. -/

@[expose] public section

namespace VG.Impl.P256.VerifyAllocated
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VerifyArithmetic

def raw (k : Kind) : List Instr := (operations k).flatMap VerifySparse.op

/-- Doubling exposes only the new accumulator. The addition headers expose
their final scratch values too, since their tails consume them. -/
def keep (k : Kind) (off : Nat) : Bool :=
  if k == .doubleRR then VerifyDouble.R.x ≤ off && off < VerifyDouble.R.z+32 else true

def code : Kind → List Instr
  | .doubleRR => VerifyAllocatedCode.doubleRR
  | .mixedHead => VerifyAllocatedCode.mixedHead
  | .mixedTail => VerifyAllocatedCode.mixedTail
  | .jacTail => VerifyAllocatedCode.jacTail
  | .cachedHead => VerifyAllocatedCode.cachedHead
  | k => raw k

def program (k : Kind) : Prog isa := .block (code k)

end VG.Impl.P256.VerifyAllocated
