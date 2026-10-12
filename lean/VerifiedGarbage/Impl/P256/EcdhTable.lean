module

public import VerifiedGarbage.Impl.P256.EcdhJac.Base
public import VerifiedGarbage.Impl.P256.EcdhAllocatedCode

/-! Register allocation for the two co-Z table-construction kernels. -/

@[expose] public section

namespace VG.Impl.P256.EcdhTable
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64

def operations (doubling : Bool) :=
  if doubling then EcdhJac.dbluOps else EcdhJac.zadduOps

def raw (doubling : Bool) : List Instr := (operations doubling).flatMap VerifySparse.op

/-- Retain the point, its cached powers of Z, and the values needed by the next table step. -/
def keep (doubling : Bool) (off : Nat) : Bool :=
  (704≤off && off<800) || (5400≤off && off<5464) ||
    (if doubling then 864≤off && off<928 else 608≤off && off<672)

def code (doubling : Bool) : List Instr :=
  if doubling then EcdhAllocatedCode.dblu else EcdhAllocatedCode.zaddu

def program (doubling : Bool) : Prog isa := .block (code doubling)
end VG.Impl.P256.EcdhTable
