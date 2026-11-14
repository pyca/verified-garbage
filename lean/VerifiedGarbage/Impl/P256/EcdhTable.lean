module

public import VerifiedGarbage.Impl.P256.EcdhJac.Base
public import VerifiedGarbage.Impl.P256.EcdhAllocatedCode
public import VerifiedGarbage.Impl.P256.VerifySparse

/-! Register allocation for the two co-Z table-construction kernels. -/

@[expose] public section

namespace VG.Impl.P256.EcdhTable
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64

def operations (doubling : Bool) :=
  if doubling then EcdhJac.dbluOps else EcdhJac.zadduOps

def raw (doubling : Bool) : List Instr := (operations doubling).flatMap VerifySparse.op

def code (doubling : Bool) : List Instr :=
  if doubling then EcdhAllocatedCode.dblu else EcdhAllocatedCode.zaddu

def program (doubling : Bool) : Prog isa := .block (code doubling)
end VG.Impl.P256.EcdhTable
