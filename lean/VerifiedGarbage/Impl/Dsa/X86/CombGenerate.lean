module

public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Impl.Dsa.X86.CombCore

/-! Key generation retains the public subgroup computation's table for g^x. -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout

def subgroup (pLen qLen : Nat) : Prog isa :=
  Generate.subgroupWith pLen (power true pLen qLen .p (.input .g) (.input .q) t)

def parameters (pLen qLen : Nat) : Prog isa :=
  .seq (Generate.domain pLen qLen) (subgroup pLen qLen)

def checkSized : Nat → Nat → Prog isa := Generate.checkSizedWith parameters

def checkParameters : Prog isa := Generate.checkParametersWith checkSized

/-- Internal only: the caller has already validated the parameters and retained
this generator's canonical table. Component range checks are still required. -/
def deriveCompute (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.range qLen .q (.input .nonce),
  power false pLen qLen .p (.input .g) (.input .nonce) t2,
  Validate.range pLen .p (.local t2) true]

def deriveSized : Nat → Nat → Prog isa := Generate.deriveSizedWith deriveCompute

def deriveKey : Prog isa := Generate.deriveKeyWith deriveSized

end VG.Impl.Dsa.X86.Comb
