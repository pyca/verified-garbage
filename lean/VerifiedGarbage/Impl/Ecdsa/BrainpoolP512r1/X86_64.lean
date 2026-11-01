module

public import VerifiedGarbage.Impl.Ecdsa.X86_64

/-! # brainpoolP512r1 signing on x86-64, using the general complete-addition ladder -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def brainpoolp512r1 : Cfg where
  n := 8
  C := Spec.BrainpoolP512r1.curve
  fastN := true
  windows := false
  mul := some Impl.Weierstrass.Mul.brainpoolp512r1
  inverse := some Impl.Weierstrass.Inverse.brainpoolp512r1
  checkPoint := some Impl.Weierstrass.CheckPoint.brainpoolp512r1

def signBrainpoolP512r1 : Prog isa := brainpoolp512r1.sign

end VG.Impl.Ecdsa.X86_64
