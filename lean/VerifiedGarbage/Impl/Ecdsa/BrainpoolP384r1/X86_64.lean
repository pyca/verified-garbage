module

public import VerifiedGarbage.Impl.Ecdsa.X86_64

/-! # brainpoolP384r1 signing on x86-64, using the general complete-addition ladder -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def brainpoolp384r1 : Cfg where
  n := 6
  C := Spec.BrainpoolP384r1.curve
  fastN := true
  windows := false
  mul := some Impl.Weierstrass.Mul.brainpoolp384r1
  inverse := some Impl.Weierstrass.Inverse.brainpoolp384r1
  checkPoint := some Impl.Weierstrass.CheckPoint.brainpoolp384r1

def signBrainpoolP384r1 : Prog isa := brainpoolp384r1.sign

end VG.Impl.Ecdsa.X86_64
