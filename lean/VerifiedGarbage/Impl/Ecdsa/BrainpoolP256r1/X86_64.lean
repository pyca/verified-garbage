module

public import VerifiedGarbage.Impl.Ecdsa.X86_64

/-! # brainpoolP256r1 signing on x86-64, using the general complete-addition ladder -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def brainpoolp256r1 : Cfg where
  n := 4
  C := Spec.BrainpoolP256r1.curve
  fastN := true
  windows := false
  mul := some Impl.Weierstrass.Mul.brainpoolp256r1
  inverse := some Impl.Weierstrass.Inverse.brainpoolp256r1
  checkPoint := some Impl.Weierstrass.CheckPoint.brainpoolp256r1

def signBrainpoolP256r1 : Prog isa := brainpoolp256r1.sign

end VG.Impl.Ecdsa.X86_64
