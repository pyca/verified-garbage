module

public import VerifiedGarbage.Impl.Ecdsa.X86_64

/-! # secp256k1 signing on x86-64, using the general complete-addition ladder -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def secp256k1 : Cfg where
  n := 4
  C := Spec.Secp256k1.curve
  fastN := true
  windows := false
  mul := some Impl.Weierstrass.Mul.secp256k1
  inverse := some Impl.Weierstrass.Inverse.secp256k1
  checkPoint := some Impl.Weierstrass.CheckPoint.secp256k1

def signSecp256k1 : Prog isa := secp256k1.sign

end VG.Impl.Ecdsa.X86_64
