import VerifiedGarbage.Impl.Ecdsa.X86_64
import VerifiedGarbage.Spec.Secp256k1

/-! # secp256k1 signing on x86-64, using the general complete-addition ladder -/

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def secp256k1 : Cfg where
  n := 4
  C := Spec.Secp256k1.curve
  fastN := true
  windows := false

def signSecp256k1 : Prog isa := secp256k1.sign

end VG.Impl.Ecdsa.X86_64
