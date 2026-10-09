import VerifiedGarbage.Impl.Ecdsa.X86_64
import VerifiedGarbage.Spec.P192

/-! # p192 signing on x86-64, using the general complete-addition ladder -/

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64

def p192 : Cfg where
  n := 4
  C := Spec.P192.curve
  fastN := true
  windows := false

def signP192 : Prog isa := p192.sign

end VG.Impl.Ecdsa.X86_64
