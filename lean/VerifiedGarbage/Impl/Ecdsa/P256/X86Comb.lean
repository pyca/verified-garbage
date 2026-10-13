module

public import VerifiedGarbage.Impl.Ecdsa.P256.X86
public import VerifiedGarbage.Impl.P256.CombTable7

/-! # P-256's seven-bit fixed-base comb on 32-bit x86 -/

@[expose] public section

namespace VG.Impl.Ecdsa.X86
open VG.X86

def p256Comb : Cfg := { p256 with
  comb := some ⟨7, Impl.P256.p256Comb7, Impl.P256.p256Comb7Start, "VG_P256_COMB"⟩ }

def signP256Comb : Prog isa := p256Comb.signComb

end VG.Impl.Ecdsa.X86
