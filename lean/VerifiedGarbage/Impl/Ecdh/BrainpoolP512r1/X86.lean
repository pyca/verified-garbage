module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.X86

/-! # ECDH over brainpoolP512r1 on x86 (32-bit): eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_brainpoolp512r1`. -/
def exchangeBrainpoolP512r1 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.brainpoolp512r1

end VG.Impl.Ecdh.X86
