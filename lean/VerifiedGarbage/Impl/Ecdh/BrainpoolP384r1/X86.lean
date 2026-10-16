module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.X86

/-! # ECDH over brainpoolP384r1 on x86 (32-bit): six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_brainpoolp384r1`. -/
def exchangeBrainpoolP384r1 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.brainpoolp384r1

end VG.Impl.Ecdh.X86
