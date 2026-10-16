module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.X86

/-! # ECDH over brainpoolP256r1 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_brainpoolp256r1`. -/
def exchangeBrainpoolP256r1 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.brainpoolp256r1

end VG.Impl.Ecdh.X86
