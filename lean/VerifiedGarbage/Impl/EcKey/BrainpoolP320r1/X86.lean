module

public import VerifiedGarbage.Impl.EcKey.X86
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP320r1.X86Comb

/-! # brainpoolP320r1 public keys on x86 (32-bit): five-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.X86

open VG.X86

/-- `vg_ec_brainpoolp320r1_public_key`. -/
def publicKeyBrainpoolP320r1 : Prog isa := Cfg.publicKeyComb Impl.Ecdsa.X86.brainpoolp320r1Comb

end VG.Impl.EcKey.X86
