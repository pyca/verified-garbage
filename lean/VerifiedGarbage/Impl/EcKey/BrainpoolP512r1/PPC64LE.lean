module

public import VerifiedGarbage.Impl.EcKey.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE

/-! # brainpoolP512r1 public keys on PPC64LE: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.PPC64LE

open VG.PPC64LE

/-- `vg_ec_brainpoolp512r1_public_key`. -/
def publicKeyBrainpoolP512r1 : Prog isa := Cfg.publicKey Impl.Ecdsa.PPC64LE.brainpoolp512r1

end VG.Impl.EcKey.PPC64LE
