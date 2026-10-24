module

public import VerifiedGarbage.Impl.Ecdsa.Verify.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LE

/-! # `vg_ecdsa_brainpoolp512r1_verify` on PPC64LE -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.PPC64LE

open VG.PPC64LE

/-- `vg_ecdsa_brainpoolp512r1_verify`. -/
def verifyBrainpoolP512r1 : Prog isa := Cfg.verify Impl.Ecdsa.PPC64LE.brainpoolp512r1

end VG.Impl.Ecdsa.Verify.PPC64LE
