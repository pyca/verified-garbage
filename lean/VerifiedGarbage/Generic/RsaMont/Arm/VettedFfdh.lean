module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ARM key-generation artifacts are emitted by CachedFfdh -/

@[expose] public section
namespace VG.Generic.RsaMont.Arm.VettedFfdh
open VG

def artifacts (_v : Proof.Bignum.Arm.MontBackend) : List Artifact := []

end VG.Generic.RsaMont.Arm.VettedFfdh
