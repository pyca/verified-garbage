module

public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm

/-! # ARM key-generation artifacts are emitted by CachedFfdh -/

@[expose] public section

namespace VG.Artifacts.VettedFfdh.Arm
open VG

def artifactsFor (_v : Proof.Bignum.Arm.MontBackend) : List Artifact := []

def artifacts : List Artifact :=
  VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.VettedFfdh.Arm
