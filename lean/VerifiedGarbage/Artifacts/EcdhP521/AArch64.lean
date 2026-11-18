module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.Ecdh.P521
public import VerifiedGarbage.TCB.AArch64.Print

/-! # ECDH over P-521 (SP 800-56A) on AArch64 -/

@[expose] public section
namespace VG.Artifacts.EcdhP521.AArch64

def artifacts : List Artifact := [
  Spec.Ecdh.P521.exchangeApi.artifact AArch64.target Proof.Weierstrass.AArch64.P521Native.Scrub.exchangeReg]

end VG.Artifacts.EcdhP521.AArch64
