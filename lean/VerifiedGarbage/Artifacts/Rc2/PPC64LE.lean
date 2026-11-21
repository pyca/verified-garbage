module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.Block
public import VerifiedGarbage.Proof.Rc2.PPC64LE.KeyVerified
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Verified
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Cbc.Chained
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Scrub
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RC2 on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rc2.PPC64LE

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.Fn.cbcInit
    verified := Proof.Rc2.PPC64LE.Scrub.cbcInit_scrubbed },
  Spec.Rc2.cbcEncryptChainedApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.Fn.cbcEncryptChained
    verified := Proof.Rc2.PPC64LE.Scrub.cbcEncryptChained_scrubbed },
  Spec.Rc2.cbcDecryptChainedApi.artifact PPC64LE.target {
    code := Impl.Rc2.PPC64LE.Fn.cbcDecryptChained
    verified := Proof.Rc2.PPC64LE.Scrub.cbcDecryptChained_scrubbed }]

end VG.Artifacts.Rc2.PPC64LE
