module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Zeroize.Contract
import VerifiedGarbage.Proof.Zeroize.PPC64LE
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Zeroization on PPC64LE -/

namespace VG.Artifacts.Zeroize.PPC64LE
open VG.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.PPC64LE.zeroize
    verified := Proof.Zeroize.PPC64LE.zeroize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Zeroize.PPC64LE
