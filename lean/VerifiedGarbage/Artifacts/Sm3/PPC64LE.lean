module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Sm3.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # SM3 (GB/T 32905-2016) on PPC64LE -/

namespace VG.Artifacts.Sm3.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Sm3.initApi.artifact PPC64LE.target {
    code := Impl.Sm3.PPC64LE.Stream.init
    verified := Proof.Sm3.PPC64LE.init_scrubbed },
  Spec.Sm3.updateApi.artifact PPC64LE.target {
    code := Impl.Sm3.PPC64LE.Fn.update
    verified := Proof.Sm3.PPC64LE.update_scrubbed },
  Spec.Sm3.finalizeApi.artifact PPC64LE.target {
    code := Impl.Sm3.PPC64LE.Fn.finalize
    verified := Proof.Sm3.PPC64LE.finalize_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Sm3.PPC64LE
