module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Instances
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # DSA parameter generation on PPC64LE, calling the probable-prime tests over each Miller–Rabin round -/

@[expose] public section

namespace VG.Artifacts.DsaParameters.PPC64LE
open VG Proof.Dsa.PPC64LE.Gen

def artifactsFor (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.Dsa.parameterSearchApi.artifact PPC64LE.target {
    suffix := v.suffix
    code := Impl.Dsa.PPC64LE.Generation.code (gen1 v) (gen2 v) (gen3 v)
    stack := 176
    verified := search_params v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MillerRabin.PPC64LE.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.DsaParameters.PPC64LE
