module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ffdh.X86_64
open VG.X86_64

def artifacts : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact target {
    code := Impl.Ffdh.X86_64.Generation.init
    verified := Proof.Ffdh.X86_64.Generation.init_verified },
  Spec.Ffdh.keyInitApi.artifact target {
    code := Impl.Ffdh.X86_64.KeyGeneration.init
    verified := Proof.Ffdh.X86_64.KeyGeneration.init_verified }]
end VG.Artifacts.Ffdh.X86_64
