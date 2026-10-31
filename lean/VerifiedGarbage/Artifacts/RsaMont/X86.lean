module

public import VerifiedGarbage.Impl.Mont.X86.Sse2
public import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
public import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Montgomery multiplication on i686 with SSE2 -/

@[expose] public section

namespace VG.Artifacts.RsaMont.X86

def runtime : Artifact :=
  Spec.Rsa.MontMul.mulApi.artifact X86.target {
    stack := 56
    code := Impl.Mont.X86.Sse2.atBody
    verified := Proof.Mont.X86.Sse2.at_verified }

def prepared : Artifact :=
  Spec.Rsa.Mont.mulApi.artifact X86.target {
    stack := 56
    code := Impl.Mont.X86.Sse2.preparedBody
    verified := Proof.Mont.X86.Sse2.prepared_verified }

def artifacts : List Artifact := [runtime, prepared]

end VG.Artifacts.RsaMont.X86
