module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Shared BrainpoolP512r1 Montgomery products on x86-64 -/

@[expose] public section
namespace VG.Artifacts.WeierstrassMontBrainpoolP512r1.X86_64
open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86_64.Mont

def artifacts : List Artifact := [
  brainpoolp512r1p.mulApi.artifact X86_64.target {
    code := Wide8.fn false
    verified := VG.Proof.Weierstrass.X86_64.Mont.Wide8.verified false },
  brainpoolp512r1n.mulApi.artifact X86_64.target {
    code := Wide8.fn true
    verified := VG.Proof.Weierstrass.X86_64.Mont.Wide8.verified true }
]

end VG.Artifacts.WeierstrassMontBrainpoolP512r1.X86_64
