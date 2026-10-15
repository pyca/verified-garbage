module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Weierstrass.X86_64.MontWide8Verified

/-! # Shared BrainpoolP512r1 Montgomery products on x86-64 -/

@[expose] public section
namespace VG.Artifacts.WeierstrassMontBrainpoolP512r1.X86_64
open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.X86_64.Mont

def artifacts : List Artifact := [
  { brainpoolp512r1p.mulApi with
    target := X86_64.target
    doc := brainpoolp512r1p.mulApi.doc
    code := Wide8.fn false
    contract := brainpoolp512r1p.mulContract X86_64.abi
    verified := VG.Proof.Weierstrass.X86_64.Mont.Wide8.verified false
    spSafe := Code.all_of_allInstrs (by decide +kernel) },
  { brainpoolp512r1n.mulApi with
    target := X86_64.target
    doc := brainpoolp512r1n.mulApi.doc
    code := Wide8.fn true
    contract := brainpoolp512r1n.mulContract X86_64.abi
    verified := VG.Proof.Weierstrass.X86_64.Mont.Wide8.verified true
    spSafe := Code.all_of_allInstrs (by decide +kernel) }
]

end VG.Artifacts.WeierstrassMontBrainpoolP512r1.X86_64
