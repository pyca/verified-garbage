module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontBrainpoolP512r1

/-! # Shared BrainpoolP512r1 Montgomery products on AArch64 -/

@[expose] public section
namespace VG.Artifacts.WeierstrassMontBrainpoolP512r1.AArch64
open VG.Spec.Weierstrass.Mont VG.Impl.Weierstrass.AArch64.Mont VG.Proof.Weierstrass.AArch64.Mont

def artifacts : List Artifact := [
  { brainpoolp512r1p.mulApi with
    target := AArch64.target
    doc := brainpoolp512r1p.mulApi.doc
    code := mulFn brainpoolp512r1p.k brainpoolp512r1p.m
    contract := brainpoolp512r1p.mulContract AArch64.abi
    verified := brainpoolp512r1p_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { brainpoolp512r1n.mulApi with
    target := AArch64.target
    doc := brainpoolp512r1n.mulApi.doc
    code := mulFn brainpoolp512r1n.k brainpoolp512r1n.m
    contract := brainpoolp512r1n.mulContract AArch64.abi
    verified := brainpoolp512r1n_mul_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }
]

end VG.Artifacts.WeierstrassMontBrainpoolP512r1.AArch64
