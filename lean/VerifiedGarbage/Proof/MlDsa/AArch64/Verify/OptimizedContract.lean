import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSat
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedTimingBase

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (Ok3 StaticRoots RootSymbolsEq signRootConsts)

/-- Internal proof boundary retains the original verifier semantics and adds
only the immutable transform tables and their public addresses. -/
def verifyK (p : Params) (S : Nat) : Contract isa where
  pre s := vPre p S s ∧ StaticRoots S s
  post := (verifyContract p abi S).post
  pub s t := vPub p S s t ∧ RootSymbolsEq s t

theorem shared_pub {p : Params} {S : Nat} {s t : State}
    (h : (verifyContract p (abi.withConsts signRootConsts) S).pub s t) :
    vPub p S s t ∧ RootSymbolsEq s t := by
  sig_pub [verifyContract,verifySig,abi,argRegs,Abi.withConsts,Sign.signRootConsts_eq] at h
  obtain ⟨hsp,hf,hi,hb,h0,h1,h2,h3⟩ := h
  refine ⟨?_,hf,hi⟩
  unfold vPub
  sig_pub [verifyContract,verifySig,abi,argRegs]
  exact ⟨hsp,hb,h0,h1,h2,h3⟩

theorem verifyK_implies {p : Params} (hp : Ok3 p) :
    (verifyK p 16).Implies (verifyContract p (abi.withConsts signRootConsts) 16) where
  pre := fun _ h=>entry (by decide) h
  post := by
    sig_implies_post [verifyK,verifyContract,verifySig,abi,argRegs,Abi.withConsts]
  pub := fun _ _ _ _ h=>shared_pub h
  sat := ⟨verifySat p,verify_sat hp⟩

end VG.Proof.MlDsa.AArch64.Verify.Optimized
