module

public import VerifiedGarbage.Impl.Ffdh.AArch64.VettedValidation
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyConsts
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.Omega

/-! The unchanged domain-check contract with its public recognition table. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open CheckDomain

abbrev plain (s : State) : State := stripConsts Policy.tableConsts s

def pre (s : State) : Prop := cdPre (plain s) ∧ ConstsOk Policy.tableConsts 0 s

def pub (s t : State) : Prop := cdPub s t ∧ s.syms Policy.tableSym=t.syms Policy.tableSym

def contract : Contract isa where
  pre := pre
  post := cdPost
  pub := pub

theorem shared_pre {s : State}
    (h : (Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)).pre s) : pre s := by
  obtain ⟨h,c⟩:=pre_consts.mp h
  exact ⟨cd_implies.pre _ h,c⟩

theorem shared_post {s t : State} (h : cdPost s t) :
    (Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)).post s t := by
  apply post_consts.mpr
  have post : ∀ s t, True → cdPost s t → (Spec.Ffdh.checkDomainContract abi).post s t := by
    sig_implies_post [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi, argRegs, cdPost, cdDom]
  exact post s t True.intro h

end VG.Proof.Ffdh.AArch64.VettedValidation
