module

public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Correct
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Timing
public import VerifiedGarbage.Proof.Ffdh.AArch64.VettedValidation.Sat
import VerifiedGarbage.Proof.Framework.GetElem

/-! Exact standard-group acceptance implements the existing checked-domain API. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.VettedValidation
open VG VG.AArch64 VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive
open VG.Impl.Ffdh.AArch64.Cached

theorem implies : contract.Implies (Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)) where
  pre:=fun _ h =>shared_pre h
  post:=fun _ _ _ h =>shared_post h
  pub:=by
    rintro s t _ _ h
    obtain ⟨plain,symbols⟩:=pub_consts.mp h
    sig_pub [Spec.Ffdh.checkDomainContract,Spec.Ffdh.checkDomainSig,abi,argRegs] at plain
    obtain ⟨sp,dom,r0,r1,r2,r3,r4⟩:=plain
    exact ⟨⟨sp,dom,r0,r1,r2,r3,r4⟩,symbols _ List.mem_cons_self⟩
  sat:=shared_sat

theorem verified (W : Window) (M : Mont) (S : Selector) :
    Verified target (VG.Impl.Ffdh.AArch64.VettedValidation.code W.code S.code M.mm)
      (Spec.Ffdh.checkDomainContract (abi.withConsts Policy.tableConsts)) := by
  refine Verified.of_correct (k:=contract) ?_ (constantTime W M S) implies
  intro s h
  obtain ⟨trace,t,run,preserved,post⟩:=correct W M S h
  exact ⟨trace,t,run,preserved,post⟩

end VG.Proof.Ffdh.AArch64.VettedValidation
