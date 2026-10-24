module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeCorrect
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeSat
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-! The complete native initializer satisfies the reviewed ABI and public-table convention. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Spec.Ffdh

theorem precompute_implies : precomputeContract.Implies (generationPrecomputeContract (abi.withConsts Policy.tableConsts)) where
 pre:=fun _ h=>precompute_shared_pre h
 post:=by
  intro s t _ h
  apply post_consts.mpr
  have shared : ∀ s t,True → precomputeContract.post s t → (generationPrecomputeContract abi).post s t :=by
   sig_implies_post [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs,precomputeContract,precomputePost]
  exact shared s t True.intro h
 pub:=by
  rintro s t _ _ h
  obtain ⟨plain,symbols⟩:=pub_consts.mp h
  sig_pub [generationPrecomputeContract,generationPrecomputeSig,abi,argRegs] at plain
  obtain ⟨sp,dom,r0,r1,r2,r3,r4,r5,r6⟩:=plain
  exact ⟨sp,dom,r0,r1,r2,r3,r4,r5,r6,symbols _ List.mem_cons_self⟩
 sat:=precompute_shared_sat

theorem precompute_verified (M : Mont) : Verified target (Precompute.code M.mm)
 (generationPrecomputeContract (abi.withConsts Policy.tableConsts)) :=by
 refine Verified.of_correct (k:=precomputeContract) ?_ (precompute_constantTime M) precompute_implies
 intro s h
 obtain ⟨trace,t,run,preserved,post⟩:=precompute_correct M h
 exact ⟨trace,t,run,preserved,post⟩

end VG.Proof.Ffdh.AArch64.Cached
