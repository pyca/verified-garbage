module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptCorrect
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.AttemptSat
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit

/-! Cached native generation is correct, constant time, ABI preserving, and satisfiable. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Spec.Ffdh

theorem attempt_implies : attemptContract.Implies (cachedGenerateKeyContract abi) where
 pre:=fun _ h =>attempt_shared_pre h
 post:=by
  sig_implies_post [cachedGenerateKeyContract,cachedGenerateKeySig,generateKeySig,abi,argRegs,
   attemptContract,attemptPost,stackArgs_five,List.append_eq]
 pub:=by
  rintro s t _ _ h
  sig_pub [cachedGenerateKeyContract,cachedGenerateKeySig,generateKeySig,abi,argRegs,attemptContract,attemptPub,
   stackArgs_five,List.append_eq] at h
  simp only [List.getD_cons_succ,List.getD_cons_zero] at h
  obtain ⟨sp,leak,r0,r1,r2,r3,r4,r5,r6,r7,a0,a1,a2,a3,a4⟩:=h
  refine ⟨?_,sp,by rw [stackArgs_five,stackArgs_five,a0,a1,a2,a3,a4],?_⟩
  · simp only [argRegs,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
    exact ⟨r0,r1,r2,r3,r4,r5,r6,r7⟩
  · unfold attemptLeak;exact leak
 sat:=attempt_shared_sat

theorem attempt_verified (M : Mont) : Verified target (Generate.code M.mm) (cachedGenerateKeyContract abi) :=by
 refine Verified.of_correct (k:=attemptContract) ?_ (attempt_constantTime M) attempt_implies
 intro s h
 obtain ⟨trace,t,run,preserved,post⟩:=attempt_correct M h
 exact ⟨trace,t,run,preserved,post⟩

end VG.Proof.Ffdh.AArch64.Cached
