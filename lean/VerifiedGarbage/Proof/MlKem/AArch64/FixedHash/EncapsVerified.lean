module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.EncapsChecks
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Optimized

theorem encaps768_ct :
 ConstantTime isa (entryContract (encapsAArch64 lay768)).pre (entryContract (encapsAArch64 lay768)).pub
  (Impl.MlKem.AArch64.Optimized.encapsUsing (FixedHashCallers.enAUsing fixedHash lay768) prf lay768) :=
 encaps_using_ct enH768_correct enG768_correct VG.Proof.MlKem.AArch64.KeyGen.wf768 enA768_depth enA768_taint enRest768_taint

theorem encaps768_verified : Verified AArch64.target (Impl.MlKem.AArch64.Optimized.encapsUsing (FixedHashCallers.enAUsing fixedHash lay768) prf lay768) encaps768Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (encapsAArch64 lay768)) ?_ encaps768_ct ?_
 · intro s h
   exact Encaps.using_correct fixedHash prf_valid enH768_correct enG768_correct
    (kem_unstrip (Encaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 h.1)) Noise.room768 VG.Proof.MlKem.AArch64.Encaps.calls768
    (entry_tables h) enA768_depth kemMatrix768_depth
 · exact ⟨fun _ h=>encaps768_entry h,fun _ _ h hp=>encaps768_post h hp,
    fun _ _ hs ht hp=>encaps768_pub hs ht hp,encaps768_sat⟩

theorem encaps1024_ct :
 ConstantTime isa (entryContract (encapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pre (entryContract (encapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pub
  (Impl.MlKem.AArch64.Optimized.encapsUsing (FixedHashCallers.enAUsing fixedHash Impl.MlKem1024.AArch64.lay1024) prf Impl.MlKem1024.AArch64.lay1024) :=
 encaps_using_ct enH1024_correct enG1024_correct VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 enA1024_depth enA1024_taint enRest1024_taint

theorem encaps1024_verified : Verified AArch64.target (Impl.MlKem.AArch64.Optimized.encapsUsing (FixedHashCallers.enAUsing fixedHash Impl.MlKem1024.AArch64.lay1024) prf Impl.MlKem1024.AArch64.lay1024) encaps1024Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (encapsAArch64 Impl.MlKem1024.AArch64.lay1024)) ?_ encaps1024_ct ?_
 · intro s h
   exact Encaps.using_correct fixedHash prf_valid enH1024_correct enG1024_correct
    (kem_unstrip (Encaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 h.1)) Noise.room1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024
    (entry_tables h) enA1024_depth kemMatrix1024_depth
 · exact ⟨fun _ h=>encaps1024_entry h,fun _ _ h hp=>encaps1024_post h hp,
    fun _ _ hs ht hp=>encaps1024_pub hs ht hp,encaps1024_sat⟩
end VG.Proof.MlKem.AArch64.FixedHash
