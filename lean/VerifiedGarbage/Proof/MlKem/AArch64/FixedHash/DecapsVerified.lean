module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsChecks
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsPrefix
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Optimized

theorem decaps768_ct (v : Proof.Sha3.AArch64.Permutation) :
 ConstantTime isa (entryContract (decapsAArch64 lay768)).pre (entryContract (decapsAArch64 lay768)).pub
  (FixedHashDecaps.decapsUsing (fixedHash v.callee) (prf v.callee) lay768) :=
 decaps_using_ct VG.Proof.MlKem.AArch64.KeyGen.wf768
  (fun hp tables=>decaps_using_prefix (fixedHash v.callee) (deG768_correct v) hp VG.Proof.MlKem.AArch64.Encaps.calls768 tables (deStart768_depth v))
  (deStart768_taint v.callee (symSums v)) (deRest768_taint v.callee (symSums v))

theorem decaps768_verified (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target
 (FixedHashDecaps.decapsUsing (fixedHash v.callee) (prf v.callee) lay768) decaps768Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (decapsAArch64 lay768)) ?_ (decaps768_ct v) ?_
 · intro s h
   exact Decaps.using_correct (fixedHash v.callee) (prf_valid v) (deG768_correct v) (deJ768_correct v)
    (kem_unstrip (Decaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 h.1)) Noise.room768 VG.Proof.MlKem.AArch64.Encaps.calls768
    (entry_tables h) (deStart768_depth v) kemMatrix768_depth
 · exact ⟨fun _ h=>decaps768_entry h,fun _ _ h hp=>decaps768_post h hp,
    fun _ _ hs ht hp=>decaps768_pub hs ht hp,decaps768_sat⟩

theorem decaps1024_ct (v : Proof.Sha3.AArch64.Permutation) :
 ConstantTime isa (entryContract (decapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pre (entryContract (decapsAArch64 Impl.MlKem1024.AArch64.lay1024)).pub
  (FixedHashDecaps.decapsUsing (fixedHash v.callee) (prf v.callee) Impl.MlKem1024.AArch64.lay1024) :=
 decaps_using_ct VG.Proof.MlKem1024.AArch64.KeyGen.wf1024
  (fun hp tables=>decaps_using_prefix (fixedHash v.callee) (deG1024_correct v) hp VG.Proof.MlKem1024.AArch64.Encaps.calls1024 tables (deStart1024_depth v))
  (deStart1024_taint v.callee (symSums v)) (deRest1024_taint v.callee (symSums v))

theorem decaps1024_verified (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target
 (FixedHashDecaps.decapsUsing (fixedHash v.callee) (prf v.callee) Impl.MlKem1024.AArch64.lay1024) decaps1024Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (decapsAArch64 Impl.MlKem1024.AArch64.lay1024)) ?_ (decaps1024_ct v) ?_
 · intro s h
   exact Decaps.using_correct (fixedHash v.callee) (prf_valid v) (deG1024_correct v) (deJ1024_correct v)
    (kem_unstrip (Decaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 h.1)) Noise.room1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024
    (entry_tables h) (deStart1024_depth v) kemMatrix1024_depth
 · exact ⟨fun _ h=>decaps1024_entry h,fun _ _ h hp=>decaps1024_post h hp,
    fun _ _ hs ht hp=>decaps1024_pub hs ht hp,decaps1024_sat⟩
end VG.Proof.MlKem.AArch64.FixedHash
