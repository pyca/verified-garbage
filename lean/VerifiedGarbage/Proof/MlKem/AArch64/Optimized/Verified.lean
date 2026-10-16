module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Timing
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenCorrect
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsCorrect
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecapsCorrect
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Proof.MlKem VG.Impl.MlKem.AArch64

theorem keyGen768_verified : Verified AArch64.target
 (Impl.MlKem.AArch64.Optimized.keyGenWith Sha3.AArch64.Sha3.callee lay768) keyGen768Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (keyGenAArch64 lay768)) ?_ keyGen768_ct ?_
 · intro s h
   exact KeyGen.optimized_correct (keccak:=Sha3.AArch64.Sha3.backend) (entry_keygen VG.Proof.MlKem.AArch64.KeyGen.wf768 h).1 Noise.room768 (entry_tables h) kgA768_depth kgMatrix768_depth
 · exact ⟨fun _ h=>keyGen768_entry h,fun _ _ h hp=>keyGen768_post h hp,
  fun _ _ hs ht hp=>keyGen768_pub hs ht hp,keyGen768_sat⟩

theorem encaps768_verified : Verified AArch64.target
 (Impl.MlKem.AArch64.Optimized.encapsWith Sha3.AArch64.Sha3.callee lay768) encaps768Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (encapsAArch64 lay768)) ?_ encaps768_ct ?_
 · intro s h
   exact Encaps.optimized_correct (keccak:=Sha3.AArch64.Sha3.backend) (kem_unstrip (Encaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 h.1)) Noise.room768 VG.Proof.MlKem.AArch64.Encaps.calls768 (entry_tables h) enA768_depth kemMatrix768_depth
 · exact ⟨fun _ h=>encaps768_entry h,fun _ _ h hp=>encaps768_post h hp,
  fun _ _ hs ht hp=>encaps768_pub hs ht hp,encaps768_sat⟩

theorem decaps768_verified : Verified AArch64.target
 (Impl.MlKem.AArch64.Optimized.decapsWith Sha3.AArch64.Sha3.callee lay768) decaps768Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (decapsAArch64 lay768)) ?_ decaps768_ct ?_
 · intro s h
   exact Decaps.optimized_correct (keccak:=Sha3.AArch64.Sha3.backend) (kem_unstrip (Decaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 h.1)) Noise.room768 VG.Proof.MlKem.AArch64.Encaps.calls768 (entry_tables h) deStart768_depth kemMatrix768_depth
 · exact ⟨fun _ h=>decaps768_entry h,fun _ _ h hp=>decaps768_post h hp,
  fun _ _ hs ht hp=>decaps768_pub hs ht hp,decaps768_sat⟩

theorem keyGen1024_verified : Verified AArch64.target
 (Impl.MlKem.AArch64.Optimized.keyGenWith Sha3.AArch64.Sha3.callee Impl.MlKem1024.AArch64.lay1024) keyGen1024Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (keyGenAArch64 Impl.MlKem1024.AArch64.lay1024)) ?_ keyGen1024_ct ?_
 · intro s h
   exact KeyGen.optimized_correct (keccak:=Sha3.AArch64.Sha3.backend) (entry_keygen VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 h).1 Noise.room1024 (entry_tables h) kgA1024_depth kgMatrix1024_depth
 · exact ⟨fun _ h=>keyGen1024_entry h,fun _ _ h hp=>keyGen1024_post h hp,
  fun _ _ hs ht hp=>keyGen1024_pub hs ht hp,keyGen1024_sat⟩

theorem encaps1024_verified : Verified AArch64.target
 (Impl.MlKem.AArch64.Optimized.encapsWith Sha3.AArch64.Sha3.callee Impl.MlKem1024.AArch64.lay1024) encaps1024Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (encapsAArch64 Impl.MlKem1024.AArch64.lay1024)) ?_ encaps1024_ct ?_
 · intro s h
   exact Encaps.optimized_correct (keccak:=Sha3.AArch64.Sha3.backend) (kem_unstrip (Encaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 h.1)) Noise.room1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024 (entry_tables h) enA1024_depth kemMatrix1024_depth
 · exact ⟨fun _ h=>encaps1024_entry h,fun _ _ h hp=>encaps1024_post h hp,
  fun _ _ hs ht hp=>encaps1024_pub hs ht hp,encaps1024_sat⟩

theorem decaps1024_verified : Verified AArch64.target
 (Impl.MlKem.AArch64.Optimized.decapsWith Sha3.AArch64.Sha3.callee Impl.MlKem1024.AArch64.lay1024) decaps1024Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (decapsAArch64 Impl.MlKem1024.AArch64.lay1024)) ?_ decaps1024_ct ?_
 · intro s h
   exact Decaps.optimized_correct (keccak:=Sha3.AArch64.Sha3.backend) (kem_unstrip (Decaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 h.1)) Noise.room1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024 (entry_tables h) deStart1024_depth kemMatrix1024_depth
 · exact ⟨fun _ h=>decaps1024_entry h,fun _ _ h hp=>decaps1024_post h hp,
  fun _ _ hs ht hp=>decaps1024_pub hs ht hp,decaps1024_sat⟩
end VG.Proof.MlKem.AArch64.Optimized
