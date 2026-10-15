module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Optimized

theorem keyGen768_verified
 (hG : HashCorrect fixedHash .x28 KG.ST KG.WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩])
 (hH : HashCorrect fixedHash .x28 KG.ST KG.WK 136 6
  [⟨.x26,0,lay768.ekLen⟩] [⟨.x27,768*lay768.k+32,32⟩]) :
 Verified AArch64.target (FixedHashCallers.keyGenUsing fixedHash lay768) keyGen768Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (keyGenAArch64 lay768)) ?_
  (keyGen_using_ct fixedHash hG VG.Proof.MlKem.AArch64.KeyGen.wf768 kgA768_depth kgA768_taint kgRest768_taint) ?_
 · intro s h
   exact KeyGen.using_correct fixedHash hH hG (entry_keygen VG.Proof.MlKem.AArch64.KeyGen.wf768 h).1 Noise.room768
    (entry_tables h) kgA768_depth kgMatrix768_depth
 · exact ⟨fun _ h=>keyGen768_entry h,fun _ _ h hp=>keyGen768_post h hp,
    fun _ _ hs ht hp=>keyGen768_pub hs ht hp,keyGen768_sat⟩

theorem keyGen1024_verified
 (hG : HashCorrect fixedHash .x28 KG.ST KG.WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩])
 (hH : HashCorrect fixedHash .x28 KG.ST KG.WK 136 6
  [⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x27,768*Impl.MlKem1024.AArch64.lay1024.k+32,32⟩]) :
 Verified AArch64.target (FixedHashCallers.keyGenUsing fixedHash Impl.MlKem1024.AArch64.lay1024) keyGen1024Contract := by
 refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (keyGenAArch64 Impl.MlKem1024.AArch64.lay1024)) ?_
  (keyGen_using_ct fixedHash hG VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 kgA1024_depth kgA1024_taint kgRest1024_taint) ?_
 · intro s h
   exact KeyGen.using_correct fixedHash hH hG (entry_keygen VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 h).1 Noise.room1024
    (entry_tables h) kgA1024_depth kgMatrix1024_depth
 · exact ⟨fun _ h=>keyGen1024_entry h,fun _ _ h hp=>keyGen1024_post h hp,
    fun _ _ hs ht hp=>keyGen1024_pub hs ht hp,keyGen1024_sat⟩
end VG.Proof.MlKem.AArch64.FixedHash
