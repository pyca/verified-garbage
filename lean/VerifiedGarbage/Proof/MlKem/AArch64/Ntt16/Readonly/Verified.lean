module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Sat
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Spec.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16 VG.Impl.MlKem.AArch64.Ntt16.Readonly

theorem fwd_verified : Verified target fwd (nttContract (abi.withConsts fwdConsts)) := by
  refine Verified.of_correct fwd_correct fwd_ct
    { pre := fun s h => shared_pre _ _ _ _ forward_length forward_words h
      post := ?_,pub := ?_,sat := ?_ }
  · intro s t _ h
    sig_post [nttContract,inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,fwdConsts]
    exact h
  · intro s t _ _ h
    sig_pub [nttContract,inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,fwdConsts] at h
    exact ⟨h.1,h.2.2.1,h.2.2.2,h.2.1⟩
  · exact ⟨sat (words 16 tableHalves),shared_sat _ _ _ forward_length⟩

theorem inv_verified : Verified target inv (nttInvContract (abi.withConsts invConstsTable)) := by
  refine Verified.of_correct inv_correct inv_ct
    { pre := fun s h => shared_pre _ _ _ _ inverse_length inverse_words h
      post := ?_,pub := ?_,sat := ?_ }
  · intro s t _ h
    sig_post [nttInvContract,inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,invConstsTable]
    exact h
  · intro s t _ _ h
    sig_pub [nttInvContract,inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,invConstsTable] at h
    exact ⟨h.1,h.2.2.1,h.2.2.2,h.2.1⟩
  · exact ⟨sat (words 16 invTableHalves),shared_sat _ _ _ inverse_length⟩

end VG.Proof.MlKem.AArch64.Ntt16.Readonly
