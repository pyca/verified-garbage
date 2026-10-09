import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedBatch

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (PairRegs)

def groupPairs (a b : Nat) : List PairRegs :=
  [⟨vr a,vr b,.v24⟩,⟨vr (a+8),vr (b+8),.v25⟩]

def groupProducts (b : Nat) : List MulRegs :=
  [⟨.v24,vr b,.v26⟩,⟨.v25,vr (b+8),.v27⟩]

theorem group_shape (a b : Fin 8) (hab : a≠b) :
    BatchShape (groupPairs a.val b.val) (groupProducts b.val) := by
  constructor
  · revert hab b a; decide +kernel
  · constructor <;> revert hab b a <;> decide +kernel
  · revert hab b a; decide +kernel
  · revert hab b a; decide +kernel
  · revert hab b a; decide +kernel
  · revert hab b a; decide +kernel
  · intro p hp
    simp only [groupPairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨⟨.v24,vr b.val,.v26⟩,by simp [groupProducts],rfl,rfl⟩
    · exact ⟨⟨.v25,vr (b.val+8),.v27⟩,by simp [groupProducts],rfl,rfl⟩

theorem group_code (a b : Nat) :
    batchPair a b=(groupPairs a b).flatMap PairRegs.code++renamedMultiply (groupProducts b) .v28 .v29 .v31 := rfl

end VG.Proof.MlDsa.AArch64.Optimized.Paired
