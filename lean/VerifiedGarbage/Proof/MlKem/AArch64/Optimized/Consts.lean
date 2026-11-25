module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Forward
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Inverse

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16 VG.Impl.MlKem.AArch64.Ntt16.Readonly

def constants : List (String × List (BitVec 64)) :=
 [("VG_MLKEM_REJ_SHUFFLE",Impl.MlKem.AArch64.Rej8.tableWords),
  ("VG_MLKEM_GAMMA",words 32 gammaTable),
  (Inverse.name,Inverse.words),
  (Forward.name,Forward.words)]

theorem constants_regions (s : State) : constRegs constants s =
 [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩,⟨s.syms "VG_MLKEM_GAMMA",512⟩,
  ⟨s.syms Inverse.name,1216⟩,⟨s.syms Forward.name,1152⟩] := by
 simp only [constRegs,Abi.constRegions,constants,List.map_cons,List.map_nil,
  Rej8.tableWords_length,Ntt16.Readonly.gamma_length,Ntt16.inv_length,Ntt16.fwd_length]

theorem tables_of_consts {s : State} (h : ConstsOk constants 16 s) : Tables s := by
 have read : ∀r∈constRegs constants s,Covers [r] (s.rd++s.wr) := by
  intro r hr
  apply Covers.of_mem
  intro q hq
  rw [List.mem_singleton.mp hq]
  apply List.mem_append_left
  rw [←h.1] at hr
  exact List.mem_of_mem_drop hr
 have apart : ∀r∈constRegs constants s,∀q∈s.wr,r.Disjoint q := fun r hr=> (h.2.2.1 r hr).2.1
 have stack : ∀r∈constRegs constants s,r.Disjoint (below s.sp 16) := by
  intro r hr
  exact (h.2.2.1 r hr).2.2 _ (by simp [abi,stackBelow])
 have sh : (⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩:Region)∈constRegs constants s := by rw [constants_regions]; simp
 have ga : (⟨s.syms "VG_MLKEM_GAMMA",512⟩:Region)∈constRegs constants s := by rw [constants_regions]; simp
 have iv : (⟨s.syms Inverse.name,1216⟩:Region)∈constRegs constants s := by rw [constants_regions]; simp
 have fa : (⟨s.syms Forward.name,1152⟩:Region)∈constRegs constants s := by rw [constants_regions]; simp
 have held := h.2.1
 simp only [Abi.constsHeld,constants,List.forall_mem_cons] at held
 refine ⟨?_,read _ sh,apart _ sh,stack _ sh,?_,read _ ga,apart _ ga,stack _ ga,
  ⟨⟨?_,read _ fa,apart _ fa⟩,⟨?_,read _ iv,apart _ iv⟩,stack _ fa,stack _ iv⟩⟩
 · intro i hi
   exact held.1 i (by rw [Rej8.tableWords_length]; exact hi)
 · intro i hi
   exact held.2.1 i (by rw [Ntt16.Readonly.gamma_length]; exact hi)
 · intro i hi
   exact held.2.2.2.1 i (by rw [Ntt16.fwd_length]; exact hi)
 · intro i hi
   exact held.2.2.1 i (by rw [Ntt16.inv_length]; exact hi)
end VG.Proof.MlKem.AArch64.Optimized
