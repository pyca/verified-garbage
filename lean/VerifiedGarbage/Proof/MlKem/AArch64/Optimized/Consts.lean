module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables
public import VerifiedGarbage.Proof.Framework.AArch64.StackScratchConsts
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Words
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Fast
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Ntt16 VG.Impl.MlKem.AArch64.Ntt16.Readonly

def constants : List (String × List (BitVec 64)) :=
 [("VG_MLKEM_REJ_SHUFFLE",Impl.MlKem.AArch64.Rej8.tableWords),
  ("VG_MLKEM_GAMMA",words 32 gammaTable),
  ("VG_MLKEM_NTT16_ZETAS",words 16 tableHalves),
  ("VG_MLKEM_INTT16_ZETAS",words 16 invTableHalves),
  ("VG_MLKEM16_NTT_ZETAS",Fast.tabWords)]

theorem constants_regions (s : State) : constRegs constants s =
 [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩,⟨s.syms "VG_MLKEM_GAMMA",512⟩,
  ⟨s.syms "VG_MLKEM_NTT16_ZETAS",512⟩,⟨s.syms "VG_MLKEM_INTT16_ZETAS",512⟩,
  ⟨s.syms "VG_MLKEM16_NTT_ZETAS",928⟩] := by
 simp only [constRegs,Abi.constRegions,constants,List.map_cons,List.map_nil,
  Rej8.tableWords_length,Ntt16.Readonly.gamma_length,Ntt16.Readonly.forward_length,
  Ntt16.Readonly.inverse_length,NttR.tabWords_length]

theorem tables_of_consts {s : State} (h : ConstsOk constants 16 s) : Tables s := by
 have read : ∀r∈constRegs constants s,Covers [r] (s.rd++s.wr) := by
  intro r hr
  apply Covers.of_mem
  intro q hq
  rw [List.mem_singleton.mp hq]
  apply List.mem_append_left
  rw [←h.1] at hr
  exact List.mem_of_mem_drop hr
 have apart : ∀r∈constRegs constants s,∀q∈s.wr,r.Disjoint q := fun r hr=> (h.2.2 r hr).2.1
 have stack : ∀r∈constRegs constants s,r.Disjoint (below s.sp 16) := by
  intro r hr
  exact (h.2.2 r hr).2.2 _ (by simp [abi,stackBelow])
 have sh : (⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩:Region)∈constRegs constants s := by rw [constants_regions]; simp
 have ga : (⟨s.syms "VG_MLKEM_GAMMA",512⟩:Region)∈constRegs constants s := by rw [constants_regions]; simp
 have fw : (⟨s.syms "VG_MLKEM_NTT16_ZETAS",512⟩:Region)∈constRegs constants s := by rw [constants_regions]; simp
 have iv : (⟨s.syms "VG_MLKEM_INTT16_ZETAS",512⟩:Region)∈constRegs constants s := by rw [constants_regions]; simp
 have fa : (⟨s.syms "VG_MLKEM16_NTT_ZETAS",928⟩:Region)∈constRegs constants s := by rw [constants_regions]; simp
 have held := h.2.1
 simp only [Abi.constsHeld,constants,List.forall_mem_cons] at held
 refine ⟨?_,read _ sh,apart _ sh,stack _ sh,?_,read _ ga,apart _ ga,stack _ ga,
  ⟨⟨?_,read _ fw,apart _ fw⟩,⟨?_,read _ iv,apart _ iv⟩,stack _ fw,stack _ iv,
   ⟨?_,read _ fa,apart _ fa⟩,stack _ fa⟩⟩
 · intro i hi
   exact held.1 i (by rw [Rej8.tableWords_length]; exact hi)
 · intro i hi
   exact held.2.1 i (by rw [Ntt16.Readonly.gamma_length]; exact hi)
 · intro i hi
   have hx := held.2.2.1 i (by rw [Ntt16.Readonly.forward_length]; exact hi)
   rw [Ntt16.Readonly.forward_words i hi] at hx
   exact hx
 · intro i hi
   have hx := held.2.2.2.1 i (by rw [Ntt16.Readonly.inverse_length]; exact hi)
   rw [Ntt16.Readonly.inverse_words i hi] at hx
   exact hx
 · intro i hi
   have hx := held.2.2.2.2.1 i (by rw [NttR.tabWords_length]; exact hi)
   rw [NttR.tabWords_get i hi] at hx
   exact hx
end VG.Proof.MlKem.AArch64.Optimized
