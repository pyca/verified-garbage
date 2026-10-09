import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def fiveSliceCode : List Instr := firstLoads ++ fiveCode ++ firstStores

def fiveSliceMem (u : Nat) (s : State) : Mem :=
  writeBank (fiveValues u (readBank s.mem (s.gpr .x0) 16)) (s.gpr .x0) 16 s.mem

theorem firstLoads_eq : firstLoads=(bankLoads (regs 0) 16).map (fun p => Instr.ldrq p.1 .x0 p.2) := by decide +kernel
theorem firstStores_eq : firstStores=(bankLoads (regs 7) 16).map (fun p => Instr.strq p.1 .x0 p.2) := rfl

theorem fiveSlice_ok (u : Nat) {s : State} {rest : List Instr} {Q : State → Prop}
    (hp : PackedRoots s (packedRoot u)) (hl : TableRoots localOffset (localRoot u) s)
    (hr : ∀ i : Fin 8, InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*i.val)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 (16*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧ VMem mid t (fiveSliceMem u s)) → WP isa (.block rest) t Q) :
    WP isa (.block (fiveSliceCode ++ rest)) s Q := by
  have ho : ∀ i : Fin 8, (16*i.val)%16=0 ∧ 16*i.val<65536 := by intro i; omega
  have hsub : ((bankLoads (regs 0) 16).map Prod.fst)⊆packedRegs := by decide +kernel
  simp only [fiveSliceCode,firstLoads_eq,firstStores_eq,List.append_assoc]
  refine loadBank_ok (regs 0) 16 .x0 initial_inj ho hr fun s₁ hc₁ hb₁ => ?_
  have hc₁' := hc₁.mono hsub
  refine five_ok u hb₁ (hp.frame hc₁') (hl.frame hc₁' (by decide)) fun s₂ hc₂ hb₂ => ?_
  refine storeBank_ok (regs 7) 16 .x0 ho hb₂ ?_ fun t hm => ?_
  · intro i
    simpa only [hc₂.gpr,hc₂.wr,hc₁.gpr,hc₁.wr] using hw i
  · have hc : VChg runRegs s s₂ := VChg.mono (hc₁'.trans hc₂) (by
      intro r h
      rcases List.mem_append.mp h with h | h
      · exact (show packedRegs⊆runRegs by decide) h
      · exact h)
    have hm' : VMem s₂ t (fiveSliceMem u s) := by
      simpa only [fiveSliceMem,hc₂.mem,hc₁.mem,hc₂.gpr,hc₁.gpr] using hm
    exact k t ⟨s₂,hc,hm'⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
