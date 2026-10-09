import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Slice
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def outerSliceCode (input : Reg) : List Instr :=
  (bankLoads ({} : Ren).data 128).map (fun p => Instr.ldrq p.1 input p.2) ++
  (renThree true).code ++
  (bankLoads (renThree true).data 128).map (fun p => Instr.strq p.1 .x2 p.2)

def outerSliceMem (s : State) (input : Reg) (z : Nat → Int) : Mem :=
  writeBank (outerValues (readBank s.mem (s.gpr input) 128) z outerSteps)
    (s.gpr .x2) 128 s.mem

/-- Exact loaded/stored first-stage slice. Both in-place and separate-input
entry points use this theorem; all reads finish before the first write. -/
theorem outerSlice_ok (input : Reg)
    {s : State} {rest : List Instr} {Q : State → Prop} {z : Nat → Int}
    (hconst : Hoisted s z)
    (hr : ∀ i : Fin 8, InRegions (s.rd++s.wr)
      (s.gpr input + BitVec.ofNat 64 (128*i.val)) 16)
    (hw : ∀ i : Fin 8, InRegions s.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128*i.val)) 16)
    (k : ∀ t, (∃ u, VChg outerRegs s u ∧ VMem u t (outerSliceMem s input z)) →
      Hoisted t z → WP isa (.block rest) t Q) :
    WP isa (.block (outerSliceCode input ++ rest)) s Q := by
  have ho : ∀ i : Fin 8, (128*i.val)%16=0 ∧ 128*i.val<65536 := by
    intro i
    omega
  have hsub : ((bankLoads ({} : Ren).data 128).map Prod.fst) ⊆ outerRegs := by decide
  simp only [outerSliceCode, List.append_assoc]
  refine loadBank_ok ({} : Ren).data 128 input initial_good.injective ho hr fun s₁ hc₁ hb₁ => ?_
  have hc₁' := VChg.mono hc₁ hsub
  refine outerThree_ok hb₁ (hconst.keep hc₁') fun s₂ hc₂ ht₂ hb₂ => ?_
  refine storeBank_ok (renThree true).data 128 .x2 ho hb₂ ?_ fun s₃ hm => ?_
  · intro i
    simpa only [hc₂.gpr, hc₂.wr, hc₁.gpr, hc₁.wr] using hw i
  · have hc : VChg outerRegs s s₂ := VChg.mono (hc₁'.trans hc₂) (by
      intro v hv
      simpa only [List.mem_append, or_self] using hv)
    have hm' : VMem s₂ s₃ (outerSliceMem s input z) := by
      simpa only [outerSliceMem, hc₂.mem, hc₁.mem, hc₂.gpr, hc₁.gpr] using hm
    apply k s₃ ⟨s₂,hc,hm'⟩
    exact ⟨ht₂.range, by simpa only [hm.v] using ht₂.q,
      by simpa only [hm.v] using ht₂.roots⟩

end VG.Proof.MlDsa.AArch64.Optimized
