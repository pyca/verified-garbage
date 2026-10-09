import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TailRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NormalizeBank

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def fiveRegs : List VReg := outerRegs ++ tailRegs

def fiveCoreCode : List Instr := (renThree false).code ++ tailCode (renThree false) tailSteps ++
  (renThree false).data.toList.flatMap canon

def fiveValues (v : Vector (BitVec 128) 8) (zi zt : Nat → Nat → Nat → Int) : Vector (BitVec 128) 8 :=
  (tailValues (innerValues v zi outerSteps) zt tailSteps).map positiveVector

/-- The exact five fused inner layers, followed by positive normalization. -/
theorem fiveCore_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} {zi zt : Nat → Nat → Nat → Int}
    (hb : Bank s ({} : Ren).data v) (hi : InnerRoots s zi) (ht : TailRoots s zt)
    (k : ∀ t, VChg fiveRegs s t →
      Bank t (renThree false).data (fiveValues v zi zt) → WP isa (.block rest) t Q) :
    WP isa (.block (fiveCoreCode ++ rest)) s Q := by
  simp only [fiveCoreCode,List.append_assoc]
  refine innerThree_ok hb hi fun s₁ hc₁ _ hb₁ => ?_
  refine tailRun_ok (renThree false) tailSteps tailSteps_valid (renThree_good false)
    hb₁ (ht.keep_of hc₁ (by decide)) fun s₂ hc₂ ht₂ hb₂ => ?_
  have hd : (renThree false).data.toList.Nodup := by rw [renThree_data]; decide
  have ha : ∀ d ∈ (renThree false).data.toList, d ≠ VReg.v4 ∧ d ≠ VReg.v16 := by
    rw [renThree_data]
    decide
  refine normalizeBank_ok (renThree false).data hd ha hb₂ ht₂.q fun s₃ hc₃ hb₃ => k s₃ ?_ hb₃
  have hs : (.v4::(renThree false).data.toList) ⊆ tailRegs := by
    rw [renThree_data]
    decide
  refine VChg.mono ((hc₁.trans hc₂).trans (hc₃.mono hs)) ?_
  intro v hv
  simp only [fiveRegs,List.mem_append] at hv ⊢
  exact hv.elim id Or.inr

end VG.Proof.MlDsa.AArch64.Optimized
