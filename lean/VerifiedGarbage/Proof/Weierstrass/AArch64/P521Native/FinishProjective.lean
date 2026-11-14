module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAddCode
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

/-! Jacobian-to-projective arithmetic before the final complete addition. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native VG.Impl.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field

def finishProjectiveOps : List PointOp := [
 .mul 1288 1072 1216 false,.mul 1720 1216 1216 false,
 .mul 1432 1720 1216 false,.add 1360 1144 280]

theorem finish_projective_source149 : outerBlock149.drop 54=normalizeCallArgs 1288 1072 1216 := by lit_decide

theorem finish_projective_source150 : outerBlock150=buildRestore++normalizeCallArgs 1720 1216 1216 := by lit_decide

theorem finish_projective_source151 : outerBlock151=buildRestore++normalizeCallArgs 1432 1720 1216 := by lit_decide

theorem finish_projective_source152 : outerBlock152.take 53=buildRestore++P521Linear.add 1360 1144 280 := by lit_decide

def finishProjectiveMachine : Prog isa := sequence [
 .block (outerBlock149.drop 54),callNormalMul,.block outerBlock150,callNormalSqr,
 .block outerBlock151,callNormalMul,.block (outerBlock152.take 53)]

private theorem projective_wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem finish_projective_machine_wp {s : State} {Q : State → Prop} :
    WP isa finishProjectiveMachine s Q ↔ WP isa (fieldProgram id finishProjectiveOps) s Q := by
  simp only [finishProjectiveMachine,sequence,List.foldr_cons,List.foldr_nil,
    finishProjectiveOps,fieldProgram,fieldCode,id,Nat.reduceEqDiff,ite_false,ite_true,
    normalizeMulStep,normalizeSquareStep,finish_projective_source149,finish_projective_source150,
    finish_projective_source151,finish_projective_source152]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply projective_wp_post_iff; intro t)

theorem finish_projective_value {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) (zero : E 280=0) :
    (pointRun finishProjectiveOps E 1288,pointRun finishProjectiveOps E 1360,pointRun finishProjectiveOps E 1432)=
      (E 1072*E 1216,E 1144,E 1216*E 1216*E 1216) := by
  simp only [pointRun,finishProjectiveOps,List.foldl,PointOp.run,Function.update_apply,ite_true]
  grind

end VG.Proof.Weierstrass.AArch64.P521Native
