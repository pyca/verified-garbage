module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FinishAddCode

/-! Final ordinary-field products retain all calls of the selected prototype. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native
open VG.Proof.Mont.AArch64.P521Field

def finishProductsOps : List PointOp := [.mul 2512 1072 2152 false,.mul 2584 2512 352 false]

theorem finish_products_source169 : outerBlock169=normalizeCallArgs 2512 1072 2152 := by lit_decide

theorem finish_products_source170 : outerBlock170=buildRestore++normalizeCallArgs 2584 2512 352 := by lit_decide

def finishProductsMachine : Prog isa := sequence [
  .block outerBlock169,callNormalMul,.block outerBlock170,callNormalMul,.block buildRestore]

private theorem products_wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem finish_products_machine_wp {s : State} {Q : State → Prop} :
    WP isa finishProductsMachine s Q ↔ WP isa (fieldProgram id finishProductsOps) s Q := by
  simp only [finishProductsMachine,sequence,List.foldr_cons,List.foldr_nil,
    finishProductsOps,fieldProgram,fieldCode,id,Nat.reduceEqDiff,ite_false,
    normalizeMulStep,finish_products_source169,finish_products_source170]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply products_wp_post_iff; intro t)

theorem finish_products_value {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) :
    pointRun finishProductsOps E 2584=E 1072*E 2152*E 352 := by
  simp only [pointRun,finishProductsOps,List.foldl,PointOp.run,Function.update_apply,ite_true]
  rfl

theorem finish_products_machine_ok {base : Addr} {s : State}
    {E : Nat → Fin VG.Proof.Mont.AArch64.P521Square.fieldPrime}
    (hs : VG.Proof.Mont.AArch64.Scr s base 8192)
    (inv : OrdinaryInv base VG.Proof.Mont.AArch64.P521Square.fieldPrime id
      [1072,2152,352] E (fun _ => 1) s) :
    WP isa finishProductsMachine s fun t =>
      OrdinaryInv base VG.Proof.Mont.AArch64.P521Square.fieldPrime id
        (fieldLive finishProductsOps [1072,2152,352]) (pointRun finishProductsOps E) (fun _ => 1) t ∧
      VG.Proof.Mont.AArch64.Scr t base 8192 ∧ FieldPublic s t ∧
      FieldProgramFrame base id finishProductsOps s.mem t.mem := by
  apply finish_products_machine_wp.mpr
  exact field_program_ok (by decide) (by decide) build_field_layout finishProductsOps hs inv
    (by simp [buildSlot])
    (by simp [finishProductsOps,PointOp.out,PointOp.ins,buildSlot])
    (by decide) (by simp [finishProductsOps,fieldCoeffs])

end VG.Proof.Weierstrass.AArch64.P521Native
