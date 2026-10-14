module

public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! The field backends implement the same point programs and public contracts. -/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86_64.Point64.doubleAdxFn
materialize_code Impl.Ed448.X86_64.Point64.addAdxFn

end VG

namespace VG.Proof.Ed448.X86_64.FieldVariant

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64.Point64

theorem field_ok (v : Impl.Ed448.X86_64.FieldVariant) : Proof.X448.X86_64.FieldOk v.field := by
  cases v
  · exact Proof.X448.X86_64.baseline_ok
  · exact Proof.X448.X86_64.adx_ok

theorem doubleFn_eq (v : Impl.Ed448.X86_64.FieldVariant) :
    v.doubleFn = Point64.doubleFnWith v.field := by cases v <;> rfl

theorem addFn_eq (v : Impl.Ed448.X86_64.FieldVariant) :
    v.addFn = Point64.addFnWith v.field := by cases v <;> rfl

theorem bodies_ok (v : Impl.Ed448.X86_64.FieldVariant) : Point64.PointOk v.bodies where
  dbl hs := by
    change WP isa v.doubleFn _ _
    rw [doubleFn_eq]
    exact WP.mono (fnWith_ok (field_ok v) doubleOps doubleOps_valid hs) (fun _ ⟨k, e, _⟩ => ⟨k, e⟩)
  add hs hd := by
    change WP isa v.addFn _ _
    rw [addFn_eq]
    exact WP.mono (addFnWith_ok (field_ok v) hs hd) (fun _ ⟨k, e, _⟩ => ⟨k, e⟩)

theorem double_kept (v : Impl.Ed448.X86_64.FieldVariant) :
    ∀ r ∈ keptRegs, KeepReg.keeps r v.doubleFn = true := by
  cases v <;> dsimp only [Impl.Ed448.X86_64.FieldVariant.doubleFn] <;> intro r hr <;>
    simp only [keptRegs, Point64.kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide

theorem double_mxcsr (v : Impl.Ed448.X86_64.FieldVariant) :
    v.doubleFn.allInstrs (fun i => !loadsMxcsr i) = true := by
  cases v <;> dsimp only [Impl.Ed448.X86_64.FieldVariant.doubleFn] <;> lit_decide

theorem double_verified (v : Impl.Ed448.X86_64.FieldVariant) :
    Verified X86_64.target v.doubleFn (Spec.Ed448.Point64.doubleContract X86_64.abi) := by
  refine Verified.of_correct (k := doubleK) ?_ ?_ doubleK_implies
  · rw [doubleFn_eq]
    exact doubleWith_correct (field_ok v) (by rw [← doubleFn_eq]; exact double_kept v)
      (by rw [← doubleFn_eq]; exact double_mxcsr v)
  · cases v <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp])
      (fun _ _ _ _ hp => fnPub_agree hp) (by taint_decide)

private theorem addAdx_keeps_rbp : KeepReg.keeps .rbp Point64.addAdxFn = true := by lit_decide

private theorem addAdx_keeps_r12 : KeepReg.keeps .r12 Point64.addAdxFn = true := by lit_decide

private theorem addAdx_keeps_r13 : KeepReg.keeps .r13 Point64.addAdxFn = true := by lit_decide

private theorem addAdx_keeps_r14 : KeepReg.keeps .r14 Point64.addAdxFn = true := by lit_decide

private theorem addAdx_keeps_r15 : KeepReg.keeps .r15 Point64.addAdxFn = true := by lit_decide

theorem add_kept (v : Impl.Ed448.X86_64.FieldVariant) :
    ∀ r ∈ keptRegs, KeepReg.keeps r v.addFn = true := by
  cases v with
  | scalar =>
    intro r hr
    simp only [keptRegs, Point64.kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> lit_decide
  | adx =>
    intro r hr
    simp only [keptRegs, Point64.kept, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact addAdx_keeps_rbp
    · exact addAdx_keeps_r12
    · exact addAdx_keeps_r13
    · exact addAdx_keeps_r14
    · exact addAdx_keeps_r15

theorem add_mxcsr (v : Impl.Ed448.X86_64.FieldVariant) :
    v.addFn.allInstrs (fun i => !loadsMxcsr i) = true := by
  cases v <;> dsimp only [Impl.Ed448.X86_64.FieldVariant.addFn] <;> lit_decide

theorem add_verified (v : Impl.Ed448.X86_64.FieldVariant) :
    Verified X86_64.target v.addFn (Spec.Ed448.Point64.addAffineContract X86_64.abi) := by
  refine Verified.of_correct (k := addK) ?_ ?_ addK_implies
  · rw [addFn_eq]
    exact addWith_correct (field_ok v) (by rw [← addFn_eq]; exact add_kept v)
      (by rw [← addFn_eq]; exact add_mxcsr v)
  · cases v <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp])
      (fun _ _ _ _ hp => fnPub_agree hp) (by taint_decide)

end VG.Proof.Ed448.X86_64.FieldVariant
