module

public import VerifiedGarbage.Proof.Ed448.Point64Contract
public import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
public import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Ed448.X86_64.FieldVariant
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Fn
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Verified
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Sqr
meta import VerifiedGarbage.Proof.X448.X86_64.Adx.Lit
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.AddSmall
meta import VerifiedGarbage.Proof.Ed448.X86_64.Point64.Lit
meta import VerifiedGarbage.Proof.X448.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! The field backends implement the same point programs and public contracts. -/

@[expose] public section

namespace VG

materialize_code Impl.Ed448.X86_64.Point64.doubleAdxFn
materialize_code Impl.Ed448.X86_64.Point64.addAdxFn

end VG

namespace VG.Proof.Ed448.X86_64.FieldVariant

open VG VG.X86_64 VG.Impl.Ed448 VG.Impl.Ed448.X86_64
open VG.Proof.Ed448 VG.Proof.Ed448.X86_64.Point64
open VG.Impl.Ed448.X86_64.Point64 (saves restores)

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

/-- An instruction after which the SSE registers keeping a value still keep it:
one that writes no vector register (`KeepReg.step`). -/
private def quiet (i : Instr) : Bool := !KeepReg.writesVec i

/-- `restores` brings back each kept register from where `saves` put it, whatever
the code between them did to it. -/
private theorem restores_ok : ∀ r ∈ keptRegs, ∀ b : Bool,
    (restores.foldl (KeepReg.step r) ⟨b, (saves.foldl (KeepReg.step r) ⟨true, .empty⟩).xs⟩).ok =
      true := by
  decide

/-- A function `saves ++ mid ++ restores` keeps the kept registers if `mid` writes no
vector register: only `saves` and `restores` are evaluated for each, not `mid`. -/
private theorem keeps_saved {mid : List Instr}
    (hm : ((instrs (Code.block (saves ++ mid ++ restores) : Prog isa)).drop 5).all quiet = true) :
    ∀ r ∈ keptRegs, KeepReg.keeps r (.block (saves ++ mid ++ restores)) = true := by
  intro r hr
  have hm' : mid.all quiet = true := by
    change ((saves ++ mid ++ restores).drop 5).all quiet = true at hm
    rw [List.append_assoc, List.drop_left' (l₁ := saves) (i := 5) rfl, List.all_append, Bool.and_eq_true] at hm
    exact hm.1
  exact KeepReg.keeps_around hm' (restores_ok r hr)

theorem double_kept (v : Impl.Ed448.X86_64.FieldVariant) :
    ∀ r ∈ keptRegs, KeepReg.keeps r v.doubleFn = true := by
  have h : ((instrs v.doubleFn).drop 5).all quiet = true := by
    cases v <;> dsimp only [Impl.Ed448.X86_64.FieldVariant.doubleFn] <;> lit_decide
  rw [doubleFn_eq] at h ⊢
  exact keeps_saved h

theorem double_mxcsr (v : Impl.Ed448.X86_64.FieldVariant) :
    v.doubleFn.allInstrs (fun i => !loadsMxcsr i) = true := by
  cases v <;> dsimp only [Impl.Ed448.X86_64.FieldVariant.doubleFn] <;> lit_decide

theorem double_verified (v : Impl.Ed448.X86_64.FieldVariant) :
    Verified X86_64.target v.doubleFn (Proof.Ed448.Point64.doubleContract X86_64.abi) := by
  refine Verified.of_correct (k := doubleK) ?_ ?_ doubleK_implies
  · rw [doubleFn_eq]
    exact doubleWith_correct (field_ok v) (by rw [← doubleFn_eq]; exact double_kept v)
      (by rw [← doubleFn_eq]; exact double_mxcsr v)
  · cases v <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp])
      (fun _ _ _ _ hp => fnPub_agree hp) (by taint_decide)

theorem add_kept (v : Impl.Ed448.X86_64.FieldVariant) :
    ∀ r ∈ keptRegs, KeepReg.keeps r v.addFn = true := by
  have h : ((instrs v.addFn).drop 5).all quiet = true := by
    cases v <;> dsimp only [Impl.Ed448.X86_64.FieldVariant.addFn] <;> lit_decide
  rw [addFn_eq] at h ⊢
  exact keeps_saved h

theorem add_mxcsr (v : Impl.Ed448.X86_64.FieldVariant) :
    v.addFn.allInstrs (fun i => !loadsMxcsr i) = true := by
  cases v <;> dsimp only [Impl.Ed448.X86_64.FieldVariant.addFn] <;> lit_decide

theorem add_verified (v : Impl.Ed448.X86_64.FieldVariant) :
    Verified X86_64.target v.addFn (Proof.Ed448.Point64.addAffineContract X86_64.abi) := by
  refine Verified.of_correct (k := addK) ?_ ?_ addK_implies
  · rw [addFn_eq]
    exact addWith_correct (field_ok v) (by rw [← addFn_eq]; exact add_kept v)
      (by rw [← addFn_eq]; exact add_mxcsr v)
  · cases v <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp])
      (fun _ _ _ _ hp => fnPub_agree hp) (by taint_decide)

end VG.Proof.Ed448.X86_64.FieldVariant
