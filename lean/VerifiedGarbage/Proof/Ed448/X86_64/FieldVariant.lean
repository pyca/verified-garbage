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

private theorem step_quiet (r : Reg) (a : KeepReg.Abs) (i : Instr) (h : quiet i = true) :
    (KeepReg.step r a i).xs = a.xs := by
  have hv : KeepReg.writesVec i = false := by simpa only [quiet, Bool.not_eq_true'] using h
  cases i <;> first
    | (simp only [KeepReg.step, hv, Bool.cond_false]; done)
    | (rename_i d x; show (bif d == r then _ else a).xs = a.xs; cases d == r <;> rfl)
    | (simp only [KeepReg.writesVec, Bool.true_eq_false] at hv)

private theorem foldl_quiet (r : Reg) : ∀ (is : List Instr) (a : KeepReg.Abs), is.all quiet = true →
    (is.foldl (KeepReg.step r) a).xs = a.xs
  | [], _, _ => rfl
  | i :: is, a, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.foldl_cons, foldl_quiet r is _ h.2, step_quiet r a i h.1]

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
  change (KeepReg.run r (saves ++ mid ++ restores) (⟨true, .empty⟩ : KeepReg.Abs).ok
    (⟨true, .empty⟩ : KeepReg.Abs).xs.bits).ok = true
  rw [KeepReg.run_eq, List.foldl_append, List.foldl_append]
  have hx := foldl_quiet r mid (saves.foldl (KeepReg.step r) ⟨true, .empty⟩) hm'
  generalize mid.foldl (KeepReg.step r) (saves.foldl (KeepReg.step r) ⟨true, .empty⟩) = a at hx
  obtain ⟨b, xs⟩ := a
  subst hx
  exact restores_ok r hr b

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
    Verified X86_64.target v.doubleFn (Spec.Ed448.Point64.doubleContract X86_64.abi) := by
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
    Verified X86_64.target v.addFn (Spec.Ed448.Point64.addAffineContract X86_64.abi) := by
  refine Verified.of_correct (k := addK) ?_ ?_ addK_implies
  · rw [addFn_eq]
    exact addWith_correct (field_ok v) (by rw [← addFn_eq]; exact add_kept v)
      (by rw [← addFn_eq]; exact add_mxcsr v)
  · cases v <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp])
      (fun _ _ _ _ hp => fnPub_agree hp) (by taint_decide)

end VG.Proof.Ed448.X86_64.FieldVariant
