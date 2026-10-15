module

public import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Fn
public import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The point functions keep `rbp` and `r12`–`r15`

Untrusted: everything here is checked by Lean. Each function saves the
registers in `xmm0`–`xmm4`, runs field code that writes no vector register,
and restores them (`fn`), so it keeps them (`fn_keeps`): one pass over the
code, where `KeepReg.keeps` evaluated on the code would take one for each
register.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64

variable {fld : Arith} [EdArith fld]

/-- The code between a function's saves and restores (`fn`'s five each). -/
def midCode : Prog isa → List Instr
  | .block l => (l.drop 5).take (l.length - 10)
  | _ => []

theorem midCode_fn (fld : Arith) (ops : List FieldOp) : midCode (fn fld ops) = fieldCode fld ops := by
  simp [midCode, fn, saves, restores, kept]

/-- An instruction that writes no vector register keeps what is known of the SSE registers. -/
theorem step_xs {r : Reg} {i : Instr} (h : KeepReg.writesVec i = false) (a : KeepReg.Abs) :
    (KeepReg.step r a i).xs = a.xs := by
  unfold KeepReg.step
  split
  · simp [KeepReg.writesVec] at h
  · cases _ == r <;> rfl
  · simp only [h, Bool.cond_false]

theorem foldl_xs {r : Reg} : ∀ {is : List Instr}, is.all (fun i => !KeepReg.writesVec i) = true →
    ∀ a : KeepReg.Abs, (is.foldl (KeepReg.step r) a).xs = a.xs
  | [], _, _ => rfl
  | i :: is, h, a => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [List.foldl_cons, foldl_xs (by simpa only [Bool.not_eq_true'] using h.2), step_xs h.1]

/-- A function keeps `rbp` and `r12`–`r15` if its field code writes no vector register: one
pass over the code, where `KeepReg.keeps` would take one for each register. -/
theorem fn_keeps {fld : Arith} {ops : List FieldOp}
    (h : (midCode (fn fld ops)).all (fun i => !KeepReg.writesVec i) = true) :
    ∀ r ∈ keptRegs, KeepReg.keeps r (fn fld ops) = true := by
  rw [midCode_fn] at h
  intro r hr
  simp only [KeepReg.keeps, fn, KeepReg.check]
  rw [KeepReg.run_eq r _ ⟨true, .empty⟩, List.foldl_append, List.foldl_append]
  have hx := foldl_xs (r := r) h (saves.foldl (KeepReg.step r) ⟨true, .empty⟩)
  generalize (fieldCode fld ops).foldl (KeepReg.step r) _ = a at hx ⊢
  obtain ⟨ok, xs⟩ := a
  simp only at hx; subst hx
  simp only [keptRegs, kept, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> cases ok <;> decide

/-- The functions' bodies keep `rbp` and `r12`–`r15`. -/
theorem doubleFn_keeps (t : Bool) : ∀ r ∈ keptRegs, KeepReg.keeps r (doubleFn fld t) = true := by
  rcases EdArith.known (fld := fld) with rfl | rfl <;> cases t <;>
    exact fn_keeps (by lit_decide)

theorem addFn_keeps (t : Bool) : ∀ r ∈ keptRegs, KeepReg.keeps r (addFn fld t) = true := by
  rcases EdArith.known (fld := fld) with rfl | rfl <;> cases t <;>
    exact fn_keeps (by lit_decide)

theorem addAffineFn_keeps : ∀ r ∈ keptRegs, KeepReg.keeps r (addAffineFn fld) = true := by
  rcases EdArith.known (fld := fld) with rfl | rfl <;>
    exact fn_keeps (by lit_decide)

end VG.Proof.Ed25519.X86_64.Point64
