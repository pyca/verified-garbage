module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivArgsCT
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Stack-only call preparation has no secret-dependent memory addresses -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm

def StackBaseEq (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .r12 = t.gpr .r12

theorem stackBaseBlock_ct (code : List Instr)
    (keep : ∀ i ∈ code, dstOf i ≠ some .r12)
    (leak : ∀ i ∈ code, ∀ s t : State, StackBaseEq s t → addrs i s = addrs i t) :
    RelCT isa StackBaseEq (.block code) StackBaseEq := by
  induction code with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons i rest ih =>
    have first : RelCT isa StackBaseEq (.block [i]) StackBaseEq := by
      apply single_ct (fun s t h => leak i (by simp) s t h)
      intro s t u v h e1 e2
      exact ⟨(exec_sp e1).trans (h.1.trans (exec_sp e2).symm),
        (exec_gpr (keep i (by simp)) e1).trans (h.2.trans (exec_gpr (keep i (by simp)) e2).symm)⟩
    exact RelCT.block_append (first.seq (ih (fun j hj => keep j (by simp [hj]))
      (fun j hj => leak j (by simp [hj]))))

theorem stackBaseStart_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block [.addSp .r12 0]) StackBaseEq := by
  apply single_ct (fun _ _ _ => rfl)
  intro s t u v h e1 e2
  simp only [exec, Nat.reduceLT, ite_true, BitVec.add_zero, Option.some.injEq] at e1 e2
  subst u; subst v
  exact ⟨h, by simpa only [State.setReg, ite_true] using h⟩

theorem setupBlock_ct (code : List Instr)
    (keep : ∀ i ∈ code, dstOf i ≠ some .r12)
    (leak : ∀ i ∈ code, ∀ s t : State, StackBaseEq s t → addrs i s = addrs i t) :
    RelCT isa (fun s t => s.sp = t.sp) (.block (.addSp .r12 0 :: code)) (fun s t => s.sp = t.sp) := by
  exact (RelCT.block_append (stackBaseStart_ct.seq (stackBaseBlock_ct code keep leak))).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

def stackInstruction : Instr → Bool
  | .str _ n _ => decide (n = .r12)
  | .ldrSp _ _ | .dp _ _ _ _ | .mov _ _ | .addSp _ _ => true
  | _ => false

theorem stackInstruction_leak {i : Instr} (hi : stackInstruction i = true) {s t : State} (h : StackBaseEq s t) :
    addrs i s = addrs i t := by
  cases i <;> simp_all [stackInstruction, addrs, StackBaseEq]

theorem setupChecked_ct (code : List Instr)
    (keep : code.all (fun i => decide (dstOf i ≠ some .r12)) = true)
    (leak : code.all stackInstruction = true) :
    RelCT isa (fun s t => s.sp = t.sp) (.block (.addSp .r12 0 :: code)) (fun s t => s.sp = t.sp) := by
  apply setupBlock_ct
  · intro i hi
    exact of_decide_eq_true (List.all_eq_true.mp keep i hi)
  · intro i hi s t h
    exact stackInstruction_leak (List.all_eq_true.mp leak i hi) h

theorem crtArgs_ct : RelCT isa (fun s t => s.sp = t.sp) (.block crtArgs) (fun s t => s.sp = t.sp) :=
  setupChecked_ct _ (by decide) (by decide)

theorem pcArgs_ct : RelCT isa (fun s t => s.sp = t.sp) (.block pcArgs) (fun s t => s.sp = t.sp) :=
  setupChecked_ct _ (by decide) (by decide)

theorem pdArgs_ct : RelCT isa (fun s t => s.sp = t.sp) (.block pdArgs) (fun s t => s.sp = t.sp) :=
  setupChecked_ct _ (by decide) (by decide)
end VG.Proof.Rsa.Arm
