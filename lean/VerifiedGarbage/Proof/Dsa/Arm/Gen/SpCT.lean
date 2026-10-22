module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! # DSA parameter generation on ARMv7: blocks that address the stack alone

The entry and the exit save and restore registers and frame words at `sp`
and `r12` = `sp`, which the taint analysis does not follow: such a block
(`SpInstr`) leaks only those addresses, the same in two runs with the same
`sp` and `r12` (`spBlock_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm

/-- An instruction that addresses only `sp` and `r12`, and keeps `r12`. -/
def SpInstr : Instr → Bool
  | .str _ .r12 _ => true
  | .ldrSp t _ => t != .r12
  | .mov t (.imm _) => t != .r12
  | _ => false

/-- Both runs at the same `sp` and `r12`. -/
abbrev SpEq (s t : State) : Prop := s.sp = t.sp ∧ s.gpr .r12 = t.gpr .r12

theorem one_ct {i : Instr} {P Q : State → State → Prop}
    (h : ∀ s t s' t', P s t → exec i s = some s' → exec i t = some t' → addrs i s = addrs i t ∧ Q s' t') :
    RelCT isa P (.block [i]) Q := by
  intro s t tr1 tr2 u v hp e1 e2
  rw [Exec.block_iff] at e1 e2
  simp only [execBlock] at e1 e2
  split at e1
  · cases e1
  · rename_i a ha
    split at e2
    · cases e2
    · rename_i b hb
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, List.append_nil] at e1 e2
      obtain ⟨rfl, rfl⟩ := e1
      obtain ⟨rfl, rfl⟩ := e2
      obtain ⟨e, q⟩ := h s t a b hp ha hb
      exact ⟨by rw [e], q⟩

theorem exec_str_keeps {t n : Reg} {off : Nat} {s s' : State} (h : exec (.str t n off) s = some s') :
    s'.gpr = s.gpr ∧ s'.sp = s.sp := by
  simp only [exec, State.store32] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
    · cases h
  · cases h

theorem SpInstr.cases {i : Instr} (h : SpInstr i = true) :
    (∃ x off, i = .str x .r12 off) ∨ (∃ x off, x ≠ .r12 ∧ i = .ldrSp x off) ∨
      (∃ x v, x ≠ .r12 ∧ i = .mov x (.imm v)) := by
  unfold SpInstr at h
  split at h <;> simp_all

theorem spInstr_ct {i : Instr} (hi : SpInstr i = true) : RelCT isa SpEq (.block [i]) SpEq := by
  refine one_ct fun s t s' t' ⟨hsp, h12⟩ e₁ e₂ => ?_
  rcases SpInstr.cases hi with ⟨x, off, rfl⟩ | ⟨x, off, hx, rfl⟩ | ⟨x, v, hx, rfl⟩
  · obtain ⟨g₁, p₁⟩ := exec_str_keeps e₁
    obtain ⟨g₂, p₂⟩ := exec_str_keeps e₂
    exact ⟨by simp only [addrs, h12], by rw [p₁, p₂, hsp], by rw [g₁, g₂, h12]⟩
  · obtain ⟨-, -, p₁, g₁⟩ := VG.Arm.Taint.exec_dst (d := x) rfl e₁
    obtain ⟨-, -, p₂, g₂⟩ := VG.Arm.Taint.exec_dst (d := x) rfl e₂
    exact ⟨by simp only [addrs, hsp], by rw [p₁, p₂, hsp], by rw [g₁ _ (Ne.symm hx), g₂ _ (Ne.symm hx), h12]⟩
  · obtain ⟨-, -, p₁, g₁⟩ := VG.Arm.Taint.exec_dst (d := x) rfl e₁
    obtain ⟨-, -, p₂, g₂⟩ := VG.Arm.Taint.exec_dst (d := x) rfl e₂
    exact ⟨rfl, by rw [p₁, p₂, hsp], by rw [g₁ _ (Ne.symm hx), g₂ _ (Ne.symm hx), h12]⟩

theorem spBlock_ct : ∀ (l : List Instr), l.all SpInstr = true → RelCT isa SpEq (.block l) SpEq
  | [], _ => RelCT.block_nil fun _ _ h => h
  | i :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact RelCT.block_append (M := isa) (l₁ := [i]) (l₂ := l) ((spInstr_ct h.1).seq (spBlock_ct l h.2))

/-- `add r12, sp, #d` sets `r12` the same in two runs with the same `sp`. -/
theorem addSp_ct (d : Nat) : RelCT isa (fun s t => s.sp = t.sp) (.block [.addSp .r12 d]) SpEq := by
  refine one_ct fun s t s' t' hsp e₁ e₂ => ?_
  simp only [exec] at e₁ e₂
  by_cases hd : d < 256
  · simp only [hd, ite_true, Option.some.injEq] at e₁ e₂; subst e₁ e₂
    exact ⟨rfl, hsp, by simp only [State.setReg, ite_true, hsp]⟩
  · simp only [hd, ite_false, reduceCtorEq] at e₁

end VG.Proof.Dsa.Arm.Gen
