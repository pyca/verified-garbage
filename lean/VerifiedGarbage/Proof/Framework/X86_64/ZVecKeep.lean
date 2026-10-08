import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# x86-64: scalar code keeps the `zmm` registers

`VecKeep.lean`'s lemmas with bits 511:256 of `zmm0`–`zmm15` too: scalar code
(`scalCode`) leaves `xmm`, `ymmHi` and `zmmHi` as they are (`WP.zvecKeep`).
-/

namespace VG.X86_64

theorem exec_zvec {i : Instr} (hi : scalarI i = true) {s t : State} (h : exec i s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.zmmHi = s.zmmHi := by
  cases i <;> simp only [scalarI, Bool.false_eq_true] at hi
  all_goals simp only [exec, Option.map_eq_some_iff] at h
  all_goals first
    | exact execAlu32_vec h
    | exact execMulx_vec h
    | exact execAdcx_vec h
    | exact execAdox_vec h
    | exact execCmov_vec h
    | (obtain ⟨v, -, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩)
    | (simp only [State.store64, State.store8] at h; split at h <;> [(cases h; exact ⟨rfl, rfl, rfl⟩); cases h])
    | (unfold execAlu at h
       simp only [Option.bind_eq_some_iff] at h
       obtain ⟨b, -, h⟩ := h
       split at h <;> (try simp only [Option.map_eq_some_iff] at h) <;> obtain ⟨v, -, rfl⟩ := h <;>
         exact ⟨rfl, rfl, rfl⟩)
    | (unfold execShift at h
       split at h
       · split at h <;> (cases h; exact ⟨rfl, rfl, rfl⟩)
       · cases h)

theorem execBlock_zvec : ∀ {is : List Instr}, is.all scalarI = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]; exact ⟨rfl, rfl, rfl⟩
  | i :: is, hs, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, t₂, h, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      obtain ⟨x, y, z⟩ := exec_zvec hs.1 he
      obtain ⟨x', y', z'⟩ := execBlock_zvec hs.2 h
      rw [← he'.1]
      exact ⟨x'.trans x, y'.trans y, z'.trans z⟩

theorem exec_zscal {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') (hc : scalCode c = true) :
    s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi := by
  revert hc
  induction h with
  | block e => exact fun hc => execBlock_zvec hc e
  | seq _ _ ih₁ ih₂ =>
    intro hc
    simp only [scalCode, Bool.and_eq_true] at hc
    obtain ⟨a, b, c⟩ := ih₁ hc.1; obtain ⟨a', b', c'⟩ := ih₂ hc.2
    exact ⟨a'.trans a, b'.trans b, c'.trans c⟩
  | iteT _ _ ih => intro hc; simp only [scalCode, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => intro hc; simp only [scalCode, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ =>
    intro hc
    obtain ⟨a, b, c⟩ := ih₁ hc; obtain ⟨a', b', c'⟩ := ih₂ hc
    exact ⟨a'.trans a, b'.trans b, c'.trans c⟩
  | call => intro hc; simp only [scalCode, Bool.false_eq_true] at hc
  | frame => intro hc; simp only [scalCode, Bool.false_eq_true] at hc

/-- Scalar code keeps the vector registers, `zmm` included. -/
theorem WP.zvecKeep {c : Prog isa} (hc : scalCode c = true) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.zmmHi = s.zmmHi :=
  let ⟨t, s', e, q⟩ := h
  ⟨t, s', e, q, exec_zscal e hc⟩

end VG.X86_64
