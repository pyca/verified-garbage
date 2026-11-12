module

public import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# x86-64: scalar code keeps the `zmm` registers

`VecKeep.lean`'s lemmas with bits 511:256 of `zmm0`–`zmm15` too: scalar code
(`scalCode`) leaves `xmm`, `ymmHi` and `zmmHi` as they are (`WP.zvecKeep`).
-/

@[expose] public section

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
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
    | (simp only [State.store64, State.store8, State.store16, State.store32] at h; split at h <;> [(cases h; exact ⟨rfl, rfl, rfl⟩); cases h])
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
  | icall | icallNext => intro hc; simp only [scalCode, Bool.false_eq_true] at hc
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
  | call hc₁ _ hr ih =>
    intro hc
    obtain ⟨a, b, c⟩ := ih hc
    simp only [isa, call, Option.some.injEq] at hc₁
    subst hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    exact ⟨a, b, c⟩
  | frame => intro hc; simp only [scalCode, Bool.false_eq_true] at hc

/-- Scalar code keeps the vector registers, `zmm` included. -/
theorem WP.zvecKeep {c : Prog isa} (hc : scalCode c = true) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.zmmHi = s.zmmHi :=
  let ⟨t, s', e, q⟩ := h
  ⟨t, s', e, q, exec_zscal e hc⟩

/-! ## `zmm16`–`zmm31`

Scalar code leaves the low halves of `zmm16`–`zmm31` (`ymmH`) as they are too (`WP.hvecKeep`). -/

theorem execAlu32_hvec {op : AluOp} {d : Reg} {src : Src} {s t : State} (h : execAlu32 op d src s = some t) :
    t.ymmH = s.ymmH := by
  unfold execAlu32 at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> first
    | (cases h; rfl)
    | (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl)

theorem execMulx_hvec {hi lo : Reg} {src : Src} {s t : State} (h : execMulx hi lo src s = some t) :
    t.ymmH = s.ymmH := by
  unfold execMulx at h
  split at h
  · cases h
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl

theorem execAdcx_hvec {d : Reg} {src : Src} {s t : State} (h : execAdcx d src s = some t) : t.ymmH = s.ymmH := by
  unfold execAdcx at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl

theorem execAdox_hvec {d : Reg} {src : Src} {s t : State} (h : execAdox d src s = some t) : t.ymmH = s.ymmH := by
  unfold execAdox at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; rfl

theorem execCmov_hvec {cc : Cond} {d : Reg} {src : Src} {s t : State} (h : execCmov cc d src s = some t) :
    t.ymmH = s.ymmH := by
  unfold execCmov at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp h
    cases c <;> rfl

theorem exec_hvec {i : Instr} (hi : scalarI i = true) {s t : State} (h : exec i s = some t) : t.ymmH = s.ymmH := by
  cases i <;> simp only [scalarI, Bool.false_eq_true] at hi
  all_goals simp only [exec, Option.map_eq_some_iff] at h
  all_goals first
    | exact execAlu32_hvec h
    | exact execMulx_hvec h
    | exact execAdcx_hvec h
    | exact execAdox_hvec h
    | exact execCmov_hvec h
    | (obtain ⟨v, -, rfl⟩ := h; rfl)
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (simp only [State.store64, State.store8, State.store16, State.store32] at h; split at h <;> [(cases h; rfl); cases h])
    | (unfold execAlu at h
       simp only [Option.bind_eq_some_iff] at h
       obtain ⟨b, -, h⟩ := h
       split at h <;> (try simp only [Option.map_eq_some_iff] at h) <;> obtain ⟨v, -, rfl⟩ := h <;> rfl)
    | (unfold execShift at h
       split at h
       · split at h <;> (cases h; rfl)
       · cases h)

theorem execBlock_hvec : ∀ {is : List Instr}, is.all scalarI = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.ymmH = s.ymmH
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, hs, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, t₂, h, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      rw [← he'.1]
      exact (execBlock_hvec hs.2 h).trans (exec_hvec hs.1 he)

theorem exec_hscal {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') (hc : scalCode c = true) :
    s'.ymmH = s.ymmH := by
  revert hc
  induction h with
  | icall | icallNext => intro hc; simp only [scalCode, Bool.false_eq_true] at hc
  | block e => exact fun hc => execBlock_hvec hc e
  | seq _ _ ih₁ ih₂ =>
    intro hc
    simp only [scalCode, Bool.and_eq_true] at hc
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  | iteT _ _ ih => intro hc; simp only [scalCode, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => intro hc; simp only [scalCode, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact fun hc => (ih₂ hc).trans (ih₁ hc)
  | call hc₁ _ hr ih =>
    intro hc
    have a := ih hc
    simp only [isa, call, Option.some.injEq] at hc₁
    subst hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    exact a
  | frame => intro hc; simp only [scalCode, Bool.false_eq_true] at hc

/-- Scalar code keeps the low halves of `zmm16`–`zmm31`. -/
theorem WP.hvecKeep {c : Prog isa} (hc : scalCode c = true) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.ymmH = s.ymmH :=
  let ⟨t, s', e, q⟩ := h
  ⟨t, s', e, q, exec_hscal e hc⟩

end VG.X86_64
