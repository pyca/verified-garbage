module

public import VerifiedGarbage.TCB.X86_64.Isa
public import VerifiedGarbage.Impl.X86_64Scal
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# x86-64: code that does not touch the vector registers

`scalCode` (`Impl/X86_64Scal.lean`) holds of code whose every instruction is one of a few scalar ones
(moves, loads and stores of general-purpose registers, their arithmetic, `bswap`,
`lea` of a static, `mul`, `imul`, `mulx`, `adcx`, `adox`, `cmov`, 32-bit arithmetic,
stores and `bswap`):
such code leaves `xmm` and `ymmHi` as they are (`WP.vecKeep`), which a proof
about it need not state.
-/

@[expose] public section

namespace VG.X86_64

theorem execAlu32_vec {op : AluOp} {d : Reg} {src : Src} {s t : State} (h : execAlu32 op d src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.zmmHi = s.zmmHi := by
  unfold execAlu32 at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> first
    | (cases h; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl, rfl⟩)

theorem execMulx_vec {hi lo : Reg} {src : Src} {s t : State} (h : execMulx hi lo src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.zmmHi = s.zmmHi := by
  unfold execMulx at h
  split at h
  · cases h
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl, rfl⟩

theorem execAdcx_vec {d : Reg} {src : Src} {s t : State} (h : execAdcx d src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.zmmHi = s.zmmHi := by
  unfold execAdcx at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl, rfl⟩

theorem execAdox_vec {d : Reg} {src : Src} {s t : State} (h : execAdox d src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.zmmHi = s.zmmHi := by
  unfold execAdox at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl, rfl⟩

theorem execCmov_vec {cc : Cond} {d : Reg} {src : Src} {s t : State} (h : execCmov cc d src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.zmmHi = s.zmmHi := by
  unfold execCmov at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp h
    cases c <;> exact ⟨rfl, rfl, rfl⟩

theorem exec_vec {i : Instr} (hi : scalarI i = true) {s t : State} (h : exec i s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  cases i <;> simp only [scalarI, Bool.false_eq_true] at hi
  all_goals simp only [reduceExec, Option.map_eq_some_iff] at h
  all_goals first
    | exact ⟨(execAlu32_vec h).1, (execAlu32_vec h).2.1⟩
    | exact ⟨(execMulx_vec h).1, (execMulx_vec h).2.1⟩
    | exact ⟨(execAdcx_vec h).1, (execAdcx_vec h).2.1⟩
    | exact ⟨(execAdox_vec h).1, (execAdox_vec h).2.1⟩
    | exact ⟨(execCmov_vec h).1, (execCmov_vec h).2.1⟩
    | (obtain ⟨v, -, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (simp only [State.store64, State.store8, State.store16, State.store32] at h; split at h <;> [(cases h; exact ⟨rfl, rfl⟩); cases h])
    | (unfold execAlu at h
       simp only [Option.bind_eq_some_iff] at h
       obtain ⟨b, -, h⟩ := h
       split at h <;> (try simp only [Option.map_eq_some_iff] at h) <;> obtain ⟨v, -, rfl⟩ := h <;>
         exact ⟨rfl, rfl⟩)
    | (unfold execShift at h
       split at h
       · split at h <;> (cases h; exact ⟨rfl, rfl⟩)
       · cases h)

theorem execBlock_vec : ∀ {is : List Instr}, is.all scalarI = true → ∀ {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]; exact ⟨rfl, rfl⟩
  | i :: is, hs, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, t₂, h, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      obtain ⟨x, y⟩ := exec_vec hs.1 he
      obtain ⟨x', y'⟩ := execBlock_vec hs.2 h
      rw [← he'.1]
      exact ⟨x'.trans x, y'.trans y⟩

theorem exec_scal {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') (hc : scalCode c = true) :
    s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  revert hc
  induction h with
  | icall | icallNext => intro hc; simp only [scalCode, Bool.false_eq_true] at hc
  | block e => exact fun hc => execBlock_vec hc e
  | seq _ _ ih₁ ih₂ =>
    intro hc
    simp only [scalCode, Bool.and_eq_true] at hc
    obtain ⟨a, b⟩ := ih₁ hc.1; obtain ⟨a', b'⟩ := ih₂ hc.2
    exact ⟨a'.trans a, b'.trans b⟩
  | iteT _ _ ih => intro hc; simp only [scalCode, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => intro hc; simp only [scalCode, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ =>
    intro hc
    obtain ⟨a, b⟩ := ih₁ hc; obtain ⟨a', b'⟩ := ih₂ hc
    exact ⟨a'.trans a, b'.trans b⟩
  | call hc₁ _ hr ih =>
    intro hc
    obtain ⟨a, b⟩ := ih hc
    simp only [isa, call, Option.some.injEq] at hc₁
    subst hc₁
    simp only [isa, ret] at hr
    split at hr <;> cases hr
    exact ⟨a, b⟩
  | frame => intro hc; simp only [scalCode, Bool.false_eq_true] at hc

/-- Scalar code keeps the vector registers. -/
theorem WP.vecKeep {c : Prog isa} (hc : scalCode c = true) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi :=
  let ⟨t, s', e, q⟩ := h
  ⟨t, s', e, q, exec_scal e hc⟩

end VG.X86_64
