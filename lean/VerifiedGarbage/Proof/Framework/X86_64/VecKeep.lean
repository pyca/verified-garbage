import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# x86-64: code that does not touch the vector registers

`scalCode` holds of code whose every instruction is one of a few scalar ones
(moves, loads and stores of general-purpose registers, their arithmetic,
`lea` of a static, `mul`, `mulx`, `adcx`, `adox`, `cmov`, 32-bit arithmetic):
such code leaves `xmm` and `ymmHi` as they are (`WP.vecKeep`), which a proof
about it need not state.
-/

namespace VG.X86_64

/-- The instructions that read and write only general-purpose registers, flags and memory. -/
def scalarI : Instr → Bool
  | .mov .. | .store .. | .alu .. | .mov32 .. | .movzx8 .. | .movImm64 .. | .leaSym .. | .mul ..
  | .store8 .. | .shift .. | .mulx .. | .adcx .. | .adox .. | .cmov .. | .alu32 .. => true
  | _ => false

theorem execAlu32_vec {op : AluOp} {d : Reg} {src : Src} {s t : State} (h : execAlu32 op d src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  unfold execAlu32 at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  split at h <;> first
    | (cases h; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl⟩)

theorem execMulx_vec {hi lo : Reg} {src : Src} {s t : State} (h : execMulx hi lo src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  unfold execMulx at h
  split at h
  · cases h
  · obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl⟩

theorem execAdcx_vec {d : Reg} {src : Src} {s t : State} (h : execAdcx d src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  unfold execAdcx at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl⟩

theorem execAdox_vec {d : Reg} {src : Src} {s t : State} (h : execAdox d src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  unfold execAdox at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.mp h; exact ⟨rfl, rfl⟩

theorem execCmov_vec {cc : Cond} {d : Reg} {src : Src} {s t : State} (h : execCmov cc d src s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  unfold execCmov at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp h
    cases c <;> exact ⟨rfl, rfl⟩

theorem exec_vec {i : Instr} (hi : scalarI i = true) {s t : State} (h : exec i s = some t) :
    t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi := by
  cases i <;> simp only [scalarI, Bool.false_eq_true] at hi
  all_goals simp only [exec, Option.map_eq_some_iff] at h
  all_goals first
    | exact execAlu32_vec h
    | exact execMulx_vec h
    | exact execAdcx_vec h
    | exact execAdox_vec h
    | exact execCmov_vec h
    | (obtain ⟨v, -, rfl⟩ := h; exact ⟨rfl, rfl⟩)
    | (simp only [State.store64, State.store8] at h; split at h <;> [(cases h; exact ⟨rfl, rfl⟩); cases h])
    | (unfold execAlu at h
       simp only [Option.bind_eq_some_iff] at h
       obtain ⟨b, -, h⟩ := h
       split at h <;> (try simp only [Option.map_eq_some_iff] at h) <;> obtain ⟨v, -, rfl⟩ := h <;>
         exact ⟨rfl, rfl⟩)
    | (unfold execShift at h
       split at h
       · split at h <;> (cases h; exact ⟨rfl, rfl⟩)
       · cases h)

/-- Whether every instruction of `c` is in `scalarI`, with no calls or frames. -/
def scalCode : Prog isa → Bool
  | .block is => is.all scalarI
  | .seq a b => scalCode a && scalCode b
  | .ite _ a b => scalCode a && scalCode b
  | .loop b _ => scalCode b
  | _ => false

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
  | call => intro hc; simp only [scalCode, Bool.false_eq_true] at hc
  | frame => intro hc; simp only [scalCode, Bool.false_eq_true] at hc

/-- Scalar code keeps the vector registers. -/
theorem WP.vecKeep {c : Prog isa} (hc : scalCode c = true) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi :=
  let ⟨t, s', e, q⟩ := h
  ⟨t, s', e, q, exec_scal e hc⟩

end VG.X86_64
