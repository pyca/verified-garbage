module

public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.X86_64.Icall
import VerifiedGarbage.Proof.Framework.Semantics

/-!
# x86-64: the functions at every address never change

No instruction, call, return or frame changes `State.funs`, what the function
at each address does (`fnAt`), and neither does a function called
indirectly, which changes only the registers, flags, MXCSR and memory
(`fn_withArch`); so neither does a run (`Exec.funs`): `WP.mono_funs` lets a
proof use that the state after some code has the same functions as before
it.
-/

@[expose] public section

namespace VG.X86_64

theorem setReg_funs (s : State) (r : Reg) (v : BitVec 64) : (s.setReg r v).funs = s.funs := rfl

theorem exec_funs {i : Instr} {s s' : State} (h : exec i s = some s') : s'.funs = s.funs := by
  cases i with
  | store m r | store32 m r | store8 m r | movdquStore m r | stmxcsr m =>
    simp only [exec, State.store64, State.store32, State.store8, State.store128] at h
    split at h <;> cases h; rfl
  | vmovdquStore len m r =>
    cases len <;> simp only [exec, State.store128, State.store256] at h <;> split at h <;> cases h <;> rfl
  | vmovdqu32Store m r =>
    simp only [exec, State.store512] at h; split at h <;> cases h; rfl
  | mov _ _ | mov32 _ _ | movzx8 _ _ | movdquLoad _ _ | vbroadcasti128 _ _ | vmovdqu32Load _ _
  | vbroadcasti32x4 _ _ | vbroadcasti32x4H _ _ | zbcst _ _ _ _ | vpmadd52Load _ _ _ _ =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | vmovdquLoad len d m | vbinLoad _ len d _ m =>
    cases len <;> simp only [exec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;> rfl
  | alu op d src =>
    simp only [exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | alu32 op d src =>
    simp only [exec, Taint.execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | shift32 op _ n =>
    simp only [exec, execShift32] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl
    · cases h
  | shift op _ n =>
    simp only [exec, execShift] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl
    · cases h
  | rorx32 _ _ _ | rorx _ _ _ =>
    simp only [exec, execRorx32, execRorx] at h
    split at h <;> [(simp only [Option.some.injEq] at h; subst h; rfl); cases h]
  | ldmxcsr m =>
    simp only [exec, Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h
    split at h <;> cases h; rfl
  | xop op => simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.XOp.exec_eq op s]
  | vop op => simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]
  | zop op => simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]
  | eop op => simp only [exec, Option.some.injEq] at h; subst h; rw [Taint.EOp.exec_eq op s]
  | evLoad d m | evMadd52Load _ d _ m =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; cases d <;> rfl
  | evStore m r => simp only [exec, State.store256] at h; split at h <;> cases h; rfl
  | kLoad k d m => simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | kStore m k r => obtain ⟨_, rfl⟩ := State.storeMasked512_eq h; rfl
  | mulx hi lo src =>
    simp only [exec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | adcx d src | adox d src =>
    simp only [exec, execAdcx, execAdox] at h; split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h; obtain ⟨_, _, _, _, rfl⟩ := h; rfl
  | cmov =>
    obtain ⟨_, c, -, -, rfl⟩ := Taint.execCmov_some h; cases c <;> rfl
  | aluTbl op d m n ws =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    simp only [Taint.execAluW_eq, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h; split <;> rfl
  | vmovdquTbl d m n ws => simp only [exec] at h; split at h <;> cases h; rfl
  | push | pop | alloc | free => simp only [exec, reduceCtorEq] at h
  | _ => simp only [exec, Option.some.injEq] at h; subst h; rfl

theorem pushRegs_funs (t : State) (rs : List Reg) : (pushRegs t rs).funs = t.funs := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih => exact (ih _).trans rfl

theorem push_funs {i : Instr} {s s' : State} (h : push i s = some s') : s'.funs = s.funs := by
  cases i <;> simp only [push, reduceCtorEq] at h <;> split at h <;> cases h <;>
    first | rfl | exact pushRegs_funs _ _

theorem pop_funs {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') : s'.funs = s₂.funs := by
  have hp : ∀ (k : Nat) (r : Reg) (t : State), (popReg t r k).funs = t.funs := by
    intro k; induction k with
    | zero => intro r t; rfl
    | succ k ih => intro r t; exact (ih _ _).trans rfl
  cases j <;> simp only [pop, reduceCtorEq] at h <;> split at h <;> cases h <;>
    first | rfl | exact hp _ _ _

theorem execBlock_funs : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.funs = s.funs
  | [], _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, s, s', t, h => by
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h₂, e₂⟩ := Option.map_eq_some_iff.mp h
      cases e₂
      exact (execBlock_funs h₂).trans (exec_funs e)

theorem Exec.funs {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.funs = s.funs := by
  induction h with
  | block e => exact execBlock_funs e
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | iteT _ _ ih | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | call e₁ _ e₂ ih =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih
  | icall hf e₁ e₃ _ e₂ =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁
    obtain ⟨r, rfl⟩ := fn_withArch hf e₃
    rfl
  | frame e₁ _ e₂ ih => exact (pop_funs e₂).trans (ih.trans (push_funs e₁))

/-- The state after `c` has the same functions as before it. -/
theorem WP.mono_funs {c : Prog isa} {s : State} {Q R : State → Prop} (h : WP isa c s Q)
    (k : ∀ s', Q s' → s'.funs = s.funs → R s') : WP isa c s R := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, k s' hq (Exec.funs he)⟩

/-- `Q` of the state after `c`, which may assume it has the same functions
as before. -/
theorem WP.of_funs {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s fun s' => s'.funs = s.funs → Q s') : WP isa c s Q :=
  WP.mono_funs h fun _ hq sy => hq sy

end VG.X86_64
