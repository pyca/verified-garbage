import VerifiedGarbage.Proof.Framework.Spectre
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# Speculative semantics of x86-64 instructions (prototype)

**Prototype; `widen` and `spectre` would be trusted.** Transiently, a
memory access is not checked against the permitted regions: the hardware
performs a load from any mapped address before the bounds check that guards
it resolves (Spectre v1, "bounds check bypass"). So an instruction runs as
in the sequential model from the same state with every address readable.
Memory is total in the model, so the value loaded is whatever memory holds
there (in the attacker's experiment, possibly secret).

A transient store is not checked either (Spectre v1.1, "bounds check bypass
store"): its bytes go to the store buffer whatever the address, and later
transient loads of those addresses see them (store-to-load forwarding), so
it writes memory (`tstore`).

`lfence` is the speculation barrier: "LFENCE does not execute until all
prior instructions have completed locally, and no later instruction begins
execution until LFENCE completes" (SDM Vol. 2, "LFENCE"), so nothing after
it executes transiently; Intel recommends it against bounds check bypass
("Speculative Execution Side Channel Mitigations", rev. 3.0, §2.1). On AMD
processors it is dispatch-serializing only with `MSR C001_1029[1]` set
(AMD, "Software Techniques for Managing Speculation on AMD Processors"),
the default on Family 17h and later.
-/

namespace VG.X86_64.Spectre

/-- Two regions that together contain every access of at most `2⁶³` bytes. -/
def allMem : List Region := [⟨0, 2 ^ 64⟩, ⟨2 ^ 63, 2 ^ 64⟩]

/-- The state with every address readable. -/
def widen (s : State) : State := { s with rd := allMem }

/-- A store as it executes transiently: the store of `exec`, at any address. -/
def tstore : Instr → State → Option State
  | .store m r, s => some { s with mem := s.mem.writeW (s.ea m) (s.gpr r) }
  | .store32 m r, s => some { s with mem := s.mem.writeW (s.ea m) ((s.gpr r).setWidth 32) }
  | .store8 m r, s => some { s with mem := s.mem.writeW (s.ea m) ((s.gpr r).setWidth 8) }
  | .movdquStore m r, s => some { s with mem := s.mem.writeW (s.ea m) (s.xmm r) }
  | .vmovdquStore .l128 m r, s => some { s with mem := s.mem.writeW (s.ea m) (s.xmm r) }
  | .vmovdquStore .l256 m r, s => some { s with mem := s.mem.writeW (s.ea m) (s.ymm r) }
  | .vmovdqu32Store m r, s => some { s with mem := s.mem.writeW (s.ea m) (s.zmm r) }
  | .stmxcsr m, s => some { s with mem := s.mem.writeW (s.ea m) s.mxcsr }
  | _, _ => none

/-- A return as the return stack buffer predicts it: to its call site,
whatever the return address in memory (SDM Vol. 2, "RET": it moves `rsp` as
`ret` does). -/
def sret (s : State) : State := s.setReg .rsp (s.gpr .rsp + 8)

def spectre : VG.Spectre isa where
  sexec i s := (tstore i s).or (isa.exec i (widen s))
  saddrs i s := isa.addrs i s
  sret _ s := some (sret s)
  fence i := match i with
    | .lfence => true
    | _ => false

/-! ## `tstore` follows the model

`tstore` lists the model's stores by hand. These two theorems fail to build
if the model gains an instruction that writes memory without a case of
`tstore` (which would then fault transiently out of bounds, hiding what it
leaks), or if a store of `exec` and its case of `tstore` differ. -/

/-- Every instruction that `tstore` does not list leaves memory unchanged. -/
theorem mem_of_not_tstore {i : Instr} {s s' : State} (h : tstore i s = none)
    (e : exec i s = some s') : s'.mem = s.mem := by
  cases hd : Taint.dstOf i with
  | some d => exact (Taint.exec_nonstore hd e).2.2.1
  | none =>
    cases i <;> simp only [tstore, reduceCtorEq] at h <;> simp only [Taint.dstOf, reduceCtorEq] at hd
    case vmovdquStore len _ _ => cases len <;> cases h
    case vmovdquLoad len _ _ =>
      cases len <;> simp only [exec, Option.map_eq_some_iff] at e <;> obtain ⟨_, _, rfl⟩ := e <;> rfl
    case xop op => simp only [exec, Option.some.injEq] at e; subst e; rw [Taint.XOp.exec_eq]
    case vop op => simp only [exec, Option.some.injEq] at e; subst e; rw [Taint.VOp.exec_eq]
    case zop op => simp only [exec, Option.some.injEq] at e; subst e; rw [Taint.ZOp.exec_eq]
    case ldmxcsr m =>
      simp only [exec, Option.bind_eq_some_iff] at e
      obtain ⟨_, _, e⟩ := e
      split at e <;> [(cases e; rfl); cases e]
    case mulx hi lo src =>
      simp only [exec, execMulx] at e
      split at e
      · cases e
      · simp only [Option.map_eq_some_iff] at e; obtain ⟨_, _, rfl⟩ := e; rfl
    all_goals simp only [exec, Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq] at e
    all_goals first
      | (obtain ⟨_, _, rfl⟩ := e; rfl)
      | (subst e; rfl)

/-- Where a store is permitted, `tstore` is the store of `exec`. -/
theorem tstore_exec {i : Instr} {s s₁ s₂ : State} (h : tstore i s = some s₁)
    (e : exec i s = some s₂) : s₂ = s₁ := by
  cases i <;> simp only [tstore, reduceCtorEq, Option.some.injEq] at h
  case vmovdquStore len _ _ =>
    cases len <;> simp only [Option.some.injEq] at h <;> subst h <;>
      simp only [exec, State.store128, State.store256] at e <;> split at e <;>
      [(cases e; rfl); cases e; (cases e; rfl); cases e]
  all_goals subst h
  all_goals simp only [exec, State.store64, State.store32, State.store8, State.store128,
    State.store512] at e
  all_goals split at e <;> [(cases e; rfl); cases e]

theorem addrs_widen (i : Instr) (s : State) : isa.addrs i (widen s) = isa.addrs i s := by
  cases i <;> rfl

/-- `Taint.step` is sound for the speculative semantics: what the analysis
says is public does not depend on the readable regions `rd` (loads), and its
analysis of a store (`Agree.store`) does not depend on the store being
permitted. -/
theorem step_sound {τ τ' : Taint.T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Taint.Agree τ s₁ s₂)
    (hs : Taint.step τ i = some τ') (e₁ : spectre.sexec i s₁ = some s₁')
    (e₂ : spectre.sexec i s₂ = some s₂') : isa.addrs i s₁ = isa.addrs i s₂ ∧ Taint.Agree τ' s₁' s₂' := by
  have widened (x₁ : isa.exec i (widen s₁) = some s₁') (x₂ : isa.exec i (widen s₂) = some s₂') :
      isa.addrs i s₁ = isa.addrs i s₂ ∧ Taint.Agree τ' s₁' s₂' := by
    have ha' : Taint.Agree τ (widen s₁) (widen s₂) :=
      ⟨ha.rf, ha.wr, ha.wf₁, ha.wf₂, ha.ok, ha.slots, ha.lo⟩
    obtain ⟨h₁, h₂⟩ := Taint.step_sound ha' hs x₁ x₂
    exact ⟨(addrs_widen i s₁).symm.trans (h₁.trans (addrs_widen i s₂)), h₂⟩
  cases i
  case store m r =>
    simp only [Taint.step, Taint.storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    cases e₁; cases e₂
    exact ⟨congrArg (fun a => [a]) (ha.ea hok), ha.store (n := 8) hok (by decide) fun hp => by rw [ha.reg hp]⟩
  case store32 m r =>
    simp only [Taint.step, Taint.storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    cases e₁; cases e₂
    exact ⟨congrArg (fun a => [a]) (ha.ea hok), ha.store (n := 4) hok (by decide) fun hp => by rw [ha.reg hp]⟩
  case store8 m r =>
    simp only [Taint.step, Taint.storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    cases e₁; cases e₂
    exact ⟨congrArg (fun a => [a]) (ha.ea hok), ha.store (n := 1) hok (by decide) fun hp => by rw [ha.reg hp]⟩
  case movdquStore m r =>
    simp only [Taint.step, Taint.storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    cases e₁; cases e₂
    exact ⟨congrArg (fun a => [a]) (ha.ea hok), ha.store (n := 16) hok (by decide) fun hp => by cases hp⟩
  case vmovdquStore len m r =>
    cases len
    · simp only [Taint.step, Taint.storeStep] at hs
      split at hs <;> [skip; cases hs]
      rename_i hok; cases hs
      cases e₁; cases e₂
      exact ⟨congrArg (fun a => [a]) (ha.ea hok), ha.store (n := 16) hok (by decide) fun hp => by cases hp⟩
    · simp only [Taint.step, Taint.storeStep] at hs
      split at hs <;> [skip; cases hs]
      rename_i hok; cases hs
      cases e₁; cases e₂
      exact ⟨congrArg (fun a => [a]) (ha.ea hok), ha.store (n := 32) hok (by decide) fun hp => by cases hp⟩
  case vmovdqu32Store m r =>
    simp only [Taint.step, Taint.storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    cases e₁; cases e₂
    exact ⟨congrArg (fun a => [a]) (ha.ea hok), ha.store (n := 64) hok (by decide) fun hp => by cases hp⟩
  case stmxcsr m =>
    simp only [Taint.step, Taint.storeStep] at hs
    split at hs <;> [skip; cases hs]
    rename_i hok; cases hs
    cases e₁; cases e₂
    exact ⟨congrArg (fun a => [a]) (ha.ea hok), ha.store (n := 4) hok (by decide) fun hp => by cases hp⟩
  all_goals exact widened e₁ e₂

/-- `ret_sound` without the check of the return address. -/
theorem sret_sound {τ τ' : Taint.T} {b₁ b₂ : State} (ha : Taint.Agree τ b₁ b₂)
    (hs : Taint.retStep τ = some τ') : isa.retAddrs b₁ = isa.retAddrs b₂ ∧ Taint.Agree τ' (sret b₁) (sret b₂) := by
  simp only [Taint.retStep] at hs
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  have hsp := ha.reg hp
  refine ⟨by simp only [hsp], ha.keep ⟨fun r hr => ?_, ha.rf.2⟩ rfl rfl rfl rfl rfl rfl
    (Taint.kill_setReg ha.wf₁ _ _) (Taint.kill_setReg ha.wf₂ _ _) Taint.noLo⟩
  by_cases h : r = .rsp
  · subst h; simp only [sret, State.setReg, hsp, BitVec.ofNat_eq_ofNat, ↓reduceIte]
  · simp only [sret, State.setReg, h, ite_false]; exact ha.rf.1 r hr

/-- The x86-64 taint analysis is sound for the speculative semantics. -/
theorem specSound : VG.Taint.SpecSound taint spectre := by
  refine ⟨?_, fun ha hs e₁ e₂ => ?_⟩
  swap
  · cases e₁; cases e₂; exact sret_sound ha hs
  intro τ τ' i s₁ s₂ s₁' s₂' ha hs e₁ e₂
  rcases Taint.stepKD_spec τ i with ⟨h, -⟩ | ⟨a, b, h₁, h₂, hab⟩
  · have hs : Taint.stepKD τ i = some τ' := hs
    rw [h] at hs; cases hs
  · have hs : Taint.stepKD τ i = some τ' := hs
    rw [h₁] at hs; cases hs
    obtain ⟨h₃, h₄⟩ := step_sound ha h₂ e₁ e₂
    exact ⟨h₃, hab.agree h₄⟩

end VG.X86_64.Spectre
