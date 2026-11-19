module

public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An MCDT frame (x86, 32-bit)

`frame (mcdtEnter r) body mcdtLeave`: the body runs from `mcdtPushed r s`,
inside one more MCDT frame, with MXCSR's saved value at `esp + 4`; if it
keeps that word, its MCDT depth and `esp`, the pop leads to `mcdtPopped`
(`WP.mcdtFrame`). Two runs with the same `esp` push the frame at the same
addresses (`mcdt_frame`), and leak the same when the runs of its body do
(`RelCT.mcdtFrame`, from `RelCT.frameOf`, for any frame).

No instruction, call, return or frame changes `State.mxcsr`, MXCSR's value
outside MCDT frames, so neither does a run (`Exec.mxcsr`), as `Exec.syms`
for the statics.
-/

@[expose] public section

namespace VG.X86
open VG

theorem exec_mxcsr {i : Instr} {s s' : State} (h : exec i s = some s') : s'.mxcsr = s.mxcsr := by
  cases i with
  | store m r | store8 m r | movdquStore m r | movqStore m r =>
    simp only [exec, State.store32, State.store8, State.store128, State.store64] at h
    split at h <;> cases h; rfl
  | mov _ _ | movzx8 _ _ | movdquLoad _ _ | movqLoad _ _ =>
    simp only [exec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
  | alu op d src =>
    simp only [exec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, rfl⟩ := h; split <;> rfl
  | shift op _ n =>
    simp only [exec, execShift] at h
    split at h
    · cases op <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl
    · cases h
  | xop op =>
    simp only [exec, Option.some.injEq] at h; subst h; rw [SseTaint.XOp.exec_eq op s]
  | mop op => rw [MOp.exec_eq h]
  | mmxStore m r =>
    simp only [exec] at h
    split at h <;> [skip; cases h]
    simp only [State.store64] at h
    split at h <;> cases h; rfl
  | symPush | push | pop | alloc | free | mmxEnter | emms | mcdtEnter | mcdtLeave | callr =>
    simp only [exec, reduceCtorEq] at h
  | pmuludq =>
    simp only [exec] at h
    split at h <;> cases h; rfl
  | _ => simp only [exec, Option.some.injEq] at h; subst h; rfl

theorem pushRegs_mxcsr (t : State) (rs : List Reg) : (pushRegs t rs).mxcsr = t.mxcsr := by
  induction rs generalizing t with
  | nil => rfl
  | cons r rs ih => exact (ih _).trans rfl

theorem push_mxcsr {i : Instr} {s s' : State} (h : push i s = some s') : s'.mxcsr = s.mxcsr := by
  cases i <;> simp only [push, reduceCtorEq] at h <;> split at h <;> cases h <;>
    first | rfl | exact pushRegs_mxcsr _ _

theorem pop_mxcsr {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') : s'.mxcsr = s₂.mxcsr := by
  have hp : ∀ (k : Nat) (r : Reg) (t : State), (popReg t r k).mxcsr = t.mxcsr := by
    intro k; induction k with
    | zero => intro r t; rfl
    | succ k ih => intro r t; exact (ih _ _).trans rfl
  cases j <;> simp only [pop, reduceCtorEq] at h <;> split at h <;> cases h <;>
    first | rfl | exact hp _ _ _

theorem execBlock_mxcsr : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    execBlock isa is s = some (s', t) → s'.mxcsr = s.mxcsr
  | [], _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, s, s', t, h => by
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ e
      obtain ⟨⟨s₂, t₂⟩, h₂, e₂⟩ := Option.map_eq_some_iff.mp h
      cases e₂
      exact (execBlock_mxcsr h₂).trans (exec_mxcsr e)

theorem Exec.mxcsr {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.mxcsr = s.mxcsr := by
  induction h with
  | icall _ e₁ _ e₂ ih =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih
  | icallNext _ _ _ ih => exact ih
  | block e => exact execBlock_mxcsr e
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | iteT _ _ ih | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | call e₁ _ e₂ ih =>
    simp only [isa, call, Option.some.injEq] at e₁
    simp only [isa, ret] at e₂
    split at e₂ <;> [cases e₂; cases e₂]
    subst e₁; exact ih
  | frame e₁ _ e₂ ih => exact (pop_mxcsr e₂).trans (ih.trans (push_mxcsr e₁))

/-- The state after an MCDT frame's push. -/
def mcdtPushed (r : Reg) (s : State) : State :=
  { (s.setReg .esp (s.gpr .esp - 12)).setReg r 0x1FBF with
    mem := (s.mem.writeW ((s.gpr .esp - 8).setWidth 64) (mcdtSaved s.mcdt s.mxcsr)).writeW
      ((s.gpr .esp - 12).setWidth 64) (0x1FBF : BitVec 32)
    mcdt := s.mcdt + 1, wr := ⟨(s.gpr .esp - 12).setWidth 64, 9⟩ :: s.wr }

/-- The state after an MCDT frame's pop, from the state `s` its body ends in. -/
def mcdtPopped (s : State) : State :=
  { s.setReg .esp (s.gpr .esp + 12) with mcdt := s.mcdt - 1, wr := s.wr.tail }

theorem mcdtPushed_esp (r : Reg) (s : State) (hr : r ≠ .esp) :
    (mcdtPushed r s).gpr .esp = s.gpr .esp - 12 := by
  simp [mcdtPushed, State.setReg, Ne.symm hr]

theorem mcdtPushed_mcdt (r : Reg) (s : State) : (mcdtPushed r s).mcdt = s.mcdt + 1 := rfl
theorem mcdtPushed_wr (r : Reg) (s : State) :
    (mcdtPushed r s).wr = ⟨(s.gpr .esp - 12).setWidth 64, 9⟩ :: s.wr := rfl
theorem mcdtPushed_mxcsr (r : Reg) (s : State) : (mcdtPushed r s).mxcsr = s.mxcsr := rfl

theorem mcdtPopped_esp (s : State) : (mcdtPopped s).gpr .esp = s.gpr .esp + 12 := by
  simp [mcdtPopped, State.setReg]
theorem mcdtPopped_mem (s : State) : (mcdtPopped s).mem = s.mem := rfl
theorem mcdtPopped_rd (s : State) : (mcdtPopped s).rd = s.rd := rfl
theorem mcdtPopped_wr (s : State) : (mcdtPopped s).wr = s.wr.tail := rfl
/-- The pushed frame holds MXCSR's value at `esp + 4`. -/
theorem mcdtPushed_saved (r : Reg) (s : State) (hr : r ≠ .esp) (hn : 12 ≤ (s.gpr .esp).toNat) :
    (mcdtPushed r s).mem.readW (((mcdtPushed r s).gpr .esp + 4).setWidth 64) 32 = mcdtSaved s.mcdt s.mxcsr := by
  rw [mcdtPushed_esp r s hr]
  have he : ((s.gpr .esp - 12 + 4).setWidth 64 : Addr) = (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (12 : BitVec 32).toNat = 12 from rfl, show (4 : BitVec 32).toNat = 4 from rfl]
    omega_using [hn]
  have he8 : ((s.gpr .esp - 8).setWidth 64 : Addr) = (s.gpr .esp - 12).setWidth 64 + BitVec.ofNat 64 4 := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [show (12 : BitVec 32).toNat = 12 from rfl, show (8 : BitVec 32).toNat = 8 from rfl]
    omega_using [hn]
  simp only [mcdtPushed]
  rw [he, he8, Mem.readW_writeW_sep (fun x h₁ h₂ => by
      rw [Offset.lt_iff x _ (by decide : 4 + 4 ≤ 2 ^ 64)] at h₁
      omega_using [h₁, h₂]) (by decide),
    Mem.readW_writeW_self32]

theorem mcdt_push {r : Reg} {s : State} (hr : r ≠ .esp) (hn : 12 ≤ (s.gpr .esp).toNat) :
    isa.push (.mcdtEnter r) s = some (mcdtPushed r s) := by
  simp only [isa, push, ne_eq, hr, not_false_eq_true, hn, and_self, ite_true]
  rfl

/-- An MCDT frame whose body keeps `esp`, its depth and the saved MXCSR word.
The postcondition may rely on nothing the frame's 12 bytes hold, nor on the
unknowns, after the pop (as `WP.frame`'s, `Call.lean`). -/
theorem WP.mcdtFrame {r : Reg} {body : Prog isa} {s : State} {Q : State → Prop}
    (hr : r ≠ .esp) (hn : 12 ≤ (s.gpr .esp).toNat) (hsp : NoSp body)
    (hb : WP isa body (mcdtPushed r s) fun s₂ => s₂.mcdt = s.mcdt + 1 ∧
      s₂.mem.readW ((s₂.gpr .esp + 4).setWidth 64) 32 = mcdtSaved s.mcdt s.mxcsr ∧ ∀ m u,
        Frame [⟨(s.gpr .esp - 12).setWidth 64, 12⟩] s₂.mem m →
          Q { mcdtPopped s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.mcdtEnter r) body .mcdtLeave) s Q := by
  obtain ⟨t, s₂, he, hm, hs, hq⟩ := hb
  obtain ⟨-, hw⟩ := Exec.rdwr he
  have hp := Exec.gpr hsp he
  have hx := Exec.mxcsr he
  have hpop : isa.pop .mcdtLeave (mcdtPushed r s) s₂ = some { mcdtPopped s₂ with
      mem := lose s₂.mem ((s₂.gpr .esp).setWidth 64) 12 s₂.unknowns
      unknowns := fun n => s₂.unknowns (n + 6) } := by
    simp only [isa, pop]
    refine (ite_eq_left ⟨by omega_using [hm], hp, hw, ?_, ?_⟩).trans rfl
    · rw [mcdtPushed_wr, mcdtPushed_esp r s hr]; rfl
    · rw [hs, hm, hx, mcdtPushed_mxcsr, Nat.add_sub_cancel]
  exact ⟨_, _, Exec.frame (mcdt_push hr hn) he hpop,
    hq _ _ (by rw [hp, mcdtPushed_esp r s hr]; exact lose_frame _ _ _ _)⟩

theorem mcdt_push_eq {r : Reg} {s a : State} (h : isa.push (.mcdtEnter r) s = some a) :
    r ≠ .esp ∧ a = mcdtPushed r s := by
  simp only [isa, push] at h
  split at h <;> [rename_i hc; cases h]
  cases h
  exact ⟨hc.1, rfl⟩

/-- An MCDT frame's push, for runs with the same `esp`. -/
theorem mcdt_frame {r : Reg} {P : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp) :
    ∀ s₁ s₂ a₁ a₂, P s₁ s₂ → isa.push (.mcdtEnter r) s₁ = some a₁ → isa.push (.mcdtEnter r) s₂ = some a₂ →
      isa.addrs (.mcdtEnter r) s₁ = isa.addrs (.mcdtEnter r) s₂ ∧ a₁.gpr .esp = a₂.gpr .esp ∧
        a₁.wr.head?.map Region.len = a₂.wr.head?.map Region.len := by
  intro s₁ s₂ a₁ a₂ hp h₁ h₂
  obtain ⟨hr, rfl⟩ := mcdt_push_eq h₁
  obtain ⟨-, rfl⟩ := mcdt_push_eq h₂
  have e := hsp _ _ hp
  exact ⟨by simp only [addrs, e], by rw [mcdtPushed_esp _ _ hr, mcdtPushed_esp _ _ hr, e],
    by rw [mcdtPushed_wr, mcdtPushed_wr]; rfl⟩

/-- A frame whose push leaks the same addresses and leaves `esp` and the
frame's size the same in both runs, and whose pop leaks addresses of `esp`. -/
theorem RelCT.frameOf {i j : Instr} {body : Prog isa} {P R : State → State → Prop}
    (hpush : ∀ s₁ s₂ a₁ a₂, P s₁ s₂ → isa.push i s₁ = some a₁ → isa.push i s₂ = some a₂ →
      isa.addrs i s₁ = isa.addrs i s₂ ∧ a₁.gpr .esp = a₂.gpr .esp ∧
        a₁.wr.head?.map Region.len = a₂.wr.head?.map Region.len)
    (hpop : ∀ b₁ b₂ : State, b₁.gpr .esp = b₂.gpr .esp → isa.addrs j b₁ = isa.addrs j b₂)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ isa.push i s₁ = some a ∧ isa.push i s₂ = some b) body R) :
    RelCT isa P (.frame i body j) fun c₁ c₂ => c₁.gpr .esp = c₂.gpr .esp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain ⟨ha, hsp, hl⟩ := hpush _ _ _ _ hp p₁ p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨_, _, hp, p₁, p₂⟩ b₁ b₂
      obtain ⟨-, -, -, -, e₁', k₁, l₁, hk₁, hk₁', hh₁, g₁⟩ := pop_eq q₁
      obtain ⟨-, -, -, -, e₂', k₂, l₂, hk₂, hk₂', hh₂, g₂⟩ := pop_eq q₂
      have hb' := e₁'.trans (hsp.trans e₂'.symm)
      rw [hh₁, hh₂] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      have hk : k₁ = k₂ := by omega_using [hk₁, hk₁', hk₂, hk₂', hl]
      refine ⟨by rw [ha, hpop _ _ hb'], ?_⟩
      show s₁'.gpr .esp = s₂'.gpr .esp
      rw [g₁, g₂, hb', hk]

theorem mcdtLeave_addrs : ∀ b₁ b₂ : State, b₁.gpr .esp = b₂.gpr .esp →
    isa.addrs .mcdtLeave b₁ = isa.addrs .mcdtLeave b₂ := by
  intro b₁ b₂ h; simp only [addrs, h]

/-- Two runs of an MCDT frame from states with the same `esp` leak the same
trace when the runs of its body, from the states after the push, do. -/
theorem RelCT.mcdtFrame {r : Reg} {body : Prog isa} {P R : State → State → Prop}
    (hsp : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .esp = s₂.gpr .esp)
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = mcdtPushed r s₁ ∧ b = mcdtPushed r s₂) body R) :
    RelCT isa P (.frame (.mcdtEnter r) body .mcdtLeave) fun _ _ => True :=
  (RelCT.frameOf (mcdt_frame hsp) mcdtLeave_addrs (hb.mono (fun _ _ ⟨s₁, s₂, hp, p₁, p₂⟩ =>
    ⟨s₁, s₂, hp, (mcdt_push_eq p₁).2, (mcdt_push_eq p₂).2⟩) fun _ _ h => h)).mono (fun _ _ h => h)
    fun _ _ _ => trivial

end VG.X86
