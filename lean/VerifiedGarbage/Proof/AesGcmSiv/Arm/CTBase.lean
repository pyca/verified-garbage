import VerifiedGarbage.Proof.AesGcmSiv.Arm.Open
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# AES-GCM-SIV on ARMv7: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2`) piece by piece, as the AArch64
ones do (`Proof.AesGcmSiv.AArch64`): the code between calls by the taint
analysis, from the registers that hold the public arguments in both runs
(`Env`, `rel_env`), those the pieces pin to the same values, and the stack
arguments, which both runs hold and nothing writes (`Args`, `ArgOk`,
`rel_envArg`); each call by its callee's proof; a branch on a flag both
runs agree on (`rel_ite`); a loop whose condition both runs agree on
(`rel_loop`); and the next piece from the states the correctness proofs
describe (`rel_seq`).
-/

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm
open VG.Proof.AesGcm.Arm (CtrCall GhCall KeyCall ctr_rel gh_rel key_rel)

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Then, towards any relation of the final states. -/
theorem rel_seqQ {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ Q) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) Q := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- The last piece, with what correctness says of each run's final state. -/
theorem rel_wpQ {c : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h : RelCT isa (Eq2 σ₁ σ₂) c TT) (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂)
    (hq : ∀ a b, F₁ a → F₂ b → Q a b) : RelCT isa (Eq2 σ₁ σ₂) c Q :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun a b h => hq a b h.2.1 h.2.2

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.Arm.taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact Taint.agree_ofRegs hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (Eq2 σ₁ σ₂) (.block []) TT :=
  rel_taint [] (by simp) ⟨.block [], rfl⟩

/-- Code the taint analysis checks, from registers the two runs agree on and
the first `n` bytes of stack arguments, the same in both runs and apart from
the writable regions. -/
theorem rel_arg {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (n : Nat) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hsp : σ₁.sp = σ₂.sp)
    (hw₁ : σ₁.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ σ₁.wr, Region.Disjoint ⟨State.addr σ₁.sp, n⟩ r)
    (hw₂ : σ₂.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ σ₂.wr, Region.Disjoint ⟨State.addr σ₂.sp, n⟩ r)
    (hm : ∀ k < n, σ₁.mem (VG.Arm.Taint.argByte σ₁ k) = σ₂.mem (VG.Arm.Taint.argByte σ₂ k))
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint rs n) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := VG.Arm.taint) _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact agree_argTaint hr hsp hw₁ hw₂ hm) hc

theorem rel_gh {σ₁ σ₂ : State} {H Y D S : BitVec 32} {n : Nat} (h₁ : GhCall σ₁ H Y D S n)
    (h₂ : GhCall σ₂ H Y D S n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.Arm.ghFrame TT :=
  gh_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_ctr {σ₁ σ₂ : State} {K C D S : BitVec 32} {R n : Nat} (h₁ : CtrCall σ₁ K C D S R n)
    (h₂ : CtrCall σ₂ K C D S R n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.Arm.ctrFrame TT :=
  ctr_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩

theorem rel_key {σ₁ σ₂ : State} {K C S : BitVec 32} {L : Nat} (h₁ : KeyCall σ₁ K C S L)
    (h₂ : KeyCall σ₂ K C S L) : RelCT isa (Eq2 σ₁ σ₂) (.call "vg_aes_expand_key" Impl.Aes.Arm.expandKey) TT :=
  key_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, S, L, h₁, h₂⟩

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- A loop step in two runs: the condition agrees, and the runs are related
anew while it loops. -/
theorem rel_loop {body : Prog isa} {c : Cond} (I : Nat → State → State → Prop)
    (hstep : ∀ n σ₁ σ₂, I n σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) body fun s₁ s₂ => isa.eval c s₁ = isa.eval c s₂ ∧
      (isa.eval c s₁ = some true → ∃ m < n, I m s₁ s₂))
    (n : Nat) {σ₁ σ₂ : State} (h : I n σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.loop body c) TT := by
  refine (RelCT.loop (Q := TT) I (fun n => ?_) n).mono (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact h)
    fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hc, hi⟩ := hstep n s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, hc, fun _ => trivial, hi⟩

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The public arguments -/

theorem Env.agree {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) :
    ∀ r ∈ envRegs, τ₁.gpr r = τ₂.gpr r := by
  intro r hr
  simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [E₁.r7, E₂.r7]
  · rw [E₁.r8, E₂.r8]
  · rw [E₁.r9, E₂.r9]
  · rw [E₁.r10, E₂.r10]
  · rw [E₁.r11, E₂.r11]

theorem Env.sp_eq {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) : τ₁.sp = τ₂.sp := by
  rw [E₁.sp, E₂.sp]

/-- The registers holding the public arguments, and `rs`. -/
abbrev pubRegs (rs : List Reg) : List Reg := envRegs ++ rs

/-- Code the taint analysis checks, from the registers holding the public
arguments and the registers `rs` the two runs agree on. -/
theorem rel_env {c : Prog isa} {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs rs)) c h).isSome = true) :
    RelCT isa (Eq2 τ₁ τ₂) c TT :=
  rel_taint (pubRegs rs) (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) hc

theorem argByte_eq {p : Prm} (L : Lay p) {s₁ s₂ : State} (E₁ : Env p s₁) (E₂ : Env p s₂) (A₁ : Args p s₁.mem)
    (A₂ : Args p s₂.mem) : ∀ k < 12, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  refine argMem_of (j := 3) (E₁.sp_eq E₂) (by rw [E₁.sp]; have := L.spf; omega) fun i hi => ?_
  have e : ∀ {s : State}, Env p s → Args p s.mem → stackArg s i = if i = 0 then BitVec.ofNat 32 p.al
      else if i = 1 then p.D else BitVec.ofNat 32 p.n := fun {s} E A => by
    rw [Proof.AesGcm.Arm.stackArg_eq, E.sp]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact A.a0
    · exact A.a4
    · exact A.a8
  rw [e E₁ A₁, e E₂ A₂]

/-- Code the taint analysis checks, from the registers holding the public
arguments, the registers `rs` the two runs agree on, and the first three
stack arguments. -/
theorem rel_envArg {c : Prog isa} {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (A₁ : Args p τ₁.mem) (A₂ : Args p τ₂.mem) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs rs) 12) c h).isSome = true) :
    RelCT isa (Eq2 τ₁ τ₂) c TT := by
  have spf := L.spf
  have hw : ∀ {τ : State}, Env p τ →
      τ.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ τ.wr, Region.Disjoint ⟨State.addr τ.sp, 12⟩ r := fun E =>
    ⟨by rw [E.sp]; omega, fun r hr => by rw [E.sp]; exact (E.perm.argw r hr).sub_left (Region.sub_prefix (by decide))⟩
  exact rel_arg (pubRegs rs) 12 (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) (E₁.sp_eq E₂) (hw E₁) (hw E₂) (argByte_eq L E₁ E₂ A₁ A₂) hc

theorem argByte_eq16 {p : Prm} (L : Lay p) {s₁ s₂ : State} (E₁ : Env p s₁) (E₂ : Env p s₂) (A₁ : Args p s₁.mem)
    (A₂ : Args p s₂.mem) : ∀ k < 16, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  refine argMem_of (j := 4) (E₁.sp_eq E₂) (by rw [E₁.sp]; have := L.spf; omega) fun i hi => ?_
  have e : ∀ {s : State}, Env p s → Args p s.mem → stackArg s i = if i = 0 then BitVec.ofNat 32 p.al
      else if i = 1 then p.D else if i = 2 then BitVec.ofNat 32 p.n else p.T := fun {s} E A => by
    rw [Proof.AesGcm.Arm.stackArg_eq, E.sp]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
    · exact A.a0
    · exact A.a4
    · exact A.a8
    · exact A.a12
  rw [e E₁ A₁, e E₂ A₂]

/-- Code the taint analysis checks, from the registers holding the public
arguments, the registers `rs` the two runs agree on, and the first four
stack arguments (with `tag`). -/
theorem rel_envArg16 {c : Prog isa} {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (A₁ : Args p τ₁.mem) (A₂ : Args p τ₂.mem) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs rs) 16) c h).isSome = true) :
    RelCT isa (Eq2 τ₁ τ₂) c TT := by
  have spf := L.spf
  have hw : ∀ {τ : State}, Env p τ →
      τ.sp.toNat + 16 ≤ 2 ^ 32 ∧ ∀ r ∈ τ.wr, Region.Disjoint ⟨State.addr τ.sp, 16⟩ r := fun E =>
    ⟨by rw [E.sp]; omega, fun r hr => by rw [E.sp]; exact (E.perm.argw r hr).sub_left (Region.sub_prefix (by decide))⟩
  exact rel_arg (pubRegs rs) 16 (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) (E₁.sp_eq E₂) (hw E₁) (hw E₂) (argByte_eq16 L E₁ E₂ A₁ A₂) hc

end VG.Proof.AesGcmSiv.Arm
