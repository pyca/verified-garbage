module

public import VerifiedGarbage.Proof.AesGcmSiv.Scratch
import VerifiedGarbage.Proof.GcmSiv.Polyval
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.AesGcmSiv.Arm.Fn
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
public import VerifiedGarbage.Proof.AesGcmSiv.Arm.Polyval
meta import VerifiedGarbage.Proof.AesGcmSiv.Arm.Fn
meta import VerifiedGarbage.Proof.AesGcmSiv.Arm.Polyval
import VerifiedGarbage.Proof.AesGcm.Arm.Args
meta import VerifiedGarbage.Proof.AesGcm.Arm.Args
meta import VerifiedGarbage.Proof.AesGcm.Arm.Env
meta import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Impl.AesGcmSiv.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.AesGcmSiv.Arm.Fn
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Gcm.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.AesGcmSiv.Arm.Fn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Gcm.Arm.Lit

/-! ### `AesGcmSiv.Arm.FnCT`, which only this module used -/

section

/-! ### `AesGcmSiv.Arm.PolyvalCT`, which only this module used -/

section

/-!
# AES-GCM-SIV on ARMv7: relating two runs, the keys and POLYVAL

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

@[expose] public section

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

theorem rel_gh [VG.Proof.Gcm.Arm.GhashLaw] {σ₁ σ₂ : State} {H Y D S : BitVec 32} {n : Nat} (h₁ : GhCall σ₁ H Y D S n)
    (h₂ : GhCall σ₂ H Y D S n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.Arm.ghFrame TT :=
  gh_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨H, Y, D, S, n, h₁, h₂, hsp⟩

theorem rel_ctr {σ₁ σ₂ : State} {K C D S : BitVec 32} {R n : Nat} (h₁ : CtrCall σ₁ K C D S R n)
    (h₂ : CtrCall σ₂ K C D S R n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) Impl.AesGcm.Arm.ctrFrame TT :=
  ctr_rel fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, C, D, S, R, n, h₁, h₂, hsp⟩

theorem rel_key {σ₁ σ₂ : State} {K C S : BitVec 32} {L : Nat} (h₁ : KeyCall σ₁ K C S L)
    (h₂ : KeyCall σ₂ K C S L) : RelCT isa (Eq2 σ₁ σ₂) (.call "vg_aes_expand_key_scratch" Impl.Aes.Arm.expandKey) TT :=
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
  refine argMem_of (j := 3) (E₁.sp_eq E₂) (by rw [E₁.sp]; have := L.spf; omega_arith) fun i hi => ?_
  have e : ∀ {s : State}, Env p s → Args p s.mem → stackArg s i = if i = 0 then BitVec.ofNat 32 p.al
      else if i = 1 then p.D else BitVec.ofNat 32 p.n := fun {s} E A => by
    rw [Proof.AesGcm.Arm.stackArg_eq, E.sp]
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
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
    ⟨by rw [E.sp]; omega_arith, fun r hr => by rw [E.sp]; exact (E.perm.argw r hr).sub_left (Region.sub_prefix (by decide))⟩
  exact rel_arg (pubRegs rs) 12 (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) (E₁.sp_eq E₂) (hw E₁) (hw E₂) (argByte_eq L E₁ E₂ A₁ A₂) hc

theorem argByte_eq16 {p : Prm} (L : Lay p) {s₁ s₂ : State} (E₁ : Env p s₁) (E₂ : Env p s₂) (A₁ : Args p s₁.mem)
    (A₂ : Args p s₂.mem) : ∀ k < 16, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  refine argMem_of (j := 4) (E₁.sp_eq E₂) (by rw [E₁.sp]; have := L.spf; omega_arith) fun i hi => ?_
  have e : ∀ {s : State}, Env p s → Args p s.mem → stackArg s i = if i = 0 then BitVec.ofNat 32 p.al
      else if i = 1 then p.D else if i = 2 then BitVec.ofNat 32 p.n else p.T := fun {s} E A => by
    rw [Proof.AesGcm.Arm.stackArg_eq, E.sp]
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
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
    ⟨by rw [E.sp]; omega_arith, fun r hr => by rw [E.sp]; exact (E.perm.argw r hr).sub_left (Region.sub_prefix (by decide))⟩
  exact rel_arg (pubRegs rs) 16 (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) (E₁.sp_eq E₂) (hw E₁) (hw E₂) (argByte_eq16 L E₁ E₂ A₁ A₂) hc

end VG.Proof.AesGcmSiv.Arm

/-!
## The keys are constant time

Untrusted: everything here is checked by Lean. Both runs derive the same
number of blocks (`rounds / 2 − 1`, from `r8`); the code around the calls
passes the taint analysis, and each call has the same arguments in both
runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Proof.AesGcm.Arm (CtrCall ctr_call KeyCall key_call eval_ne')

/-- A run of `derive` before block `i`. -/
structure DC (p : Prm) (i : Nat) (t : State) : Prop where
  env : Env p t
  r4 : t.gpr .r4 = BitVec.ofNat 32 i

theorem derA_wp {p : Prm} (L : Lay p) {i : Nat} {t : State} (h : DC p i t) :
    WP isa (.block deriveBlock) t fun t₁ =>
      CtrCall t₁ p.K (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 176) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧
        DC p i t₁ := by
  obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := derArgs_ok L h.env h.r4
  have E₁ : Env p t₁ := h.env.of_others ho₁ sp₁ rd₁ wr₁
  exact WP.of_runBlock ⟨t₁, run₁, derCall L E₁ r0 r1 r2 r3 r12 lr, E₁, by rw [ho₁ _ (by decide), h.r4]⟩

theorem derC_wp {p : Prm} {i : Nat} {t : State}
    (h : CtrCall t p.K (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 176) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧
      DC p i t) :
    WP isa Impl.AesGcm.Arm.ctrFrame t (DC p i) :=
  WP.mono (ctr_call h.1) fun _ P =>
    ⟨h.2.env.of_saved P.saved P.sp P.rd P.wr, by rw [P.saved _ (by decide) (by decide), h.2.r4]⟩

theorem derP_wp {p : Prm} (L : Lay p) {i : Nat} (hi : i < p.R / 2 - 1) {t : State} (h : DC p i t) :
    WP isa (.block derivePost) t fun t' => DC p (i + 1) t' ∧ t'.z = decide (i + 1 = p.R / 2 - 1) := by
  obtain ⟨t', run', -, r4', z', ho', sp', rd', wr'⟩ := derPost_ok L h.env hi h.r4
  exact WP.of_runBlock ⟨t', run', ⟨h.env.of_others ho' sp' rd' wr', r4'⟩, z'⟩

theorem derA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4])) (.block deriveBlock) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem derP_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4])) (.block derivePost) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem der0_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [.mov .r4 (Impl.AesGcm.Arm.imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

/-- `derive`, in two runs with the same public arguments. -/
theorem derive_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) derive TT := by
  have hR := L.rounds
  have w0 : ∀ {σ : State}, Env p σ → WP isa (.block [.mov .r4 (Impl.AesGcm.Arm.imm 0)]) σ (DC p 0) := fun E =>
    Proof.AesGcm.Arm.WP.run ⟨_, by srun [], rfl⟩ fun t ht => by
      subst ht
      exact ⟨E.keep (fun r hr => by
          simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
        by simp [gpr_setReg]⟩
  refine rel_seq (rel_env E₁ E₂ [] (by simp) der0_check) (w0 E₁) (w0 E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  refine rel_loop (fun m t₁ t₂ => ∃ i, m = (p.R / 2 - 1) - i ∧ i < p.R / 2 - 1 ∧ DC p i t₁ ∧ DC p i t₂)
    (fun m t₁ t₂ ⟨i, hm, hi, I₁, I₂⟩ => ?_) ((p.R / 2 - 1) - 0)
    ⟨0, rfl, by rcases hR with h | h <;> rw [h] <;> decide, D₁, D₂⟩
  refine rel_seqQ (rel_env I₁.env I₂.env [.r4] (by simp [I₁.r4, I₂.r4]) derA_check) (derA_wp L I₁)
    (derA_wp L I₂) fun u₁ u₂ A₁ A₂ => ?_
  refine rel_seqQ (rel_ctr A₁.1 A₂.1 (A₁.2.env.sp_eq A₂.2.env)) (derC_wp A₁) (derC_wp A₂)
    fun a b J₁ J₂ => ?_
  refine rel_wpQ (rel_env J₁.env J₂.env [.r4] (by simp [J₁.r4, J₂.r4]) derP_check) (derP_wp L hi J₁)
    (derP_wp L hi J₂) fun a' b' ⟨K₁, z₁⟩ ⟨K₂, z₂⟩ => ?_
  have ev₁ := eval_ne' z₁
  have ev₂ := eval_ne' z₂
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : i + 1 ≠ p.R / 2 - 1 := by simpa using hc
  exact ⟨(p.R / 2 - 1) - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, K₁, K₂⟩

theorem expA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block expandArgs) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem hkey_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block hkey) h).isSome
    = true := ⟨_, by taint_decide⟩

/-- `keys`, in two runs with the same public arguments. -/
theorem keys_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (E₁ : Env p σ₁) (E₂ : Env p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) keys TT := by
  refine rel_seq (derive_rel L E₁ E₂) (derive_ok L E₁) (derive_ok L E₂) fun τ₁ τ₂ D₁ D₂ => ?_
  have wA : ∀ {τ : State}, Env p τ → WP isa (.block expandArgs) τ fun t₁ =>
      KeyCall t₁ (p.W + BitVec.ofNat 32 32) (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 1712)
        (Spec.GcmSiv.keyLen p.R) ∧ Env p t₁ := fun E => by
    obtain ⟨t₁, run₁, kc, E', -⟩ := expArgs_ok L E
    exact WP.of_runBlock ⟨t₁, run₁, kc, E'⟩
  refine rel_seq (c₁ := expand) ?_ (WP.mono (expand_ok L D₁.env) fun _ X => X.env)
    (WP.mono (expand_ok L D₂.env) fun _ X => X.env) fun u₁ u₂ F₁ F₂ =>
      rel_env F₁ F₂ [] (by simp) hkey_check
  exact rel_seq (rel_env D₁.env D₂.env [] (by simp) expA_check) (wA D₁.env) (wA D₂.env)
    fun a b ⟨k₁, _⟩ ⟨k₂, _⟩ => rel_key k₁ k₂

end VG.Proof.AesGcmSiv.Arm

/-!
## POLYVAL is constant time

Untrusted: everything here is checked by Lean. A chunk's blocks, their
number and the pointers come from the public lengths and addresses; the
calls of `vg_ghash` have the same arguments in both runs; the branches and
loops are on counts both runs agree on.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (GhCall gh_call eval_eq' eval_ne' z_cmp z_subFlags mem_subFlags gpr_subFlags sp_subFlags
  rd_subFlags wr_subFlags)

theorem chunkPre_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5])) chunkPre h).isSome
    = true := ⟨_, by taint_decide⟩

theorem chunkEnd_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r5]))
    (.block wholeLeft) h).isSome = true := ⟨_, by taint_decide⟩

/-- A chunk, in two runs with the same public arguments, pointer and count. -/
theorem chunk_rel [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (h16 : 16 ≤ m) (hQ₁ : Src p τ₁ Q (16 * (m / 16)))
    (hQ₂ : Src p τ₂ Q (16 * (m / 16))) (a4 : τ₁.gpr .r4 = Q) (b4 : τ₂.gpr .r4 = Q)
    (a5 : τ₁.gpr .r5 = BitVec.ofNat 32 m) (b5 : τ₂.gpr .r5 = BitVec.ofNat 32 m) :
    RelCT isa (Eq2 τ₁ τ₂) chunk TT := by
  refine rel_seq (rel_env E₁ E₂ [.r4, .r5] (by simp [a4, b4, a5, b5]) chunkPre_check)
    (chunkPre_ok L E₁ hm h16 hQ₁ a4 a5) (chunkPre_ok L E₂ hm h16 hQ₂ b4 b5) fun u₁ u₂ P₁ P₂ => ?_
  have wG : ∀ {u : State}, ChunkPre p Q m (min (m / 16) 64) τ₁ u ∨ ChunkPre p Q m (min (m / 16) 64) τ₂ u →
      WP isa Impl.AesGcm.Arm.ghFrame u fun w => Env p w ∧ w.gpr .r5 = BitVec.ofNat 32 (m - 16 * min (m / 16) 64) :=
    fun h => by
      rcases h with P | P <;>
      exact WP.mono (gh_call P.call) fun _ G =>
        ⟨P.env.of_saved G.saved G.sp G.rd G.wr, by rw [G.saved _ (by decide) (by decide), P.r5]⟩
  exact rel_seq (rel_gh P₁.call P₂.call (P₁.env.sp_eq P₂.env)) (wG (.inl P₁)) (wG (.inr P₂))
    fun w₁ w₂ G₁ G₂ => rel_env G₁.1 G₂.1 [.r5] (by simp [G₁.2, G₂.2]) chunkEnd_check

/-- The chunks, in two runs from `σ₁` and `σ₂` with the same public arguments. -/
theorem chunks_rel [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {σ₁ σ₂ : State} {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32)
    (hQ₁ : Src p σ₁ Q (16 * (m / 16))) (hQ₂ : Src p σ₂ Q (16 * (m / 16))) {d : Nat}
    (hd : d < m / 16) {τ₁ τ₂ : State} (I₁ : CInv p σ₁ Q m d τ₁) (I₂ : CInv p σ₂ Q m d τ₂) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop chunk .ne) TT := by
  refine rel_loop (fun k t₁ t₂ => ∃ d, k = m / 16 - d ∧ d < m / 16 ∧ CInv p σ₁ Q m d t₁ ∧ CInv p σ₂ Q m d t₂)
    (fun k t₁ t₂ ⟨d, hk, hd, J₁, J₂⟩ => ?_) (m / 16 - d) ⟨d, rfl, hd, I₁, I₂⟩
  refine rel_wpQ (chunk_rel L J₁.abs.env J₂.abs.env (by omega_arith) (by omega_arith) (J₁.src hQ₁ hd) (J₂.src hQ₂ hd)
      J₁.r4 J₂.r4 J₁.r5 J₂.r5)
    (chunk_ok L J₁.abs.env (by omega_arith) (by omega_arith) (J₁.src hQ₁ hd) J₁.r4 J₁.r5)
    (chunk_ok L J₂.abs.env (by omega_arith) (by omega_arith) (J₂.src hQ₂ hd) J₂.r4 J₂.r5) fun a b C₁ C₂ => ?_
  obtain ⟨K₁, z₁⟩ := J₁.step L hQ₁ hd C₁
  obtain ⟨K₂, z₂⟩ := J₂.step L hQ₂ hd C₂
  have ev₁ := eval_ne' z₁
  have ev₂ := eval_ne' z₂
  refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
  rw [ev₁] at hc
  have he : m / 16 - (d + min (m / 16 - d) 64) ≠ 0 := by simpa using hc
  exact ⟨m / 16 - (d + min (m / 16 - d) 64), by omega_arith, d + min (m / 16 - d) 64, rfl, by omega_arith, K₁, K₂⟩

theorem absHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block wholeLeft) h).isSome = true := ⟨_, by taint_decide⟩

theorem absCmp_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem absTailPre_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5])) absTailPre
    h).isSome = true := ⟨_, by taint_decide⟩

/-- `chunk` on the block at `W + 176`. -/
theorem chunkB_rel [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (a4 : τ₁.gpr .r4 = p.W + BitVec.ofNat 32 176) (b4 : τ₂.gpr .r4 = p.W + BitVec.ofNat 32 176)
    (a5 : τ₁.gpr .r5 = BitVec.ofNat 32 16) (b5 : τ₂.gpr .r5 = BitVec.ofNat 32 16) :
    RelCT isa (Eq2 τ₁ τ₂) chunk TT :=
  chunk_rel L E₁ E₂ (m := 16) (by decide) (by decide) (srcB L E₁.perm) (srcB L E₂.perm) a4 b4 a5 b5

/-- `cmp r5, #0`. -/
theorem cmp5_ok {t : State} {r : Nat} (hr : r < 2 ^ 32) (h5 : t.gpr .r5 = BitVec.ofNat 32 r) :
    WP isa (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) t fun t' => t'.z = decide (r = 0) ∧ t'.gpr = t.gpr ∧
      t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr :=
  Proof.AesGcm.Arm.WP.run ⟨_, by srun [h5], rfl⟩ fun t' ht => by
    subst ht
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [z_subFlags]
    rw [z_cmp hr (by decide)]

/-- `absorb`, in two runs with the same public arguments, pointer and count. -/
theorem absorb_rel [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    {Q : BitVec 32} {m : Nat} (hm : m < 2 ^ 32) (hd : (⟨State.addr Q, m⟩ : Region).Disjoint ⟨State.addr p.W, 3760⟩)
    (hQ₁ : Src p τ₁ Q m) (hQ₂ : Src p τ₂ Q m)
    (a4 : τ₁.gpr .r4 = Q) (b4 : τ₂.gpr .r4 = Q) (a5 : τ₁.gpr .r5 = BitVec.ofNat 32 m)
    (b5 : τ₂.gpr .r5 = BitVec.ofNat 32 m) :
    RelCT isa (Eq2 τ₁ τ₂) absorb TT := by
  have wH : ∀ {τ : State}, Env p τ → τ.gpr .r4 = Q → τ.gpr .r5 = BitVec.ofNat 32 m →
      WP isa (.block wholeLeft) τ fun u => Env p u ∧ u.gpr .r4 = Q ∧ u.gpr .r5 = BitVec.ofNat 32 m ∧
        u.z = decide (m / 16 = 0) ∧ u.mem = τ.mem ∧ u.rd = τ.rd ∧ u.wr = τ.wr := fun E h4 h5 => by
    obtain ⟨u, run, z, ho, hm', sp, rd, wr⟩ := wholeLeft_ok hm h5
    exact WP.of_runBlock ⟨u, run, E.of_others ho sp rd wr, by rw [ho _ (by decide), h4],
      by rw [ho _ (by decide), h5], z, hm', rd, wr⟩
  refine rel_seq (rel_env E₁ E₂ [.r4, .r5] (by simp [a4, b4, a5, b5]) absHead_check) (wH E₁ a4 a5)
    (wH E₂ b4 b5) fun u₁ u₂ ⟨F₁, u4₁, u5₁, z₁, m₁, rd₁, wr₁⟩ ⟨F₂, u4₂, u5₂, z₂, m₂, rd₂, wr₂⟩ => ?_
  have hQ₁' := hQ₁.of_eq rd₁ wr₁
  have hQ₂' := hQ₂.of_eq rd₂ wr₂
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_eq' z₁) (eval_eq' z₂)
      (fun _ => rel_skip) (fun hf => ?_))
    (absMid_ok L F₁ hm hQ₁' u4₁ u5₁ z₁) (absMid_ok L F₂ hm hQ₂' u4₂ u5₂ z₂)
    fun w₁ w₂ ⟨A₁, r4₁, r5₁⟩ ⟨A₂, r4₂, r5₂⟩ => ?_
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_rel L hm (hQ₁'.take (by omega_arith)) (hQ₂'.take (by omega_arith)) (d := 0) (by omega_arith)
      (CInv.zero F₁ u4₁ u5₁) (CInv.zero F₂ u4₂ u5₂)
  -- The last bytes.
  have wC : ∀ {w : State}, Env p w → w.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) →
      w.gpr .r5 = BitVec.ofNat 32 (m % 16) → WP isa (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) w fun u =>
        Env p u ∧ u.gpr .r4 = Q + BitVec.ofNat 32 (16 * (m / 16)) ∧ u.gpr .r5 = BitVec.ofNat 32 (m % 16) ∧
          u.z = decide (m % 16 = 0) ∧ u.rd = w.rd ∧ u.wr = w.wr := fun E h4 h5 =>
    WP.mono (cmp5_ok (by omega_arith) h5) fun u ⟨z, g, _, sp, rd, wr⟩ =>
      ⟨E.keep (fun r _ => by rw [g]) sp rd wr, by rw [g, h4], by rw [g, h5], z, rd, wr⟩
  refine rel_seq (rel_env A₁.env A₂.env [.r4, .r5] (by simp [r4₁, r4₂, r5₁, r5₂]) absCmp_check)
    (wC A₁.env r4₁ r5₁) (wC A₂.env r4₂ r5₂) fun c₁ c₂ ⟨G₁, c4₁, c5₁, cz₁, crd₁, cwr₁⟩ ⟨G₂, c4₂, c5₂, cz₂, crd₂, cwr₂⟩ => ?_
  refine rel_ite (eval_eq' cz₁) (eval_eq' cz₂) (fun _ => rel_skip) (fun hf => ?_)
  have h0 : m % 16 ≠ 0 := by simpa using hf
  have ea := hQ₁.addr (j := 16 * (m / 16)) (by omega_arith)
  have dT : (⟨State.addr (Q + BitVec.ofNat 32 (16 * (m / 16))), m % 16⟩ : Region).Disjoint
      ⟨State.addr p.W, 3760⟩ := by
    rw [ea]; exact hd.sub_left (Offset.sub_base _ (by omega_arith))
  have hs₁ := ((hQ₁'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega_arith) (by omega_arith)).of_eq A₁.rd A₁.wr).of_eq crd₁ cwr₁
  have hs₂ := ((hQ₂'.slice (a := 16 * (m / 16)) (k := m % 16) (by omega_arith) (by omega_arith)).of_eq A₂.rd A₂.wr).of_eq crd₂ cwr₂
  refine rel_seq (rel_env G₁ G₂ [.r4, .r5] (by simp [c4₁, c4₂, c5₁, c5₂]) absTailPre_check)
    (absTailPre_ok L G₁ (by omega_arith) (by omega_arith) hs₁.rd hs₁.wrap dT c4₁ c5₁)
    (absTailPre_ok L G₂ (by omega_arith) (by omega_arith) hs₂.rd hs₂.wrap dT c4₂ c5₂) fun z₁ z₂ T₁ T₂ => ?_
  exact chunkB_rel L T₁.env T₂.env T₁.r4 T₂.r4 T₁.r5 T₂.r5

theorem lensBlock_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12) (.block lensBlock) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem tagIn_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block tagIn) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem polyA_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12)
    (.block [.mov .r4 (.reg .r7), .ldrSp .r5 0]) h).isSome = true := ⟨_, by taint_decide⟩

theorem polyD_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12)
    (.block [.ldrSp .r4 4, .ldrSp .r5 8]) h).isSome = true := ⟨_, by taint_decide⟩

/-- What a run keeps before a piece: the environment and the stack
arguments. -/
structure PR (p : Prm) (t : State) : Prop where
  env : Env p t
  args : Args p t.mem

/-- After absorbing. -/
theorem PR.of_abs {p : Prm} (L : Lay p) {xs : List Spec.GcmSiv.Elem} {t t' : State} (h : PR p t)
    (P : AbsPost p xs t t') : PR p t' :=
  ⟨P.env, h.args.frame L P.frame (absorbR_args L)⟩

/-- `polyval`, in two runs with the same public arguments. -/
theorem polyval_rel [VG.Proof.Gcm.Arm.GhashLaw] {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (R₁ : PR p σ₁) (R₂ : PR p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) polyval TT := by
  have wA : ∀ {σ : State}, PR p σ → WP isa (.block [.mov .r4 (.reg .r7), .ldrSp .r5 0]) σ fun t =>
      PR p t ∧ t.gpr .r4 = p.A ∧ t.gpr .r5 = BitVec.ofNat 32 p.al := fun R => by
    have a₀ := R.env.perm.argR' L (k := 0) (by decide)
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [R.env.sp, a₀, R.args.a0], rfl⟩ fun t ht => ?_
    subst ht
    exact ⟨⟨R.env.keep (fun r hr => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, R.args⟩,
      by simp [gpr_setReg, R.env.r7], by simp [gpr_setReg]⟩
  have wD : ∀ {σ : State}, PR p σ → WP isa (.block [.ldrSp .r4 4, .ldrSp .r5 8]) σ fun t =>
      PR p t ∧ t.gpr .r4 = p.D ∧ t.gpr .r5 = BitVec.ofNat 32 p.n := fun R => by
    have a₄ := R.env.perm.argR' L (k := 4) (by decide)
    have a₈ := R.env.perm.argR' L (k := 8) (by decide)
    refine Proof.AesGcm.Arm.WP.run ⟨_, by srun [R.env.sp, a₄, a₈, R.args.a4, R.args.a8], rfl⟩ fun t ht => ?_
    subst ht
    exact ⟨⟨R.env.keep (fun r hr => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl, R.args⟩,
      by simp [gpr_setReg], by simp [gpr_setReg]⟩
  refine rel_seq (rel_envArg L R₁.env R₂.env R₁.args R₂.args [] (by simp) polyA_check) (wA R₁) (wA R₂)
    fun a₁ a₂ ⟨G₁, a4₁, a5₁⟩ ⟨G₂, a4₂, a5₂⟩ => ?_
  refine rel_seq (absorb_rel L G₁.env G₂.env L.al_lt L.a_w (srcA L G₁.env.perm) (srcA L G₂.env.perm) a4₁ a4₂ a5₁ a5₂)
    (absorb_ok L G₁.env L.al_lt (srcA L G₁.env.perm) L.a_w a4₁ a5₁)
    (absorb_ok L G₂.env L.al_lt (srcA L G₂.env.perm) L.a_w a4₂ a5₂)
    fun b₁ b₂ B₁ B₂ => ?_
  have H₁ := G₁.of_abs L B₁
  have H₂ := G₂.of_abs L B₂
  refine rel_seq (rel_envArg L H₁.env H₂.env H₁.args H₂.args [] (by simp) polyD_check) (wD H₁) (wD H₂)
    fun c₁ c₂ ⟨K₁, c4₁, c5₁⟩ ⟨K₂, c4₂, c5₂⟩ => ?_
  refine rel_seq (absorb_rel L K₁.env K₂.env L.n_lt L.d_w (srcD L K₁.env.perm) (srcD L K₂.env.perm) c4₁ c4₂ c5₁ c5₂)
    (absorb_ok L K₁.env L.n_lt (srcD L K₁.env.perm) L.d_w c4₁ c5₁)
    (absorb_ok L K₂.env L.n_lt (srcD L K₂.env.perm) L.d_w c4₂ c5₂)
    fun d₁ d₂ D₁ D₂ => ?_
  have M₁ := K₁.of_abs L D₁
  have M₂ := K₂.of_abs L D₂
  refine rel_seq (c₁ := lens) ?_ (lens_ok L M₁.env M₁.args) (lens_ok L M₂.env M₂.args) fun e₁ e₂ F₁ F₂ =>
    rel_env F₁.env F₂.env [] (by simp) tagIn_check
  have wL : ∀ {d : State}, PR p d → WP isa (.block lensBlock) d fun t =>
      Env p t ∧ t.gpr .r4 = p.W + BitVec.ofNat 32 176 ∧ t.gpr .r5 = BitVec.ofNat 32 16 := fun R => by
    have w₀ := R.env.perm.wW (show 176 + 4 ≤ 3760 by decide)
    have w₁ := R.env.perm.wW (show 180 + 4 ≤ 3760 by decide)
    have w₂ := R.env.perm.wW (show 184 + 4 ≤ 3760 by decide)
    have w₃ := R.env.perm.wW (show 188 + 4 ≤ 3760 by decide)
    have a₀ := R.env.perm.argR' L (k := 0) (by decide)
    have a₈ := R.env.perm.argR' L (k := 8) (by decide)
    refine Proof.AesGcm.Arm.WP.run ⟨_, by simp only [lensBlock]; srun [R.env.r11, R.env.sp, L.wA, a₀, a₈,
      R.args.a0, R.args.a8, w₀, w₁, w₂, w₃], rfl⟩ fun t ht => ?_
    subst ht
    refine ⟨R.env.keep (fun q hq => by
        simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      by simp [gpr_setReg, R.env.r11], by simp [gpr_setReg]⟩
  exact rel_seq (rel_envArg L M₁.env M₂.env M₁.args M₂.args [] (by simp) lensBlock_check) (wL M₁)
    (wL M₂) fun f₁ f₂ ⟨K₁, x4₁, x5₁⟩ ⟨K₂, x4₂, x5₂⟩ => chunkB_rel L K₁ K₂ x4₁ x4₂ x5₁ x5₂

end VG.Proof.AesGcmSiv.Arm

end

end

/-!
# AES-GCM-SIV on ARMv7: the functions are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments (`onePub`) have the same `prmOf`; each piece of `seal` and
`open` is related in the two runs by the lemmas of `PolyvalCT.lean`, the
counter mode's blocks by `vg_aes_ctr32`'s proof with
the same arguments in both runs, and the comparison, the mask and the
restore by the taint analysis (`seal_ct`, `open_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcmSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (CtrCall ctr_call eval_eq' eval_ne' arg args argAddr_zero)

/-! ## The tag -/

theorem tagA_check {o : Nat} (ho : o = 0 ∨ o = 176) : ∃ h, (VG.Taint.check VG.Arm.taint
    (VG.Arm.Taint.ofRegs (pubRegs [])) (.block (copy16 cbO ccO ++ Impl.AesGcm.Arm.zero16 o ++ ctrArgs ++
      ([Impl.AesGcm.Arm.addI .r3 .r11 o] : List Instr))) h).isSome = true := by
  rcases ho with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag o`, in two runs with the same public arguments. -/
theorem tag_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) {o : Nat}
    (ho : o = 0 ∨ o = 176) : RelCT isa (Eq2 τ₁ τ₂) (tag o) TT := by
  have w : ∀ {τ : State}, Env p τ → WP isa (.block (copy16 cbO ccO ++ Impl.AesGcm.Arm.zero16 o ++ ctrArgs ++
      ([Impl.AesGcm.Arm.addI .r3 .r11 o] : List Instr))) τ fun t₁ => CtrCall t₁ (p.W + BitVec.ofNat 32 192)
        (p.W + BitVec.ofNat 32 112) (p.W + BitVec.ofNat 32 o) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧ Env p t₁ :=
    fun E => by
      obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := tagArgs_ok L E ho
      have E' : Env p t₁ := E.of_others ho₁ sp₁ rd₁ wr₁
      exact WP.of_runBlock ⟨t₁, run₁, tagCall L E' ho r0 r1 r2 r3 r12 lr, E'⟩
  exact rel_seq (rel_env E₁ E₂ [] (by simp) (tagA_check ho)) (w E₁) (w E₂)
    fun a b A₁ A₂ => rel_ctr A₁.1 A₂.1 (A₁.2.sp_eq A₂.2)

/-! ## Counter mode -/

theorem blkA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr))) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem blkP_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block blockNext) h).isSome = true := ⟨_, by taint_decide⟩

/-- What the constant-time proof needs of a run of counter mode after `j`
blocks. -/
structure BL (p : Prm) (j : Nat) (t : State) : Prop where
  env : Env p t
  r4 : t.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j)
  r5 : t.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j)

/-- A block of counter mode, in two runs with the same public arguments,
pointer and count. -/
theorem cryptBlock_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (B₁ : BL p j τ₁) (B₂ : BL p j τ₂) : RelCT isa (Eq2 τ₁ τ₂) cryptBlock TT := by
  have w : ∀ {τ : State}, BL p j τ →
      WP isa (.block (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr))) τ fun t₁ =>
        CtrCall t₁ (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112) (p.D + BitVec.ofNat 32 (16 * j))
          (p.W + BitVec.ofNat 32 1712) p.R 1 ∧ BL p j t₁ := fun B => by
    obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok L B.env B.r4
    have E' : Env p t₁ := B.env.of_others ho₁ sp₁ rd₁ wr₁
    exact WP.of_runBlock ⟨t₁, run₁, blkCall L E' hj r0 r1 r2 r3 r12 lr, E', by rw [ho₁ _ (by decide), B.r4],
      by rw [ho₁ _ (by decide), B.r5]⟩
  have wc : ∀ {t : State}, (CtrCall t (p.W + BitVec.ofNat 32 192) (p.W + BitVec.ofNat 32 112)
      (p.D + BitVec.ofNat 32 (16 * j)) (p.W + BitVec.ofNat 32 1712) p.R 1 ∧ BL p j t) →
      WP isa Impl.AesGcm.Arm.ctrFrame t (BL p j) := fun ⟨cc, B⟩ =>
    WP.mono (ctr_call cc) fun _ P => ⟨B.env.of_saved P.saved P.sp P.rd P.wr,
      by rw [P.saved _ (by decide) (by decide), B.r4], by rw [P.saved _ (by decide) (by decide), B.r5]⟩
  refine rel_seq (rel_env B₁.env B₂.env [.r4, .r5] (by simp [B₁.r4, B₂.r4, B₁.r5, B₂.r5]) blkA_check) (w B₁)
    (w B₂) fun u₁ u₂ A₁ A₂ => ?_
  exact rel_seq (rel_ctr A₁.1 A₂.1 (A₁.2.env.sp_eq A₂.2.env)) (wc A₁) (wc A₂)
    fun w₁ w₂ C₁ C₂ => rel_env C₁.env C₂.env [.r4, .r5] (by simp [C₁.r4, C₂.r4, C₁.r5, C₂.r5]) blkP_check

/-- A block of counter mode, for its registers. -/
theorem cryptBlockL_ok {p : Prm} (L : Lay p) {j : Nat} (hj : 16 * (j + 1) ≤ p.n) {t : State} (B : BL p j t) :
    WP isa cryptBlock t fun t' => BL p (j + 1) t' ∧ t'.z = decide ((p.n - 16 * (j + 1)) / 16 = 0) := by
  obtain ⟨t₁, run₁, -, r0, r1, r2, r3, r12, lr, ho₁, sp₁, rd₁, wr₁⟩ := blkArgs_ok L B.env B.r4
  have E₁ : Env p t₁ := B.env.of_others ho₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (ctr_call (blkCall L E₁ hj r0 r1 r2 r3 r12 lr)) fun t₂ P => ?_)
  have E₂ : Env p t₂ := E₁.of_saved P.saved P.sp P.rd P.wr
  have h4₂ : t₂.gpr .r4 = p.D + BitVec.ofNat 32 (16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.r4]
  have h5₂ : t₂.gpr .r5 = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [P.saved _ (by decide) (by decide), ho₁ _ (by decide), B.r5]
  obtain ⟨t₃, run₃, -, r4₃, r5₃, z₃, ho₃, sp₃, rd₃, wr₃⟩ := blkPost_ok L E₂ hj h4₂ h5₂
  exact WP.of_runBlock ⟨t₃, run₃, ⟨E₂.of_others ho₃ sp₃ rd₃ wr₃, r4₃, r5₃⟩, z₃⟩

/-- The whole blocks of counter mode, for their registers. -/
theorem cryptMidL_ok {p : Prm} (L : Lay p) {t : State} (B : BL p 0 t) (hz : t.z = decide (p.n / 16 = 0)) :
    WP isa (.ite .eq (.block []) (.loop cryptBlock .ne)) t (BL p (p.n / 16)) := by
  refine WP.ite (decide (p.n / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n / 16 = 0 := by simpa using ht
    rw [h0]; exact WP.block_nil B
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine WP.loop (M := isa) (fun k t' => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BL p j t') ?_
      (p.n / 16 - 0) t ⟨0, rfl, by omega_arith, B⟩
    rintro k t' ⟨j, rfl, hj, B'⟩
    refine WP.mono (cryptBlockL_ok L (j := j) (by omega_arith) B') fun t'' ⟨B'', z⟩ => ?_
    have ev := eval_ne' z
    by_cases he : j + 1 = p.n / 16
    · left; exact ⟨ev.trans (by simp; omega_arith), he ▸ B''⟩
    · right; exact ⟨ev.trans (by simp; omega_arith), p.n / 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, B''⟩

theorem cryptHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12) (.block cryptHead) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem crypt5_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem cryptTailRest_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (.seq (.block [Impl.AesGcm.Arm.addI .r1 .r11 bO, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)])
      Impl.AesGcm.Arm.xorLoop) h).isSome = true := ⟨_, by taint_decide⟩

/-- `crypt`, in two runs with the same public arguments. -/
theorem crypt_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (R₁ : PR p σ₁) (R₂ : PR p σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) crypt TT := by
  have hn := L.n_lt
  have wh : ∀ {σ : State}, PR p σ → WP isa (.block cryptHead) σ fun t₁ => BL p 0 t₁ ∧
      t₁.z = decide (p.n / 16 = 0) := fun R => by
    obtain ⟨t₁, run₁, -, r4₁, r5₁, z₁, ho₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L R.env R.args
    exact WP.of_runBlock ⟨t₁, run₁, ⟨R.env.of_others ho₁ sp₁ rd₁ wr₁,
      by rw [r4₁, Nat.mul_zero, Proof.AesGcm.Arm.add_ofNat_zero], by rw [r5₁, Nat.mul_zero, Nat.sub_zero]⟩, z₁⟩
  refine rel_seq (rel_envArg L R₁.env R₂.env R₁.args R₂.args [] (by simp) cryptHead_check) (wh R₁) (wh R₂)
    fun u₁ u₂ ⟨B₁, z₁⟩ ⟨B₂, z₂⟩ => ?_
  -- The whole blocks.
  refine rel_seq (rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_skip) (fun hf => ?_))
    (cryptMidL_ok L B₁ z₁) (cryptMidL_ok L B₂ z₂) fun w₁ w₂ C₁ C₂ => ?_
  · have h0 : p.n / 16 ≠ 0 := by simpa using hf
    refine rel_loop (fun k t₁ t₂ => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BL p j t₁ ∧ BL p j t₂)
      (fun k t₁ t₂ ⟨j, hk, hj, J₁, J₂⟩ => ?_) (p.n / 16 - 0) ⟨0, rfl, by omega_arith, B₁, B₂⟩
    refine rel_wpQ (cryptBlock_rel L (j := j) (by omega_arith) J₁ J₂)
      (cryptBlockL_ok L (by omega_arith) J₁) (cryptBlockL_ok L (by omega_arith) J₂) fun a b ⟨K₁, z₁⟩ ⟨K₂, z₂⟩ => ?_
    have ev₁ := eval_ne' z₁
    have ev₂ := eval_ne' z₂
    refine ⟨by rw [ev₁, ev₂], fun hc => ?_⟩
    rw [ev₁] at hc
    have he : (p.n - 16 * (j + 1)) / 16 ≠ 0 := by simpa using hc
    exact ⟨p.n / 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, K₁, K₂⟩
  -- The last bytes.
  have r5₁ : w₁.gpr .r5 = BitVec.ofNat 32 (p.n % 16) := by rw [C₁.r5]; congr 1; omega_arith
  have r5₂ : w₂.gpr .r5 = BitVec.ofNat 32 (p.n % 16) := by rw [C₂.r5]; congr 1; omega_arith
  have wC : ∀ {w : State}, BL p (p.n / 16) w → w.gpr .r5 = BitVec.ofNat 32 (p.n % 16) →
      WP isa (.block [.cmp .r5 (Impl.AesGcm.Arm.imm 0)]) w fun u =>
        BL p (p.n / 16) u ∧ u.z = decide (p.n % 16 = 0) := fun B h5 =>
    WP.mono (cmp5_ok (by omega_arith) h5) fun u ⟨z, g, _, sp, rd, wr⟩ =>
      ⟨⟨B.env.keep (fun r _ => by rw [g]) sp rd wr, by rw [g, B.r4], by rw [g, B.r5]⟩, z⟩
  refine rel_seq (rel_env C₁.env C₂.env [.r4, .r5] (by simp [C₁.r4, C₂.r4, C₁.r5, C₂.r5]) crypt5_check)
    (wC C₁ r5₁) (wC C₂ r5₂) fun c₁ c₂ ⟨D₁, cz₁⟩ ⟨D₂, cz₂⟩ => ?_
  refine rel_ite (eval_eq' cz₁) (eval_eq' cz₂) (fun _ => rel_skip) (fun _ => ?_)
  refine rel_seq (tag_rel L D₁.env D₂.env (o := 176) (by decide)) (tag_ok L D₁.env (o := 176) (by decide))
    (tag_ok L D₂.env (o := 176) (by decide)) fun z₁ z₂ T₁ T₂ => ?_
  exact rel_env T₁.env T₂.env [.r4, .r5] (by simp [T₁.r4, T₂.r4, T₁.r5, T₂.r5, D₁.r4, D₂.r4, D₁.r5, D₂.r5])
    cryptTailRest_check

/-! ## The functions -/

theorem entry_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint [.r0, .r1, .r2, .r3] 20) (.block entry) h).isSome
    = true := ⟨_, by taint_decide⟩

theorem sealEnd_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 16)
    (.block (tagOut ++ Impl.AesGcm.Arm.restore)) h).isSome = true := ⟨_, by taint_decide⟩

theorem recv_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 16) (.block recv) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem openEnd_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 12)
    (.seq (.block cmp) (.seq mask (.block Impl.AesGcm.Arm.restore))) h).isSome = true := ⟨_, by taint_decide⟩

/-- The public arguments of two states with the same public data. -/
theorem prmOf_eq {σ₁ σ₂ : State} (h : onePub σ₁ σ₂) : prmOf σ₁ = prmOf σ₂ := by
  obtain ⟨hsp, h0, h1, h2, h3, ha⟩ := h
  simp only [prmOf, h0, h1, h2, h3, hsp, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide),
    ha 4 (by decide)]

/-- The entry, in two runs with the same public arguments. -/
theorem entry_rel {σ₁ σ₂ : State} (L₁ : Lay (prmOf σ₁)) (P₁ : Perm (prmOf σ₁) σ₁) (L₂ : Lay (prmOf σ₂))
    (P₂ : Perm (prmOf σ₂) σ₂) (h : onePub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have hw : ∀ {σ : State}, Lay (prmOf σ) → Perm (prmOf σ) σ → σ.sp.toNat + 20 ≤ 2 ^ 32 ∧
      ∀ r ∈ σ.wr, Region.Disjoint ⟨State.addr σ.sp, 20⟩ r := fun L P => ⟨L.spf, P.argw⟩
  obtain ⟨hsp, h0, h1, h2, h3, ha⟩ := h
  exact rel_arg _ 20 (by simp [h0, h1, h2, h3]) hsp (hw L₁ P₁) (hw L₂ P₂)
    (argMem_of (j := 5) hsp L₁.spf fun i hi => ha i hi) entry_check

/-- After the entry, what a run keeps. -/
theorem PR.entry {s s₁ : State} (L : Lay (prmOf s)) (En : Entered s s₁) : PR (prmOf s) s₁ :=
  ⟨En.env, (args_of s).frame L En.frame (by disj_tac L)⟩

theorem seal_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa sealArm.pre sealArm.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁, -⟩ := args_of_seal h₁
  obtain ⟨L₂, P₂, -⟩ := args_of_seal h₂
  have e := prmOf_eq hp
  refine rel_seq (entry_rel L P₁ L₂ P₂ hp) (entry_ok L P₁) (entry_ok L₂ P₂) fun τ₁ τ₂ En₁ En₂ => ?_
  have R₁ := PR.entry L En₁
  have R₂ := PR.entry L₂ En₂
  rw [← e] at R₂
  refine rel_seq (keys_rel L R₁.env R₂.env) (keys_ok L R₁.env) (keys_ok L R₂.env) fun a₁ a₂ K₁ K₂ => ?_
  have S₁ : PR (prmOf σ₁) a₁ := ⟨K₁.env, R₁.args.frame L K₁.frame (by disj_tac L)⟩
  have S₂ : PR (prmOf σ₁) a₂ := ⟨K₂.env, R₂.args.frame L K₂.frame (by disj_tac L)⟩
  refine rel_seq (polyval_rel L S₁ S₂) (polyval_ok L S₁.env S₁.args K₁.hkey K₁.acc)
    (polyval_ok L S₂.env S₂.args K₂.hkey K₂.acc) fun b₁ b₂ P₁ P₂ => ?_
  have U₁ : PR (prmOf σ₁) b₁ := ⟨P₁.env, S₁.args.frame L P₁.frame (by disj_tac L)⟩
  have U₂ : PR (prmOf σ₁) b₂ := ⟨P₂.env, S₂.args.frame L P₂.frame (by disj_tac L)⟩
  refine rel_seq (tag_rel L U₁.env U₂.env (o := 0) (by decide)) (tag_ok L U₁.env (o := 0) (by decide))
    (tag_ok L U₂.env (o := 0) (by decide)) fun c₁ c₂ T₁ T₂ => ?_
  have V₁ : PR (prmOf σ₁) c₁ := ⟨T₁.env, U₁.args.frame L T₁.frame (by disj_tac L)⟩
  have V₂ : PR (prmOf σ₁) c₂ := ⟨T₂.env, U₂.args.frame L T₂.frame (by disj_tac L)⟩
  exact rel_seq (crypt_rel L V₁ V₂) (crypt_ok L V₁.env V₁.args) (crypt_ok L V₂.env V₂.args)
    fun d₁ d₂ C₁ C₂ => rel_envArg16 L C₁.env C₂.env (V₁.args.frame L C₁.frame (by disj_tac L))
      (V₂.args.frame L C₂.frame (by disj_tac L)) [] (by simp) sealEnd_check

theorem open_ct [VG.Proof.Gcm.Arm.GhashLaw] : ConstantTime isa openArm.pre openArm.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hp => ?_
  obtain ⟨L, P₁⟩ := args_of_open h₁
  obtain ⟨L₂, P₂⟩ := args_of_open h₂
  have e := prmOf_eq hp
  refine rel_seq (entry_rel L P₁ L₂ P₂ hp) (entry_ok L P₁) (entry_ok L₂ P₂) fun τ₁ τ₂ En₁ En₂ => ?_
  have R₀₁ := PR.entry L En₁
  have R₀₂ := PR.entry L₂ En₂
  rw [← e] at R₀₂
  have wr : ∀ {τ : State}, PR (prmOf σ₁) τ → WP isa (.block recv) τ (PR (prmOf σ₁)) := fun {τ} R => by
    obtain ⟨t, run, fR, -, ho, sp, rd, wr⟩ := recv_ok L R.env R.args
    have fR' : Frame [⟨State.addr (prmOf σ₁).W + BitVec.ofNat 64 0, 16⟩] τ.mem t.mem := by
      rw [BitVec.add_zero]; exact fR
    exact WP.of_runBlock ⟨t, run, R.env.of_others ho sp rd wr, R.args.frame L fR' (by disj_tac L)⟩
  refine rel_seq (rel_envArg16 L R₀₁.env R₀₂.env R₀₁.args R₀₂.args [] (by simp) recv_check) (wr R₀₁) (wr R₀₂)
    fun ρ₁ ρ₂ R₁ R₂ => ?_
  refine rel_seq (keys_rel L R₁.env R₂.env) (keys_ok L R₁.env) (keys_ok L R₂.env) fun a₁ a₂ K₁ K₂ => ?_
  have S₁ : PR (prmOf σ₁) a₁ := ⟨K₁.env, R₁.args.frame L K₁.frame (by disj_tac L)⟩
  have S₂ : PR (prmOf σ₁) a₂ := ⟨K₂.env, R₂.args.frame L K₂.frame (by disj_tac L)⟩
  refine rel_seq (crypt_rel L S₁ S₂) (crypt_ok L S₁.env S₁.args) (crypt_ok L S₂.env S₂.args)
    fun b₁ b₂ C₁ C₂ => ?_
  have U₁ : PR (prmOf σ₁) b₁ := ⟨C₁.env, S₁.args.frame L C₁.frame (by disj_tac L)⟩
  have U₂ : PR (prmOf σ₁) b₂ := ⟨C₂.env, S₂.args.frame L C₂.frame (by disj_tac L)⟩
  have hG : ∀ {σ τ : State}, KeysPost (prmOf σ₁) σ τ → ∀ {u : State}, CryptPost (prmOf σ₁) τ u →
      Spec.Gcm.blockAt u.mem (State.addr (prmOf σ₁).W + BitVec.ofNat 64 64) =
        GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt u.mem (State.addr (prmOf σ₁).W + BitVec.ofNat 64 16) 16)) ∧
      Spec.Gcm.blockAt u.mem (State.addr (prmOf σ₁).W + BitVec.ofNat 64 80) = 0 := by
    intro _ _ K _ C
    rw [Proof.AesGcm.Arm.blockAt_frame C.frame (by disj_tac L), K.hkey,
      Proof.AesGcm.Arm.blockAt_frame C.frame (by disj_tac L), K.acc,
      bytesAt_keep C.frame (by disj_tac L) (by decide)]
    exact ⟨rfl, rfl⟩
  refine rel_seq (polyval_rel L U₁ U₂) (polyval_ok L U₁.env U₁.args (hG K₁ C₁).1 (hG K₁ C₁).2)
    (polyval_ok L U₂.env U₂.args (hG K₂ C₂).1 (hG K₂ C₂).2) fun c₁ c₂ P₁ P₂ => ?_
  have V₁ : PR (prmOf σ₁) c₁ := ⟨P₁.env, U₁.args.frame L P₁.frame (by disj_tac L)⟩
  have V₂ : PR (prmOf σ₁) c₂ := ⟨P₂.env, U₂.args.frame L P₂.frame (by disj_tac L)⟩
  refine rel_seq (tag_rel L V₁.env V₂.env (o := 176) (by decide)) (tag_ok L V₁.env (o := 176) (by decide))
    (tag_ok L V₂.env (o := 176) (by decide)) fun d₁ d₂ T₁ T₂ => ?_
  exact rel_envArg L T₁.env T₂.env (V₁.args.frame L T₁.frame (by disj_tac L))
    (V₂.args.frame L T₂.frame (by disj_tac L)) [] (by simp) openEnd_check

end VG.Proof.AesGcmSiv.Arm

end

end

/-!
# AES-GCM-SIV on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, with the tag input computed with GHASH equal to the RFC's
(`tagInput_eq`, from `Proof.GcmSiv.Polyval`, imported here only so that the
other proofs need not import its algebra), a state satisfying each
precondition, and the shared contracts of `Spec/GcmSiv/Contract.lean` with
the working space as a last argument (`Proof/AesGcmSiv/Scratch.lean`, 470
words), with 8 bytes of stack: each call of `vg_aes_ctr32` or `vg_ghash`
pushes two words. The last section allocates the working space.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.Arm

open VG VG.Arm VG.Impl.AesGcmSiv.Arm
open VG.Proof.AesGcm.Arm (bel arg args)

/-- RFC 8452 Appendix A: POLYVAL with `H` is GHASH with `H · x`. -/
theorem tagInput_eq : TagInputEq := fun a n pt d => by
  rw [GcmSiv.tagInput_eq, Spec.GcmSiv.polyval, GcmSiv.Polyval.polyvalFrom_eq]
  rfl

/-- `seal`'s state satisfying the precondition: no additional data, no
data, the tag at `0x4000` and `work` at `0x5000`, their addresses the stack
arguments at `sp + 12` and `sp + 16`. -/
def sealSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x800D then 0x40 else if a = 0x8011 then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8000, 20⟩]
  wr := [⟨0, 0⟩, ⟨0x4000, 16⟩, ⟨0x5000, 3760⟩]

/-- `open`'s: as `seal`'s, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x8000, 20⟩],
                 wr := [⟨0, 0⟩, ⟨0x5000, 3760⟩] }

theorem seal_verified [VG.Proof.Gcm.Arm.GhashLaw] : Verified Arm.target «seal» (Proof.AesGcmSiv.sealScratchContract Arm.abi 470 8) :=
  Verified.of_correct (fun _ hs => seal_wp tagInput_eq hs) seal_ct (by
    sig_implies [Proof.AesGcmSiv.sealScratchContract, Proof.AesGcmSiv.sealScratchSig, Spec.GcmSiv.sealPre,
      Proof.AesGcmSiv.sealRoundsPost, sealArm, sealPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified [VG.Proof.Gcm.Arm.GhashLaw] : Verified Arm.target «open» (Proof.AesGcmSiv.openScratchContract Arm.abi 470 8) :=
  Verified.of_correct (fun _ hs => open_wp tagInput_eq hs) open_ct
    { pre := by sig_implies_pre [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
        openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr]
      -- `h` and the goal match on the same outcome of `decryptWith` with
      -- different matchers (`openPost`'s and `openContract`'s): split on it
      -- rather than have `exact h` unfold both to unify them.
      post := by
        intro s s' _ h
        sig_post [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
          openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
        sig_reduce [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
          Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
          openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr] at h
        have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
        simp only [e]
        intro _
        split at h <;> rename_i heq <;> rw [heq] <;> exact h
      pub := by sig_implies_pub [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
        openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr]
      sat := by sig_implies_sat [Proof.AesGcmSiv.openScratchContract, Proof.AesGcmSiv.openScratchSig,
        Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, openArm, openResult, openPost,
        openPre, oneLay, onePub, rounds, bel, arg, args, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr] [openSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackScratch`): their working space is their fifth stack
argument, after `aad_len`, `data`, `len` and `tag`, so the frame of 3792
bytes holds a copy of those four words, the address of the working space,
the saved `lr` and the working space (3784 bytes, rounded up to an
immediate `sub` can encode). The copies are read only where the pre- and
postconditions read the buffers, and `open`'s leak, whether it succeeds,
reads only its buffers (`Proof/AesGcmSiv/Scratch.lean`).
-/

/-- A state satisfying `vg_aes_gcm_siv_seal`'s precondition, without the
working space: its four words of stack arguments at `0x8000`. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0, 0⟩, ⟨0x4000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesGcmSiv.sealRoundsContract Arm.abi 3800).pre s := by
  implies_sat [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre, Proof.AesGcmSiv.sealRoundsPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [sealFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 3792 4 «seal»)
      (Proof.AesGcmSiv.sealRoundsContract Arm.abi 3800) :=
  Arm.Verified.stackScratch (sig := Spec.GcmSiv.sealSig) (nm := "work") (e := .u64)
    (n := 470) (pre := Spec.GcmSiv.sealPre Arm.abi.ptrBits)
    (post := Proof.AesGcmSiv.sealRoundsPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (m := 4) seal_verified (by decide) (by decide) (by decide) (by decide)
    (sealPre_local _) (sealPost_local _)
    (fun vs mm m₁ m₂ r hl _ => sealPostOut_local _ vs mm m₁ m₂ r hl) sealFrameSat_pre

/-- A state satisfying `vg_aes_gcm_siv_open`'s precondition, without the
working space: its four words of stack arguments at `0x8000`. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 12⟩, ⟨0x3000, 0⟩, ⟨0x4000, 16⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesGcmSiv.openRoundsContract Arm.abi 3800).pre s := by
  implies_sat [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre, Proof.AesGcmSiv.openRoundsPost,
    Spec.GcmSiv.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [openFrameSat, sealSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using openFrameSat

theorem open_framed [VG.Proof.Gcm.Arm.GhashLaw] :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 3792 4 «open»)
      (Proof.AesGcmSiv.openRoundsContract Arm.abi 3800) :=
  Arm.Verified.stackScratch (sig := Spec.GcmSiv.openSig) (nm := "work") (e := .u64)
    (n := 470) (pre := Spec.GcmSiv.openPre Arm.abi.ptrBits)
    (post := Proof.AesGcmSiv.openRoundsPost Arm.abi.ptrBits) (wa := true) (stack := 8)
    (leak := some (Spec.GcmSiv.openLeak Arm.abi.ptrBits))
    (m := 4) (Proof.AesGcmSiv.Verified.of_openScratch open_verified) (by decide) (by decide) (by decide) (by decide)
    (openPre_local _) (openPost_local _)
    (fun vs mm m₁ m₂ r hl _ => openPostOut_local _ vs mm m₁ m₂ r hl) openFrameSat_pre
    (hleak := openLeak_local _)

end VG.Proof.AesGcmSiv.Arm

/-!
## Without secret residue

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` keep their working space in
a frame within the stack their contracts reserve and make no indirect call
(evaluated by `lit_decide`), and their postconditions read the memory on
return only within their buffers (`Arm.Scrub.PostOut`, as on PPC64LE,
`Proof/AesGcmSiv/PPC64LE/Scrub.lean`). Each is emitted followed by a wipe
of that stack and by instructions that set the registers a callee may
change, but the result, and the flags to constants (`Impl.AesGcmSiv.Arm.Fn`), and `Fn` below states
that it returns without secret residue (`Arm.Scrub.verifiedScrubbedF`), which
is what its registration binds.

That stack is a frame of the model (`Arm.Scrub.FrameOk`): the 3800 bytes
their proofs are stated with are not, and they are stated with 3808
(`Arm.Scrub.Verified.stack_le`), whose preconditions the same states as
before satisfy.
-/

namespace VG.Proof.AesGcmSiv.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Aes.ScrubLocal VG.Impl.AesGcmSiv.Arm

theorem len_le (x : BitVec 64) : (BitVec.setWidth 32 x).toNat ≤ x.toNat := by
  rw [BitVec.toNat_setWidth]; exact Nat.mod_le _ _

/-! ## Postconditions -/

theorem sealOut (stack : Nat) :
    PostOut (Spec.GcmSiv.sealContract Arm.abi stack) (Spec.GcmSiv.sealSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [schedule, rounds, nonce, aad, aadLen, data, len, tag], _ =>
      simp only [Spec.GcmSiv.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr, ArgWord.int 32,
        ArgWord.addr, ArgWord.int 32, ArgWord.addr] (Spec.GcmSiv.sealPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr, ArgWord.int 32,
        ArgWord.addr, ArgWord.int 32, ArgWord.addr] (Spec.GcmSiv.sealPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.GcmSiv.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hl hk
      rw [h key hl hk, bytesAt_of0 hb.2.2.2.1 (len_le _), bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.GcmSiv.openContract Arm.abi stack) (Spec.GcmSiv.openSig.retBits 32) := by
  -- The postcondition is a `match` on a decryption: prove the locality
  -- by intros, so that no expected type of a `fun` is reduced to it.
  refine postOut_of_local ScrubAbi.plain ?_
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [schedule, rounds, nonce, aad, aadLen, data, len, tag], _ =>
    simp only [Spec.GcmSiv.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 32, ArgWord.addr] (Spec.GcmSiv.openPost 32) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.addr, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 32, ArgWord.addr] (Spec.GcmSiv.openPost 32) _ m m₂ r
    dsimp only [Curry.apply, Spec.GcmSiv.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    rw [bytesAt_of0 (n := (BitVec.setWidth 32 len).toNat) hb.2.2.2.1 (len_le _)]
    exact @h

/-! ## The stack, rounded up to a frame of the model -/

theorem frameOk_3808 : FrameOk 3808 := by decide

theorem sealSat : ∃ s, (Proof.AesGcmSiv.sealRoundsContract Arm.abi 3808).pre s := by
  implies_sat [Proof.AesGcmSiv.sealRoundsContract, Spec.GcmSiv.sealSig, Spec.GcmSiv.sealPre,
    Proof.AesGcmSiv.sealRoundsPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [Proof.AesGcmSiv.Arm.sealFrameSat, Proof.AesGcmSiv.Arm.sealSat, Arm.stackArg, Arm.stackArgAddr,
      Mem.readW, Mem.read]
    using Proof.AesGcmSiv.Arm.sealFrameSat

theorem openSat : ∃ s, (Proof.AesGcmSiv.openRoundsContract Arm.abi 3808).pre s := by
  implies_sat [Proof.AesGcmSiv.openRoundsContract, Spec.GcmSiv.openSig, Spec.GcmSiv.openPre,
    Proof.AesGcmSiv.openRoundsPost, Spec.GcmSiv.openLeak, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr]
    [Proof.AesGcmSiv.Arm.openFrameSat, Proof.AesGcmSiv.Arm.sealSat, Arm.stackArg, Arm.stackArgAddr,
      Mem.readW, Mem.read]
    using Proof.AesGcmSiv.Arm.openFrameSat

/-! ## The code: its frames, and no indirect call -/

theorem seal_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 3792 4 «seal») 3808 := by
  lit_decide

theorem open_code :
    CodeOk (Impl.StackScratch.Arm.withStackScratch 3792 4 «open») 3808 := by
  lit_decide

end VG.Proof.AesGcmSiv.Arm.Scrub

namespace VG.Proof.AesGcmSiv.Arm.Fn

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack VG.Proof.Aes.ScrubLocal VG.Impl.AesGcmSiv.Arm


/-- `vg_aes_gcm_siv_seal`. -/
theorem «seal» [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcmSiv.Arm.Fn.«seal» (Spec.GcmSiv.sealContract abi 3808) 0 :=
  verifiedScrubbedF (api := Spec.GcmSiv.sealApi)
    { code := Impl.StackScratch.Arm.withStackScratch 3792 4 Impl.AesGcmSiv.Arm.«seal»
      verified := Proof.AesGcmSiv.seal_keyed (Verified.stack_le (by decide) Proof.AesGcmSiv.Arm.seal_framed
        Scrub.sealSat : Verified Arm.target _ (Proof.AesGcmSiv.sealRoundsContract Arm.abi 3808)) }
    (Scrub.sealOut _) (scrubSideF_of Scrub.seal_code Scrub.frameOk_3808 _)

/-- `vg_aes_gcm_siv_open`. -/
theorem «open» [VG.Proof.Gcm.Arm.GhashLaw] : VerifiedScrubbed target Impl.AesGcmSiv.Arm.Fn.«open» (Spec.GcmSiv.openContract abi 3808) 32 :=
  verifiedScrubbedF (api := Spec.GcmSiv.openApi)
    { code := Impl.StackScratch.Arm.withStackScratch 3792 4 Impl.AesGcmSiv.Arm.«open»
      verified := Proof.AesGcmSiv.open_keyed (Verified.stack_le (by decide) Proof.AesGcmSiv.Arm.open_framed
        Scrub.openSat : Verified Arm.target _ (Proof.AesGcmSiv.openRoundsContract Arm.abi 3808)) }
    (Scrub.openOut _) (scrubSideF_of Scrub.open_code Scrub.frameOk_3808 _)

end VG.Proof.AesGcmSiv.Arm.Fn
