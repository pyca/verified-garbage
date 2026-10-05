import VerifiedGarbage.Proof.AesOcb.Arm.Open
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-OCB on ARMv7: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2`) piece by piece, as AES-GCM-SIV's
do (`Proof.AesGcmSiv.Arm`): the code between calls by the taint analysis,
from the registers that hold the public arguments in both runs (`Env`,
`rel_env`), those the pieces pin to the same values, and the stack
arguments, which both runs hold and nothing writes (`Args`, `rel_envArg`);
each call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` by its
proof, with the same arguments in both runs (`rel_blk`, `encOne_rel`); a
branch on a flag both runs agree on (`rel_ite`); a loop whose condition both
runs agree on (`rel_loop`); and the next piece from the states the
correctness proofs describe (`rel_seq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Impl.AesGcm.Arm (imm addI)

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

/-- The last piece of a loop's body, with what correctness says of each run's
final state. -/
theorem rel_wpQ {c : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h : RelCT isa (Eq2 σ₁ σ₂) c TT) (w₁ : WP isa c σ₁ F₁) (w₂ : WP isa c σ₂ F₂)
    (hq : ∀ a b, F₁ a → F₂ b → Q a b) : RelCT isa (Eq2 σ₁ σ₂) c Q :=
  (h.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono
    (fun _ _ h => h) fun a b h => hq a b h.2.1 h.2.2

/-- Then, towards any relation of the final states. -/
theorem rel_seqQ {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop} {Q : State → State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ Q) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) Q := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The public arguments -/

theorem Env.agree {p : Prm} {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) :
    ∀ r ∈ envRegs, τ₁.gpr r = τ₂.gpr r := by
  intro r hr
  simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
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
    (A₂ : Args p s₂.mem) : ∀ k < 24, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  refine argMem_of (j := 6) (E₁.sp_eq E₂) (by rw [E₁.sp]; have := L.spf; omega) fun i hi => ?_
  have e : ∀ {s : State}, Env p s → Args p s.mem → stackArg s i =
      [p.A, BitVec.ofNat 32 p.al, p.D, BitVec.ofNat 32 p.n, p.T, BitVec.ofNat 32 p.tl].getD i 0 := fun {s} E A => by
    rw [Proof.AesGcm.Arm.stackArg_eq, E.sp]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.a0
    · exact A.a4
    · exact A.a8
    · exact A.a12
    · exact A.a16
    · exact A.a20
  rw [e E₁ A₁, e E₂ A₂]

/-- Code the taint analysis checks, from the registers holding the public
arguments, the registers `rs` the two runs agree on, and the first six
stack arguments. -/
theorem rel_envArg {c : Prog isa} {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (A₁ : Args p τ₁.mem) (A₂ : Args p τ₂.mem) (rs : List Reg)
    (hr : ∀ r ∈ rs, τ₁.gpr r = τ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs rs) 24) c h).isSome = true) :
    RelCT isa (Eq2 τ₁ τ₂) c TT := by
  have spf := L.spf
  have hw : ∀ {τ : State}, Env p τ →
      τ.sp.toNat + 24 ≤ 2 ^ 32 ∧ ∀ r ∈ τ.wr, Region.Disjoint ⟨State.addr τ.sp, 24⟩ r := fun E =>
    ⟨by rw [E.sp]; omega, fun r hr => by rw [E.sp]; exact (E.perm.argw r hr).sub_left (Region.sub_prefix (by decide))⟩
  exact rel_arg (pubRegs rs) 24 (fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact E₁.agree E₂ r h
    · exact hr r h) (E₁.sp_eq E₂) (hw E₁) (hw E₂) (argByte_eq L E₁ E₂ A₁ A₂) hc

/-! ## The calls -/

/-- A call of `F` in two runs, with the same arguments. -/
theorem rel_blk (F : BlkFn) {σ₁ σ₂ : State} {K D S : BitVec 32} {R n : Nat} (h₁ : BlkCall σ₁ K D S R n)
    (h₂ : BlkCall σ₂ K D S R n) (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (blkFrame F) TT :=
  blk_rel F fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨K, D, S, R, n, h₁, h₂, hsp⟩

/-! ## What a run keeps -/

/-- Then, from what every execution of the first piece leaves. -/
theorem rel_seqX {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : ∀ t τ, Exec isa c₁ σ₁ t τ → F₁ τ)
    (w₂ : ∀ t τ, Exec isa c₁ σ₂ t τ → F₂ τ)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => ?_) ?_
  · obtain ⟨rfl, rfl⟩ := hp
    exact ⟨(h₁ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, w₁ _ _ e₁, w₂ _ _ e₂⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- What every execution leaves, from a correctness proof. -/
theorem exec_of_wp {c : Prog isa} {σ : State} {F : State → Prop} (w : WP isa c σ F) :
    ∀ t τ, Exec isa c σ t τ → F τ := fun _ _ e => by
  obtain ⟨_, _, e', hf⟩ := w
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hf

/-- The environment, after code that writes none of its registers. -/
theorem Env.exec {p : Prm} {c : Prog isa} {τ τ' : State} {t : List Leak} (E : Env p τ) (h : Exec isa c τ t τ')
    (h9 : ∀ i ∈ instrs c, dstOf i ≠ some .r9) (h10 : ∀ i ∈ instrs c, dstOf i ≠ some .r10)
    (h11 : ∀ i ∈ instrs c, dstOf i ≠ some .r11) : Env p τ' :=
  have ⟨rd, wr, sp⟩ := Exec.rdwr h
  ⟨by rw [Exec.gpr h9 h, E.r9], by rw [Exec.gpr h10 h, E.r10], by rw [Exec.gpr h11 h, E.r11], by rw [sp, E.sp],
    E.perm.of_eq rd wr⟩

/-- The stack arguments, after code without frames. -/
theorem Args.exec {p : Prm} (L : Lay p) {c : Prog isa} {τ τ' : State} {t : List Leak} (E : Env p τ)
    (A : Args p τ.mem) (h : Exec isa c τ t τ') (hn : c.noFrames = true) : Args p τ'.mem :=
  A.frame L (Exec.regions h hn).2.2.2 fun r hr => E.perm.argw r hr

/-- What every execution of frame-free code that keeps the environment's
registers leaves: the environment, the stack arguments, and the registers in
`rs` it does not write. -/
structure Kept (p : Prm) (rs : List Reg) (τ τ' : State) : Prop where
  env : Env p τ'
  args : Args p τ.mem → Args p τ'.mem
  gpr : ∀ r ∈ rs, τ'.gpr r = τ.gpr r

theorem kept_of {p : Prm} (L : Lay p) {c : Prog isa} {τ : State} (E : Env p τ) (rs : List Reg)
    (hk : ∀ r ∈ envRegs ++ rs, ∀ i ∈ instrs c, dstOf i ≠ some r) (hn : c.noFrames = true)
    (hc : c.noCalls = true) : ∀ t τ', Exec isa c τ t τ' → Kept p rs τ τ' := fun _ _ h =>
  ⟨E.exec h (hk _ (by simp)) (hk _ (by simp)) (hk _ (by simp)), fun A => A.exec L E h hn,
    fun r hr => Exec.gpr (hk r (List.mem_append_right _ hr)) h (.inl hc)⟩

/-! ## The calls -/

/-- `ENCIPHER` of the block at `W + d`, set up. -/
theorem encOne_pre {p : Prm} (L : Lay p) {τ : State} (E : Env p τ) {d : Nat} (hd : d + 16 ≤ 512)
    (he : encodable (BitVec.ofNat 32 d) = true) :
    WP isa (.block (callArgs ++ ([addI .r2 .r11 d, .mov .r3 (imm 1)] : List Instr))) τ fun t =>
      BlkCall t p.K (p.W + BitVec.ofNat 32 d) (p.W + BitVec.ofNat 32 scrO) p.R 1 ∧ Env p t := by
  have fw := L.ww
  have ed : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d := L.wA (by omega)
  refine WP.of_runBlock ⟨_, by orun [callArgs, E.r9, E.r10, E.r11, he], ?_⟩
  have E' := E.of_others (s' := ((((τ.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 (p.W + BitVec.ofNat 32 d)).setReg .r3 (BitVec.ofNat 32 1))
    (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac) (by rfl) (by rfl) (by rfl)
  exact ⟨blkCall_of L E' (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
    (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by omega)]; omega)
    (by rw [ed]; exact E.perm.wC (by omega)) (by rw [ed]; exact L.k_w' (by omega))
    (by rw [ed]; exact L.w_w (.inl (by simp only [scrO]; omega)) (by omega) (by decide))
    (by rw [ed]; exact L.bw' (by omega)), E'⟩

theorem encOneA_check {d : Nat} (hd : d = tmpO ∨ d = bufO) : ∃ h, (VG.Taint.check VG.Arm.taint
    (VG.Arm.Taint.ofRegs (pubRegs [])) (.block (callArgs ++ ([addI .r2 .r11 d, .mov .r3 (imm 1)] : List Instr))) h).isSome
      = true := by
  rcases hd with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `ENCIPHER` of the block at `W + d`, in two runs with the same public
arguments. -/
theorem encOne_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) {d : Nat}
    (hd : d = tmpO ∨ d = bufO) : RelCT isa (Eq2 τ₁ τ₂) (encOne d) TT := by
  have hd' : d + 16 ≤ 512 := by rcases hd with rfl | rfl <;> decide
  have he : encodable (BitVec.ofNat 32 d) = true := by rcases hd with rfl | rfl <;> decide
  exact rel_seq (rel_env E₁ E₂ [] (by simp) (encOneA_check hd)) (encOne_pre L E₁ hd' he) (encOne_pre L E₂ hd' he)
    fun a b A B => rel_blk encF A.1 B.1 (A.2.sp_eq B.2)

end VG.Proof.AesOcb.Arm
