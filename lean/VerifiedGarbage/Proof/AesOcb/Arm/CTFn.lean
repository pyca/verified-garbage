module

public import VerifiedGarbage.Proof.AesOcb.Arm.Body
import VerifiedGarbage.Proof.AesOcb.Arm.RestTag
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesOcb.Arm.Body
meta import VerifiedGarbage.Proof.AesOcb.Arm.RestTag
meta import VerifiedGarbage.Proof.Ocb.State
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Impl.AesOcb.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.TCB.Arm.Isa
import Batteries.Logic
import VerifiedGarbage.Proof.Aes.Ct32.Layers
import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesOcb.Arm.Hash
public import VerifiedGarbage.Proof.AesOcb.Arm.HashChunk
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.Ocb.Contract
meta import Batteries.Logic
meta import VerifiedGarbage.Proof.Aes.Ct32.Layers
meta import VerifiedGarbage.Proof.AesGcm.Arm.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.Arm.Ghash1
meta import VerifiedGarbage.Proof.AesGcm.Arm.Loops
meta import VerifiedGarbage.Proof.AesOcb.Arm.Hash
meta import VerifiedGarbage.Proof.AesOcb.Arm.HashChunk
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Mem
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesGcm.Arm.Run
meta import VerifiedGarbage.Proof.AesGcm.Arm.Run
import VerifiedGarbage.Proof.Gcm.Stream
meta import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.AesOcb.Arm.Env
import VerifiedGarbage.Proof.Ocb.Bytes
public import VerifiedGarbage.Proof.AesGcm.Arm.Fn
import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.AesOcb.Arm.Env
meta import VerifiedGarbage.Proof.Ocb.Bytes
meta import VerifiedGarbage.Proof.AesGcm.Arm.Fn
meta import VerifiedGarbage.Proof.AesGcm.Arm.Entry
meta import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.AesGcm.Arm.Env
meta import VerifiedGarbage.Proof.AesGcm.Arm.Env
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.AesOcb.Arm.Callee
import VerifiedGarbage.Proof.AesOcb.Arm.Calls
meta import VerifiedGarbage.Proof.AesOcb.Arm.Callee
meta import VerifiedGarbage.Proof.AesOcb.Arm.Calls

/-! ### `AesOcb.Arm.CTBase`, which only this module used -/

section

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

@[expose] public section

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
  refine argMem_of (j := 6) (E₁.sp_eq E₂) (by rw [E₁.sp]; have := L.spf; omega_using [this]) fun i hi => ?_
  have e : ∀ {s : State}, Env p s → Args p s.mem → stackArg s i =
      [p.A, BitVec.ofNat 32 p.al, p.D, BitVec.ofNat 32 p.n, p.T, BitVec.ofNat 32 p.tl].getD i 0 := fun {s} E A => by
    rw [Proof.AesGcm.Arm.stackArg_eq, E.sp]
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
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
    ⟨by rw [E.sp]; omega_using [spf], fun r hr => by rw [E.sp]; exact (E.perm.argw r hr).sub_left (Region.sub_prefix (by decide))⟩
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
    (h9 : ∀ i ∈ instrs c, clobbers i .r9 = false) (h10 : ∀ i ∈ instrs c, clobbers i .r10 = false)
    (h11 : ∀ i ∈ instrs c, clobbers i .r11 = false) : Env p τ' :=
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
    (hk : ∀ r ∈ envRegs ++ rs, ∀ i ∈ instrs c, clobbers i r = false) (hn : c.noFrames = true)
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
  have ed : State.addr (p.W + BitVec.ofNat 32 d) = State.addr p.W + BitVec.ofNat 64 d := L.wA (by omega_using [hd])
  refine WP.of_runBlock ⟨_, by orun [callArgs, E.r9, E.r10, E.r11, he], ?_⟩
  have E' := E.of_others (s' := ((((τ.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 (p.W + BitVec.ofNat 32 d)).setReg .r3 (BitVec.ofNat 32 1))
    (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac) (by rfl) (by rfl) (by rfl)
  exact ⟨blkCall_of L E' (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
    (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by rw [L.wN (by omega_using [hd])]; omega_using [hd, fw])
    (by rw [ed]; exact E.perm.wC (by omega_using [hd])) (by rw [ed]; exact L.k_w' (by omega_using [hd]))
    (by rw [ed]; exact L.w_w (.inl (by simp only [scrO]; omega_using [hd])) (by omega_using [hd]) (by decide))
    (by rw [ed]; exact L.bw' (by omega_using [hd])), E'⟩

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

end

end

/-! ### `AesOcb.Arm.CTBody`, which only this module used -/

section

/-!
# AES-OCB on ARMv7: the data and the tag in two runs

Untrusted: everything here is checked by Lean. `body` and `tag d`, in two
runs with the same public arguments: the passes over the whole blocks and
the rest by the taint analysis, from the registers holding the data's
pointer, its blocks and the block index, the same in both runs; the calls of
`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` with the same arguments
in both runs (`body_rel`, `tag_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (offAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0 and15 ofNat_sub32)

/-! ## The whole blocks -/

theorem passStart_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r7, .r8]))
    (.block passStart) h).isSome = true := ⟨_, by taint_decide⟩

theorem pass_check {b : List Instr} (hb : b = addCk ++ xorOfs ∨ b = xorOfs ∨ b = xorOfs ++ addCk) :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5, .r6, .r7, .r8])) (pass b) h).isSome =
      true := by
  rcases hb with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem wholeArgs_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (callArgs ++ ([.mov .r2 (.reg .r8), .mov .r3 (.reg .r7)] : List Instr))) h).isSome = true := ⟨_, by taint_decide⟩

theorem wholeTail_check {b : List Instr} (hb : b = addCk ++ xorOfs ∨ b = xorOfs ∨ b = xorOfs ++ addCk) :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r7, .r8]))
      (.seq (.block (copy16 o0O ofsO ++ passStart)) (pass b)) h).isSome = true := by
  rcases hb with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem pass_kept {p : Prm} (L : Lay p) {τ : State} (E : Env p τ) {b : List Instr}
    (hb : b = addCk ++ xorOfs ∨ b = xorOfs ∨ b = xorOfs ++ addCk) :
    ∀ t τ', Exec isa (pass b) τ t τ' → Kept p [.r7, .r8] τ τ' := by
  rcases hb with rfl | rfl | rfl <;>
    exact kept_of L E [.r7, .r8] (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The call between the passes, set up. -/
theorem wholeArgs_ok {p : Prm} (L : Lay p) {τ : State} (E : Env p τ) {m : Nat} (hmn : 16 * m ≤ p.n)
    (h8 : τ.gpr .r8 = p.D) (h7 : τ.gpr .r7 = BitVec.ofNat 32 m) :
    WP isa (.block (callArgs ++ ([.mov .r2 (.reg .r8), .mov .r3 (.reg .r7)] : List Instr))) τ fun t =>
      BlkCall t p.K p.D (p.W + BitVec.ofNat 32 scrO) p.R m ∧ Env p t ∧ t.gpr .r8 = p.D ∧
        t.gpr .r7 = BitVec.ofNat 32 m := by
  have fd := L.dw
  refine WP.of_runBlock ⟨_, by orun [callArgs, E.r9, E.r10, E.r11, h8, h7], ?_⟩
  have E' := E.of_others (s' := ((((τ.setReg .r0 p.K).setReg .r1 (BitVec.ofNat 32 p.R)).setReg .r12
    (p.W + BitVec.ofNat 32 scrO)).setReg .r2 p.D).setReg .r3 (BitVec.ofNat 32 m))
    (rs := [.r0, .r1, .r2, .r3, .r12]) (by others_tac) (by rfl) (by rfl) (by rfl)
  exact ⟨blkCall_of L E' (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by simp [gpr_setReg])
    (by simp [gpr_setReg]) (by simp [gpr_setReg]) (by omega_using [hmn, fd])
    (Proof.AesGcm.Arm.covers_prefix E.perm.d hmn) (L.k_d.sub_right (Region.sub_prefix hmn))
    ((L.d_w' (d := scrO) (k := 2048) (by decide)).sub_left (Region.sub_prefix hmn))
    (L.bd.sub_right (Region.sub_prefix hmn)), E', by simp [gpr_setReg, h8], by simp [gpr_setReg, h7]⟩

/-- The whole blocks, in two runs with the same public arguments. -/
theorem whole_rel (F : BlkFn) {pre post : List Instr}
    (hpre : pre = addCk ++ xorOfs ∨ pre = xorOfs ∨ pre = xorOfs ++ addCk)
    (hpost : post = addCk ++ xorOfs ∨ post = xorOfs ∨ post = xorOfs ++ addCk)
    {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) {m : Nat} (hmn : 16 * m ≤ p.n)
    (h8₁ : τ₁.gpr .r8 = p.D) (h8₂ : τ₂.gpr .r8 = p.D) (h7₁ : τ₁.gpr .r7 = BitVec.ofNat 32 m)
    (h7₂ : τ₂.gpr .r7 = BitVec.ofNat 32 m) : RelCT isa (Eq2 τ₁ τ₂) (whole (blkFrame F) pre post) TT := by
  unfold whole
  obtain ⟨s₁, run₁, r4₁, r5₁, r6₁, R₁⟩ := passStart_run h8₁ h7₁
  obtain ⟨s₂, run₂, r4₂, r5₂, r6₂, R₂⟩ := passStart_run h8₂ h7₂
  refine rel_seq (F₁ := (s₁ = ·)) (F₂ := (s₂ = ·)) (rel_env E₁ E₂ [.r7, .r8] (by simp [h7₁, h7₂, h8₁, h8₂])
    passStart_check) (WP.of_runBlock ⟨s₁, run₁, rfl⟩) (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun u₁ u₂ e₁ e₂ => ?_
  subst e₁ e₂
  have Es₁ : Env p s₁ := E₁.of_others R₁.gpr R₁.sp R₁.rd R₁.wr
  have Es₂ : Env p s₂ := E₂.of_others R₂.gpr R₂.sp R₂.rd R₂.wr
  have g₁ : ∀ r ∈ [Reg.r7, .r8], s₁.gpr r = τ₁.gpr r := fun r hr => R₁.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide)
  have g₂ : ∀ r ∈ [Reg.r7, .r8], s₂.gpr r = τ₂.gpr r := fun r hr => R₂.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> decide)
  refine rel_seqX (rel_env Es₁ Es₂ [.r4, .r5, .r6, .r7, .r8] (by
      simp [r4₁, r4₂, r5₁, r5₂, r6₁, r6₂, g₁ .r7 (by simp), g₂ .r7 (by simp), g₁ .r8 (by simp), g₂ .r8 (by simp),
        h7₁, h7₂, h8₁, h8₂]) (pass_check hpre))
    (pass_kept L Es₁ hpre) (pass_kept L Es₂ hpre) fun v₁ v₂ K₁ K₂ => ?_
  have h8v₁ : v₁.gpr .r8 = p.D := by rw [K₁.gpr _ (by simp), g₁ _ (by simp), h8₁]
  have h8v₂ : v₂.gpr .r8 = p.D := by rw [K₂.gpr _ (by simp), g₂ _ (by simp), h8₂]
  have h7v₁ : v₁.gpr .r7 = BitVec.ofNat 32 m := by rw [K₁.gpr _ (by simp), g₁ _ (by simp), h7₁]
  have h7v₂ : v₂.gpr .r7 = BitVec.ofNat 32 m := by rw [K₂.gpr _ (by simp), g₂ _ (by simp), h7₂]
  refine rel_seq (rel_env K₁.env K₂.env [] (by simp) wholeArgs_check) (wholeArgs_ok L K₁.env hmn h8v₁ h7v₁)
    (wholeArgs_ok L K₂.env hmn h8v₂ h7v₂) fun w₁ w₂ ⟨B₁, Ew₁, h8w₁, h7w₁⟩ ⟨B₂, Ew₂, h8w₂, h7w₂⟩ => ?_
  refine rel_seq (rel_blk F B₁ B₂ (Ew₁.sp_eq Ew₂)) (blk_call F B₁) (blk_call F B₂) fun x₁ x₂ C₁ C₂ => ?_
  exact rel_env (Ew₁.of_saved C₁.saved C₁.sp C₁.rd C₁.wr) (Ew₂.of_saved C₂.saved C₂.sp C₂.rd C₂.wr) [.r7, .r8]
    (by simp [C₁.saved .r7 (by decide) (by decide), C₂.saved .r7 (by decide) (by decide),
      C₁.saved .r8 (by decide) (by decide), C₂.saved .r8 (by decide) (by decide), h7w₁, h7w₂, h8w₁, h8w₂])
    (wholeTail_check hpost)

/-! ## The rest of the data -/

theorem restA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (xorB .r11 .r10 .r11 ofsO 240 ofsO ++ copy16 ofsO tmpO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem restTail_check (enc : Bool) : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (if enc then .seq padCk xorPad else .seq xorPad padCk) h).isSome = true := by
  cases enc <;> exact ⟨_, by taint_decide⟩

/-- The rest of the data, in two runs with the same pointer and length. -/
theorem rest_rel (enc : Bool) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (h4 : τ₁.gpr .r4 = τ₂.gpr .r4) (h5 : τ₁.gpr .r5 = τ₂.gpr .r5) : RelCT isa (Eq2 τ₁ τ₂) (rest enc) TT :=
  rel_seqX (rel_env E₁ E₂ [] (by simp) restA_check)
    (kept_of L E₁ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L E₂ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  rel_seqX (encOne_rel L K₁.env K₂.env (.inl rfl))
    (exec_of_wp (encOne_ok L K₁.env (d := tmpO) (by decide) (by decide)))
    (exec_of_wp (encOne_ok L K₂.env (d := tmpO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  rel_env (C₁.env K₁.env) (C₂.env K₂.env) [.r4, .r5] (by
    simp [C₁.saved .r4 (by decide), C₂.saved .r4 (by decide), C₁.saved .r5 (by decide), C₂.saved .r5 (by decide),
      K₁.gpr .r4 (by simp), K₂.gpr .r4 (by simp), K₁.gpr .r5 (by simp), K₂.gpr .r5 (by simp), h4, h5])
    (restTail_check enc)

/-! ## The data -/

/-- The start of `body`: the data in `r8`, its whole blocks in `r7`. -/
theorem bodyHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) :
    WP isa (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)]) t fun t' =>
      Env p t' ∧ t'.gpr .r8 = p.D ∧ t'.gpr .r7 = BitVec.ofNat 32 (p.n / 16) ∧ t'.z = decide (p.n / 16 = 0) := by
  have n32 := L.n_lt
  have a₈ := E.perm.argR' L (k := 8) (by decide)
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E.sp, a₈, a₁₂, A.a8, A.a12], ?_, ?_, ?_, ?_⟩
  · exact E.of_others (rs := [.r7, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl)
  · simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg]
  · simp [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ofNat_lsr32 n32]
  · simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, ofNat_lsr32 n32,
      Nat.reducePow, z_cmp0 (show p.n / 16 < 2 ^ 32 by omega_using [n32])]

/-- Where the rest of the data is. -/
theorem restBlk_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) (A : Args p t.mem) (h8 : t.gpr .r8 = p.D) :
    WP isa (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
        .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) t fun t' =>
      Env p t' ∧ t'.gpr .r4 = p.D + BitVec.ofNat 32 (16 * (p.n / 16)) ∧ t'.gpr .r5 = BitVec.ofNat 32 (p.n % 16) ∧
        t'.z = decide (p.n % 16 = 0) := by
  have n32 := L.n_lt
  have a₁₂ := E.perm.argR' L (k := 12) (by decide)
  refine WP.of_runBlock ⟨_, by orun [E.sp, a₁₂, A.a12, h8], ?_, ?_, ?_, ?_⟩
  · exact E.of_others (rs := [.r4, .r5]) (by others_tac) (by rfl) (by rfl) (by rfl)
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
      toNat_ofNat32 n32, h8]
    rw [ofNat_sub32 (Nat.mod_le _ _) n32, BitVec.add_comm, show p.n - p.n % 16 = 16 * (p.n / 16) by omega_using []]
  · simp only [Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, ite_false, reduceCtorEq, and15,
      toNat_ofNat32 n32]
  · simp only [z_subFlags, Proof.AesGcm.Arm.gpr_subFlags, gpr_setReg, ite_true, BitVec.sub_zero, and15,
      toNat_ofNat32 n32, z_cmp0 (show p.n % 16 < 2 ^ 32 by omega_using [])]

theorem bodyHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24)
    (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restBlk_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs [.r8]) 24)
    (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
      .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

/-- The whole blocks, if there are any, in two runs. -/
theorem wholeIte_rel (F : BlkFn) {pre post : List Instr}
    (hpre : pre = addCk ++ xorOfs ∨ pre = xorOfs ∨ pre = xorOfs ++ addCk)
    (hpost : post = addCk ++ xorOfs ∨ post = xorOfs ∨ post = xorOfs ++ addCk)
    {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) (A₁ : Args p τ₁.mem)
    (A₂ : Args p τ₂.mem) :
    RelCT isa (Eq2 τ₁ τ₂) (.seq (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4),
      .cmp .r7 (imm 0)]) (.ite .eq (.block []) (whole (blkFrame F) pre post))) TT :=
  rel_seq (rel_envArg L E₁ E₂ A₁ A₂ [] (by simp) bodyHead_check) (bodyHead_ok L E₁ A₁) (bodyHead_ok L E₂ A₂)
    fun _ _ ⟨U₁, h8₁, h7₁, z₁⟩ ⟨U₂, h8₂, h7₂, z₂⟩ =>
  rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_skip)
    (fun _ => whole_rel F hpre hpost L U₁ U₂ (Nat.mul_div_le p.n 16) h8₁ h8₂ h7₁ h7₂)

/-- The rest of the data, if there is any, in two runs. -/
theorem restIte_rel (enc : Bool) {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (A₁ : Args p τ₁.mem) (A₂ : Args p τ₂.mem) (h8₁ : τ₁.gpr .r8 = p.D) (h8₂ : τ₂.gpr .r8 = p.D) :
    RelCT isa (Eq2 τ₁ τ₂) (.seq (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12,
      .dp .sub .r4 .r4 (.reg .r5), .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)]) (.ite .eq (.block []) (rest enc)))
      TT :=
  rel_seq (rel_envArg L E₁ E₂ A₁ A₂ [.r8] (by simp [h8₁, h8₂]) restBlk_check) (restBlk_ok L E₁ A₁ h8₁)
    (restBlk_ok L E₂ A₂ h8₂) fun _ _ ⟨U₁, h4₁, h5₁, z₁⟩ ⟨U₂, h4₂, h5₂, z₂⟩ =>
  rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_skip)
    (fun _ => rest_rel enc L U₁ U₂ (by rw [h4₁, h4₂]) (by rw [h5₁, h5₂]))

/-- `body` for `seal`, in two runs from the states `body` starts from. -/
theorem bodySeal_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (A₁ : Args p τ₁.mem) (A₂ : Args p τ₂.mem) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₁)
    (ho0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p τ₁.mem) 0)
    (hofs₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₂)
    (ho0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p τ₂.mem) 0) :
    RelCT isa (Eq2 τ₁ τ₂) (body true) TT := by
  simp only [body, ↓reduceIte]
  refine RelCT.assoc (rel_seq (wholeIte_rel encF (.inl rfl) (.inr (.inl rfl)) L E₁ E₂ A₁ A₂)
    (wholeIte_ok encF (O0 := O₁) (l := lstarOf p τ₁.mem)
      (ckF1 := ckOf fun i => blockAtMem τ₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => ckOf (fun i => blockAtMem τ₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
      L (sealPre_ok L) (xorOfs_ok L) E₁ A₁ hofs₁ ho0₁ hck₁ hl0₁ (fun _ => rfl) rfl (fun _ => rfl))
    (wholeIte_ok encF (O0 := O₂) (l := lstarOf p τ₂.mem)
      (ckF1 := ckOf fun i => blockAtMem τ₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)))
      (ckF2 := fun _ => ckOf (fun i => blockAtMem τ₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i))) (p.n / 16))
      L (sealPre_ok L) (xorOfs_ok L) E₂ A₂ hofs₂ ho0₂ hck₂ hl0₂ (fun _ => rfl) rfl (fun _ => rfl))
    fun _ _ W₁ W₂ => ?_)
  exact restIte_rel true L W₁.env W₂.env (A₁.mut L (wholeR_mut L (Nat.mul_div_le p.n 16) W₁.frame))
    (A₂.mut L (wholeR_mut L (Nat.mul_div_le p.n 16) W₂.frame)) W₁.r8 W₂.r8

/-- `body` for `open`, in two runs from the states `body` starts from. -/
theorem bodyOpen_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (A₁ : Args p τ₁.mem) (A₂ : Args p τ₂.mem) {O₁ O₂ : Block}
    (hofs₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₁)
    (ho0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₁)
    (hck₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p τ₁.mem) 0)
    (hofs₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ofsO) = O₂)
    (ho0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 o0O) = O₂)
    (hck₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0)
    (hl0₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p τ₂.mem) 0) :
    RelCT isa (Eq2 τ₁ τ₂) (body false) TT := by
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine RelCT.assoc (rel_seq (wholeIte_rel decF (.inr (.inl rfl)) (.inr (.inr rfl)) L E₁ E₂ A₁ A₂)
    (wholeIte_ok decF (O0 := O₁) (l := lstarOf p τ₁.mem) (ckF1 := fun _ => 0)
      (ckF2 := ckOf fun i => invOf p τ₁.mem
        (blockAtMem τ₁.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₁ (lstarOf p τ₁.mem) (i + 1)) ^^^
          offAt O₁ (lstarOf p τ₁.mem) (i + 1))
      L (xorOfs_ok L) (openPost_ok L) E₁ A₁ hofs₁ ho0₁ hck₁ hl0₁ (fun _ => rfl) rfl (fun _ => rfl))
    (wholeIte_ok decF (O0 := O₂) (l := lstarOf p τ₂.mem) (ckF1 := fun _ => 0)
      (ckF2 := ckOf fun i => invOf p τ₂.mem
        (blockAtMem τ₂.mem (State.addr p.D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O₂ (lstarOf p τ₂.mem) (i + 1)) ^^^
          offAt O₂ (lstarOf p τ₂.mem) (i + 1))
      L (xorOfs_ok L) (openPost_ok L) E₂ A₂ hofs₂ ho0₂ hck₂ hl0₂ (fun _ => rfl) rfl (fun _ => rfl))
    fun _ _ W₁ W₂ => ?_)
  exact restIte_rel false L W₁.env W₂.env (A₁.mut L (wholeR_mut L (Nat.mul_div_le p.n 16) W₁.frame))
    (A₂.mut L (wholeR_mut L (Nat.mul_div_le p.n 16) W₂.frame)) W₁.r8 W₂.r8

/-! ## The tag -/

theorem tagA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (copy16 ckO tmpO ++ xorW ofsO tmpO ++ xorW ldO tmpO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem tagB_check {d : Nat} (hd : d = tagO ∨ d = t2O) : ∃ h, (VG.Taint.check VG.Arm.taint
    (VG.Arm.Taint.ofRegs (pubRegs [])) (.block (copy16 tmpO d ++ xorW sumO d)) h).isSome = true := by
  rcases hd with rfl | rfl <;> exact ⟨_, by taint_decide⟩

/-- `tag d`, in two runs with the same public arguments. -/
theorem tag_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) {d : Nat}
    (hd : d = tagO ∨ d = t2O) : RelCT isa (Eq2 τ₁ τ₂) (tag d) TT :=
  rel_seqX (rel_env E₁ E₂ [] (by simp) tagA_check)
    (kept_of L E₁ [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L E₂ [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  rel_seqX (encOne_rel L K₁.env K₂.env (.inl rfl))
    (exec_of_wp (encOne_ok L K₁.env (d := tmpO) (by decide) (by decide)))
    (exec_of_wp (encOne_ok L K₂.env (d := tmpO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  rel_env (C₁.env K₁.env) (C₂.env K₂.env) [] (by simp) (tagB_check hd)

end VG.Proof.AesOcb.Arm

end

end

/-! ### `AesOcb.Arm.Seal`, which this module and modules that import it used -/

section

/-! ### `AesOcb.Arm.Front`, which this module and modules that import it used -/

section

/-!
# AES-OCB on ARMv7: before the data

Untrusted: everything here is checked by Lean. What the contracts'
preconditions give about the arguments (`prmOf`, `lay_of`, `perm_of`,
`args_of`); the entry, which saves our caller's registers in `W`, keeps `W`,
the key context and the rounds in registers, and computes `L_$` and `L_0`
(`entry_wp`); and the entry, `Offset_0` (`nonce`) and `HASH` (`hash`)
together (`pre_wp`), as on AArch64 (`Proof.AesOcb.AArch64.pre_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (blockAtMem_frame)
open VG.Proof.AesGcm.Arm (below SavedAt savedR entry_ok covers_of_mem covers_left)

/-! ## The arguments -/

/-- The public arguments of a call. -/
def prmOf (s : State) : Prm where
  K := s.gpr .r0
  W := arg s 6
  N := s.gpr .r2
  A := arg s 0
  D := arg s 2
  T := arg s 4
  SP := s.sp
  R := (s.gpr .r1).toNat
  nl := (s.gpr .r3).toNat
  al := (arg s 1).toNat
  n := (arg s 3).toNat
  tl := (arg s 5).toNat

theorem ofNat_toNat32' (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem argR_eq (s : State) : args s 7 = argR s.sp := by
  simp only [args, argR, stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem lay_of {s : State} (h : oneLay s) : Lay (prmOf s) := by
  sig_split h
  rename_i d1 d2 d3 d4 d5 d6 d7 d8 d9 b1 b2 b3 b4 b5 f1 f2 f3 f4 f5 sp8 spf hR hv t1 t2 t3
  have t4 := h
  clear h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  rw [argR_eq] at d8 d9
  exact ⟨f1, f5, f2, f3, f4, t4, BitVec.isLt _, BitVec.isLt _, sp8, spf, d2, d1, d4, d3, d6, d5, t2, t1, d7, d8, d9,
    b1, b2, b3, b4, t3, b5, hR, hn1, hn15, ht1, ht16⟩

/-- The permissions, from the regions each function may read and write. -/
theorem perm_of {s : State} (_h : oneLay s)
    (mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 256⟩ : Region), ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
      ⟨State.addr (arg s 0), (arg s 1).toNat⟩, ⟨State.addr (arg s 4), (arg s 5).toNat⟩, args s 7],
      Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [(⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region), ⟨State.addr (arg s 6), 2560⟩], Covers [r] s.wr)
    (hwr : ∀ r ∈ s.wr, (args s 7).Disjoint r) : Perm (prmOf s) s := by
  rw [argR_eq] at mrd hwr
  exact ⟨mrd _ (by simp [prmOf]), mrd _ (by simp [prmOf]), mrd _ (by simp [prmOf]), mrd _ (by simp [prmOf]),
    mwr _ (by simp [prmOf]), mwr _ (by simp [prmOf]), mrd _ (by simp [prmOf]), hwr⟩

theorem args_of (s : State) : Args (prmOf s) s.mem :=
  ⟨rfl, by rw [prmOf, ofNat_toNat32']; rfl, rfl, by rw [prmOf, ofNat_toNat32']; rfl, rfl,
    by rw [prmOf, ofNat_toNat32']; rfl⟩

theorem sealPerm {s : State} (h : sealPre s) : Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, hl, ht⟩ := h
  have d8 := hl.2.2.2.2.2.2.2.1
  have d9 := hl.2.2.2.2.2.2.2.2.1
  refine perm_of hl (fun r hr => ?_) (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
    · exact covers_left (covers_of_mem (by rw [hwr]; simp))
    · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact d8.symm
    · exact ht.symm
    · exact d9.symm

theorem openPerm {s : State} (h : openPre s) : Perm (prmOf s) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have d8 := hl.2.2.2.2.2.2.2.1
  have d9 := hl.2.2.2.2.2.2.2.2.1
  refine perm_of hl (fun r hr => ?_) (fun r hr => ?_) fun r hr => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)
  rw [hwr] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact d8.symm
  · exact d9.symm

/-! ## Frames within `W` -/

section
variable {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame [⟨State.addr p.W, 2560⟩] m m')
include L h

theorem sched_W : sched p m' = sched p m :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact L.k_w.sub_left (Region.sub_prefix (by have := L.rounds_le; omega_using [this]))) (by have := L.rounds_le; omega_using [this])

theorem lstar_W : lstarOf p m' = lstarOf p m := by
  unfold lstarOf Spec.Ocb.ctxLstar
  exact blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Offset.sub_base _ (by decide))

theorem nonce_W : bytesAt m' (State.addr p.N) p.nl = bytesAt m (State.addr p.N) p.nl :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.n_w)
    (by have := L.nl15; omega_using [this])

theorem aad_W : bytesAt m' (State.addr p.A) p.al = bytesAt m (State.addr p.A) p.al :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.a_w)
    (by have := L.al_lt; omega_using [this])

theorem data_W : bytesAt m' (State.addr p.D) p.n = bytesAt m (State.addr p.D) p.n :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.d_w)
    (by have := L.n_lt; omega_using [this])

theorem tag_W : bytesAt m' (State.addr p.T) p.tl = bytesAt m (State.addr p.T) p.tl :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.t_w)
    (by have := L.tl16; omega_using [this])

theorem args_W (A : Args p m) : Args p m' :=
  A.frame L h fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact L.w_args.symm

end

/-- Proves that a block of `W` misses a frame of parts of `W` and the stack
below `sp`. -/
tactic_template "wdisj" L:term : tactic => `(tactic| plain_simp_names (
                   simp only [nonceR, hashR, bodyR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
                   and_intros
                   all_goals first
                     | (with_reducible refine Lay.w_w $L ?_ ?_ ?_) <;> decide
                     | (with_reducible refine (Lay.bw' $L ?_).symm) <;> decide
                     | (with_reducible refine (Lay.d_w' $L ?_).symm) <;> decide))

/-- Proves that the data misses a frame of parts of `W` and the stack below
`sp`. -/
tactic_template "ddisj" L:term : tactic => `(tactic| plain_simp_names (
                   simp only [nonceR, hashR, bodyR, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
                   and_intros
                   all_goals first
                     | (with_reducible refine Lay.d_w' $L ?_) <;> decide
                     | with_reducible exact (Lay.bd $L).symm))

/-! ## The entry -/

/-- What the entry leaves. -/
structure EntryPost (p : Prm) (s₀ s : State) : Prop where
  env : Env p s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r4 : s.gpr .r4 = p.N
  r5 : s.gpr .r5 = BitVec.ofNat 32 p.nl
  frame : Frame [⟨State.addr p.W, 2560⟩] s₀.mem s.mem
  saved : SavedAt s.mem p.W s₀
  ld : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem)
  l0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s₀.mem) 0
  ck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0

theorem entry_wp {p : Prm} (L : Lay p) {s₀ : State} (P : Perm p s₀) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa (.block entry) s₀ (EntryPost p s₀) := by
  have fw := L.ww
  have fk := L.kw
  have i24 : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 24)) 4 := by
    rw [hsp]; exact P.argR' L (k := 24) (by decide)
  simp only [entry, lsetup, List.append_assoc]
  refine entry_ok (off := 24) (by decide) i24 (by rw [hW]; exact L.ww) (by rw [hW]; exact P.w)
    fun s₁ g12 g rd₁ wr₁ sp₁ sv₁ fr₁ => ?_
  rw [hW] at g12 sv₁ fr₁
  obtain ⟨s₂, run₂, E₂, r4₂, r5₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.mov .r11 (.reg .r12), .mov .r10 (.reg .r0),
      .mov .r9 (.reg .r1), .mov .r4 (.reg .r2), .mov .r5 (.reg .r3)] s₁ = some s₂ ∧ Env p s₂ ∧
      s₂.gpr .r4 = p.N ∧ s₂.gpr .r5 = BitVec.ofNat 32 p.nl ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr := by
    refine ⟨_, by orun [], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, by rfl, by simp [rd_setReg, rd₁], by simp [wr_setReg, wr₁]⟩
    · simp [gpr_setReg, g .r1 (by decide), h1]
    · simp [gpr_setReg, g .r0 (by decide), h0]
    · simp [gpr_setReg, g12]
    · simp [sp_setReg, sp₁, hsp]
    · exact P.of_eq (by simp [rd_setReg, rd₁]) (by simp [wr_setReg, wr₁])
    · simp [gpr_setReg, g .r2 (by decide), h2]
    · simp [gpr_setReg, g .r3 (by decide), h3]
  refine WP.block_append (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  -- `L_$`
  refine WP.block_append (WP.mono (dbl_wp (b := .r10) (t := s₂) (P := State.addr p.K) (W := State.addr p.W)
    (sO := 240) (dO := ldO) ⟨by decide, by decide, by decide⟩ (by rw [E₂.r10]) (by rw [E₂.r11]) (by decide)
    (by decide) (by rw [E₂.r10]; omega_using [fk]) (by rw [E₂.r11]; simp only [ldO]; omega_using [fw]) (E₂.perm.kC (by decide))
    (E₂.perm.wC (by decide))) fun s₃ R₃ => ?_)
  have E₃ := E₂.of_others R₃.gpr R₃.sp R₃.rd R₃.wr
  -- `L_0`
  refine WP.block_append (WP.mono (dbl_wp (b := .r11) (t := s₃) (P := State.addr p.W) (W := State.addr p.W)
    (sO := ldO) (dO := l0O) ⟨by decide, by decide, by decide⟩ (by rw [E₃.r11]) (by rw [E₃.r11]) (by decide)
    (by decide) (by rw [E₃.r11]; simp only [ldO]; omega_using [fw]) (by rw [E₃.r11]; simp only [l0O]; omega_using [fw])
    (E₃.perm.wCR (by decide)) (E₃.perm.wC (by decide))) fun s₄ R₄ => ?_)
  have E₄ := E₃.of_others R₄.gpr R₄.sp R₄.rd R₄.wr
  -- the checksum
  refine WP.mono (zero16_wp (s := s₄) (o := ckO) (by decide) (by rw [E₄.r11]; simp only [ckO]; omega_using [fw])
    (by rw [E₄.r11]; exact E₄.perm.wC (by decide))) fun s₅ R₅ => ?_
  rw [E₄.r11] at R₅
  have f₃ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ldO, 16⟩] s₂.mem s₃.mem := by
    rw [R₃.mem]; exact dblMem_frame _ _ _
  have f₄ : Frame [⟨State.addr p.W + BitVec.ofNat 64 l0O, 16⟩] s₃.mem s₄.mem := by
    rw [R₄.mem]; exact dblMem_frame _ _ _
  have f₅ : Frame [⟨State.addr p.W + BitVec.ofNat 64 ckO, 16⟩] s₄.mem s₅.mem := by
    rw [R₅.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have inW : ∀ {d k : Nat}, d + k ≤ 2560 → ∀ r ∈ [(⟨State.addr p.W + BitVec.ofNat 64 d, k⟩ : Region)],
      ∃ r' ∈ [(⟨State.addr p.W, 2560⟩ : Region)], Region.Sub r r' := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, Lay.wSub h⟩
  have F₂ : Frame [⟨State.addr p.W, 2560⟩] s₀.mem s₂.mem := by rw [m₂]; exact fr₁.sub (inW (by decide))
  have F₅ : Frame [⟨State.addr p.W, 2560⟩] s₂.mem s₅.mem :=
    ((f₃.sub (inW (by decide))).trans (f₄.sub (inW (by decide)))).trans (f₅.sub (inW (by decide)))
  have hl : blockAtMem s₂.mem (State.addr p.K + BitVec.ofNat 64 240) = lstarOf p s₀.mem :=
    (lstar_W L F₂).symm ▸ rfl
  have ld₃ : blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem) := by
    rw [R₃.mem, blockAtMem_dbl, hl]; rfl
  have ld₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem) := by
    rw [blockAtMem_frame f₄ (by wdisj L), ld₃]
  have l0₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s₀.mem) 0 := by
    rw [R₄.mem, blockAtMem_dbl, ld₃]; rfl
  refine ⟨E₄.of_others R₅.gpr R₅.sp R₅.rd R₅.wr, by rw [R₅.rd, R₄.rd, R₃.rd, rd₂],
    by rw [R₅.wr, R₄.wr, R₃.wr, wr₂], by rw [R₅.gpr _ (by decide), R₄.gpr _ (by decide), R₃.gpr _ (by decide), r4₂],
    by rw [R₅.gpr _ (by decide), R₄.gpr _ (by decide), R₃.gpr _ (by decide), r5₂], F₂.trans F₅, ?_,
    by rw [blockAtMem_frame f₅ (by wdisj L), ld₄], by rw [blockAtMem_frame f₅ (by wdisj L), l0₄],
    by rw [R₅.mem, blockAtMem_zero4]⟩
  rw [← m₂] at sv₁
  exact ((sv₁.frame f₃ (by wdisj L)).frame f₄ (by wdisj L)).frame f₅ (by wdisj L)

/-! ## Before the data -/

theorem nonceR_mut {p : Prm} (L : Lay p) {m m' : Mem} (h : Frame (nonceR p) m m') : Frame (mutR p) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact w_mut L (.inl (by decide))
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact w_mut L (.inr ⟨by decide, by decide⟩)
    · exact below_mut L

/-- What the pieces before the data leave: the offset, the checksum, `L_$`,
`L_0` and `HASH`, and the inputs as they were. -/
structure Pre (p : Prm) (s₀ s : State) : Prop where
  env : Env p s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  args : Args p s.mem
  saved : SavedAt s.mem p.W s₀
  sched : sched p s.mem = sched p s₀.mem
  lstar : lstarOf p s.mem = lstarOf p s₀.mem
  data : bytesAt s.mem (State.addr p.D) p.n = bytesAt s₀.mem (State.addr p.D) p.n
  tag : bytesAt s.mem (State.addr p.T) p.tl = bytesAt s₀.mem (State.addr p.T) p.tl
  ofs : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ofsO) =
    Spec.Ocb.offset0 (ciphOf p s₀.mem) p.tl (bytesAt s₀.mem (State.addr p.N) p.nl)
  o0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 o0O) =
    Spec.Ocb.offset0 (ciphOf p s₀.mem) p.tl (bytesAt s₀.mem (State.addr p.N) p.nl)
  ck : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem)
  l0 : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 l0O) = lAt (lstarOf p s₀.mem) 0
  sum : blockAtMem s.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ciphOf p s₀.mem) (lstarOf p s₀.mem) (aadOf p s₀.mem)

/-- `entry`, `nonce` and `hash`. -/
theorem pre_wp' {p : Prm} (L : Lay p) {s₀ : State} (P : Perm p s₀) (A : Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa (.seq (.block entry) (.seq nonce Impl.AesOcb.Arm.hash)) s₀ (Pre p s₀) := by
  refine WP.seq (WP.mono (entry_wp L P hsp h0 h1 h2 h3 hW) fun s₁ P₁ => ?_)
  have A₁ := args_W L P₁.frame A
  refine WP.seq (WP.mono (nonce_ok L P₁.env A₁ P₁.r4 P₁.r5) fun s₂ N₂ => ?_)
  have F₂ := nonceR_mut L N₂.frame
  have l₂ : lstarOf p s₂.mem = lstarOf p s₀.mem := (lstar_mut L F₂).trans (lstar_W L P₁.frame)
  have l0₂ : blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) =
      blockAtMem s₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) := blockAtMem_frame N₂.frame (by wdisj L)
  refine WP.mono (hash_ok L N₂.env (A₁.mut L F₂) (by rw [l0₂, P₁.l0, l₂])) fun s₃ H₃ => ?_
  have F₃ := hashR_mut L H₃.frame
  have sc₂ : sched p s₂.mem = sched p s₀.mem := (sched_mut L F₂).trans (sched_W L P₁.frame)
  have c₂ : ciphOf p s₂.mem = ciphOf p s₀.mem := by simp only [ciphOf, sc₂]
  have c₁ : ciphOf p s₁.mem = ciphOf p s₀.mem := by simp only [ciphOf, sched_W L P₁.frame]
  have k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 192) ∨
      (216 ≤ d ∧ d + 16 ≤ 256)) →
      blockAtMem s₃.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun {d} hd => blockAtMem_frame H₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact (L.bw' (by omega_using [hd])).symm
  have k₂ : ∀ {d : Nat}, d ∈ [ckO, ldO, l0O] →
      blockAtMem s₂.mem (State.addr p.W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (State.addr p.W + BitVec.ofNat 64 d) :=
    fun {d} hd => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl <;> exact blockAtMem_frame N₂.frame (by wdisj L)
  refine ⟨H₃.env, by rw [H₃.rd, N₂.rd, P₁.rd], by rw [H₃.wr, N₂.wr, P₁.wr], (A₁.mut L F₂).mut L F₃,
    ((P₁.saved.frame N₂.frame (by wdisj L)).frame H₃.frame (by wdisj L)),
    (sched_mut L F₃).trans sc₂, (lstar_mut L F₃).trans l₂,
    by rw [Proof.Cmac.bytesAt_frame H₃.frame (by ddisj L) (by have := L.n_lt; omega_using [this]),
      Proof.Cmac.bytesAt_frame N₂.frame (by ddisj L) (by have := L.n_lt; omega_using [this]), data_W L P₁.frame],
    by rw [tag_mut L F₃, tag_mut L F₂, tag_W L P₁.frame], ?_, ?_,
    by rw [k₃ (by decide), k₂ (by simp), P₁.ck], by rw [k₃ (by decide), k₂ (by simp), P₁.ld],
    by rw [k₃ (by decide), k₂ (by simp), P₁.l0], ?_⟩
  · rw [k₃ (by decide), N₂.ofs]
    show Spec.Ocb.offset0 (ciphOf p s₁.mem) _ _ = _
    rw [c₁, nonce_W L P₁.frame]
  · rw [k₃ (by decide), N₂.o0]
    show Spec.Ocb.offset0 (ciphOf p s₁.mem) _ _ = _
    rw [c₁, nonce_W L P₁.frame]
  · rw [H₃.sum, c₂, l₂, aadOf, aad_mut L F₂, aad_W L P₁.frame]

end VG.Proof.AesOcb.Arm

end

end

/-!
# AES-OCB on ARMv7: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. `seal` is `front`: `entry`,
`Offset_0` (`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W`
(`tag`); then the copy of the tag to `tag`, whose address is on the stack
(`tagOut_ok`), and `restore` (`seal_wp`), as on AArch64
(`Proof.AesOcb.AArch64.seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt)
open VG.Proof.Ocb (blockAtMem_frame length_bytesAt)
open VG.Proof.AesGcm.Arm (below SavedAt restore_ok copyLoop_ok covers_left covers_prefix covers_of_mem)

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`. -/
theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (A : Args p s.mem)
    (hTw : Covers [⟨State.addr p.T, p.tl⟩] s.wr) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem (State.addr p.T) (bytesAt s.mem (State.addr p.W) p.tl) ∧
      Env p t ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have fw := L.ww
  have t16 := L.tl16
  have a₁₆ := E.perm.argR' L (k := 16) (by decide)
  have a₂₀ := E.perm.argR' L (k := 20) (by decide)
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨_, by orun [E.sp, a₁₆, a₂₀, A.a16, A.a20], ?_⟩)
  refine WP.mono (copyLoop_ok _ (S := p.W) (D := p.T) (n := p.tl)
    ⟨by simp [gpr_setReg, E.r11], by simp [gpr_setReg, E.sp, A.a16], by simp [gpr_setReg, E.sp, A.a20], L.tl1,
      by omega_using [t16], by omega_using [fw, t16], L.tw, by simp only [rd_setReg, wr_setReg]; exact covers_left (covers_prefix E.perm.w (by omega_using [t16])),
      by simp only [wr_setReg]; exact hTw, (L.t_w.sub_right (Region.sub_prefix (by omega_using [t16]))).symm⟩)
    fun t ⟨m, O⟩ => ⟨by rw [m]; rfl, E.keep (fun r hr => ?_) (by rw [O.sp]; rfl) (by rw [O.rd]; rfl)
      (by rw [O.wr]; rfl), by rw [O.rd]; rfl, by rw [O.wr]; rfl⟩
  simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    (rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg])

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (q : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m q t = (Spec.Ocb.toBytes (blockAtMem m q)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega_using [h],
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {p : Prm} (L : Lay p) {d : Nat} (hd : d + 16 ≤ 128 ∨ (164 ≤ d ∧ d + 16 ≤ 2560)) {m m' : Mem}
    (h : Frame [⟨State.addr p.W + BitVec.ofNat 64 tmpO, 16⟩, ⟨State.addr p.W + BitVec.ofNat 64 d, 16⟩,
      ⟨State.addr p.W + BitVec.ofNat 64 scrO, 2048⟩, below p.SP] m m') :
    Frame (mutR p) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_mut L (.inl (by decide))
  · exact w_mut L hd
  · exact w_mut L (.inr ⟨by decide, by decide⟩)
  · exact below_mut L

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' {p : Prm} (L : Lay p) {s₀ : State} (P : Perm p s₀) (A : Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W)
    (hTw : Covers [⟨State.addr p.T, p.tl⟩] s₀.wr) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ocb.encryptWith (ciphOf p s₀.mem) (lstarOf p s₀.mem) p.tl (bytesAt s₀.mem (State.addr p.N) p.nl)
        (aadOf p s₀.mem) (bytesAt s₀.mem (State.addr p.D) p.n) =
        (bytesAt s'.mem (State.addr p.D) p.n, bytesAt s'.mem (State.addr p.T) p.tl) := by
  unfold «seal» front
  refine WP.seq (WP.assoc (WP.assoc (WP.seq (WP.mono (WP.assoc' (pre_wp' L P A hsp h0 h1 h2 h3 hW))
    fun s₃ P₃ => ?_))))
  refine WP.seq (WP.mono (bodySeal_ok L P₃.env P₃.args P₃.ofs P₃.o0 P₃.ck (by rw [P₃.l0, P₃.lstar]))
    fun s₄ B => ?_)
  have F₄ : Frame (mutR p) s₃.mem s₄.mem := bodyR_mut L B.frame
  refine WP.mono (tag_ok L B.env (.inl rfl)) fun s₅ T₅ => ?_
  have F₅ : Frame (mutR p) s₄.mem s₅.mem := tagR_mut L (.inl (by decide)) T₅.frame
  refine WP.seq (WP.mono (tagOut_ok L T₅.env ((P₃.args.mut L F₄).mut L F₅)
    (by rw [T₅.wr, B.wr, P₃.wr]; exact hTw)) fun s₆ ⟨m₆, E₆, rd₆, wr₆⟩ => ?_)
  have hx : (bytesAt s₅.mem (State.addr p.W) p.tl).length = p.tl := length_bytesAt _ _ _
  have f₆ : Frame [⟨State.addr p.T, p.tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [hx]; exact Region.contains_self _ _)
  have sv₆ : SavedAt s₆.mem p.W s₀ :=
    ((P₃.saved.frame F₄ (saved_mut L)).frame F₅ (saved_mut L)).frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (L.t_w' (by decide)).symm
  refine WP.mono (restore_ok E₆.r11 L.ww (covers_left E₆.perm.w) sv₆ (by rw [E₆.sp, hsp]))
    fun s' ⟨ab, hm, _, _, _⟩ => ⟨ab, ?_⟩
  have c₄ : ciphOf p s₄.mem = ciphOf p s₀.mem := by simp only [ciphOf, sched_mut L F₄, P₃.sched]
  have c₃ : ciphOf p s₃.mem = ciphOf p s₀.mem := by simp only [ciphOf, P₃.sched]
  have hout := B.out
  rw [c₃, P₃.lstar, P₃.data] at hout
  have hofs := B.ofs
  rw [P₃.lstar] at hofs
  have hck := B.ck
  rw [P₃.data] at hck
  have ld₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (lstarOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.ld]
  have sum₄ : blockAtMem s₄.mem (State.addr p.W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ciphOf p s₀.mem) (lstarOf p s₀.mem) (aadOf p s₀.mem) := by
    rw [blockAtMem_frame B.frame (by wdisj L), P₃.sum]
  have d₆ : bytesAt s'.mem (State.addr p.D) p.n = bytesAt s₄.mem (State.addr p.D) p.n := by
    rw [hm, Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by have := L.n_lt; omega_using [this])]
    exact Proof.Cmac.bytesAt_frame T₅.frame (by ddisj L) (by have := L.n_lt; omega_using [this])
  have tv := T₅.val
  rw [show State.addr p.W + BitVec.ofNat 64 tagO = State.addr p.W from BitVec.add_zero _] at tv
  have t₆ : bytesAt s'.mem (State.addr p.T) p.tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem (State.addr p.W))).take p.tl := by
    rw [hm, m₆, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [hx]) (by have := L.tl16; omega_using [this]), hx,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, bytesAt_take_block _ _ L.tl16]
  rw [Proof.Ocb.encryptWith_eq, d₆, hout, t₆, tv, hck, hofs, ld₄, sum₄, c₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < p.n % 16
  · have h' : p.n - 16 * (p.n / 16) > 0 := by omega_using [hr]
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (p.n - 16 * (p.n / 16) > 0) := by omega_using [hr]
    simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp {s : State} (h : sealArm.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' :=
  seal_wp' (lay_of h.2.2.1) (sealPerm h) (args_of s) rfl rfl (ofNat_toNat32' _).symm rfl (ofNat_toNat32' _).symm rfl
    (covers_of_mem (by rw [h.2.1]; simp [prmOf]))

end VG.Proof.AesOcb.Arm

end

end

/-! ### `AesOcb.Arm.CTPre`, which only this module used -/

section

/-!
# AES-OCB on ARMv7: `Offset_0` and `HASH` in two runs

Untrusted: everything here is checked by Lean. `nonce` and `hash`, in two
runs with the same public arguments: the code between the calls by the taint
analysis, from the registers holding the public arguments and those pinned
to the same values in both runs (the nonce and its length, the associated
data's pointer and its blocks, the count of a chunk), and each call of
`vg_aes_encrypt_blocks` with the same arguments in both runs (`nonce_rel`,
`hash_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem)
open VG.Proof.Ocb (blockAtMem_frame)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (eval_eq' eval_ne' z_subFlags z_cmp0)

/-! ## `Offset_0` -/

theorem nonceBlock_check :
    ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs [.r4, .r5]) 24) nonceBlock h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem offset0_check :
    ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block offset0) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `nonce`, in two runs with the same public arguments, nonce pointer and
length. -/
theorem nonce_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) (A₁ : Args p τ₁.mem)
    (A₂ : Args p τ₂.mem) (h4 : τ₁.gpr .r4 = τ₂.gpr .r4) (h5 : τ₁.gpr .r5 = τ₂.gpr .r5) :
    RelCT isa (Eq2 τ₁ τ₂) nonce TT :=
  rel_seqX (rel_envArg L E₁ E₂ A₁ A₂ [.r4, .r5] (by simp [h4, h5]) nonceBlock_check)
    (kept_of L E₁ [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L E₂ [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  rel_seqX (encOne_rel L K₁.env K₂.env (.inl rfl)) (exec_of_wp (encOne_ok L K₁.env (d := tmpO) (by decide) (by decide)))
    (exec_of_wp (encOne_ok L K₂.env (d := tmpO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  rel_env (C₁.env K₁.env) (C₂.env K₂.env) [] (by simp) offset0_check

/-! ## A chunk of `HASH` -/

/-- The start of a chunk: `Z` set if fewer than 16 blocks are left. -/
theorem chunkB0_ok {p : Prm} (L : Lay p) {t₀ t : State} {j : Nat} (H : HInv p t₀ t j) :
    WP isa (.block [.mov .r12 (.shifted .r7 .lsr 4), .cmp .r12 (imm 0)]) t fun t' =>
      HInv p t₀ t' j ∧ t'.z = decide (p.al / 16 - j < 16) := by
  have al32 := L.al_lt
  have m32 : p.al / 16 - j < 2 ^ 32 := by omega_using [al32]
  have z₁ : (BitVec.ofNat 32 (p.al / 16 - j) >>> 4 == 0) = decide (p.al / 16 - j < 16) := by
    rw [ofNat_lsr32 m32, z_cmp0 (by omega_using [al32])]; congr 1; apply propext; omega_using []
  refine WP.of_runBlock ⟨_, by orun [H.r7], ?_, ?_⟩
  · exact ⟨H.env.of_others (rs := [.r12]) (by others_tac) (by rfl) (by rfl) (by rfl), H.frame, H.rd, H.wr, H.le,
      H.sum, H.oh, by simp [gpr_setReg, H.r4], by simp [gpr_setReg, H.r6], by simp [gpr_setReg, H.r7], H.l0⟩
  · simp only [z_subFlags, gpr_setReg, ite_true, H.r7, BitVec.sub_zero, z₁]

/-- The count of a chunk, `min(16, r7)`, in `r5`. -/
theorem chunkSel_ok {p : Prm} {t₀ t : State} {j : Nat} (H : HInv p t₀ t j)
    (hz : t.z = decide (p.al / 16 - j < 16)) :
    WP isa (.ite .eq (.block [.mov .r5 (.reg .r7)]) (.block [.mov .r5 (imm 16)])) t fun t' =>
      HInv p t₀ t' j ∧ t'.gpr .r5 = BitVec.ofNat 32 (min 16 (p.al / 16 - j)) := by
  have Hk : ∀ {t' : State}, t'.mem = t.mem → t'.rd = t.rd → t'.wr = t.wr → t'.sp = t.sp →
      Others [.r5] t t' → HInv p t₀ t' j := fun hm hrd hwr hsp ho =>
    ⟨H.env.of_others ho hsp hrd hwr, by rw [hm]; exact H.frame, by rw [hrd, H.rd], by rw [hwr, H.wr], H.le,
      by rw [hm]; exact H.sum, by rw [hm]; exact H.oh, by rw [ho _ (by decide), H.r4], by rw [ho _ (by decide), H.r6],
      by rw [ho _ (by decide), H.r7], by rw [hm]; exact H.l0⟩
  refine WP.ite (decide (p.al / 16 - j < 16)) (eval_eq' hz) (fun hb => ?_) (fun hb => ?_)
  · have hlt : p.al / 16 - j < 16 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by orun [H.r7], Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac), ?_⟩
    simp [gpr_setReg, H.r7, show min 16 (p.al / 16 - j) = p.al / 16 - j by omega_using [hlt]]
  · have hlt : ¬ p.al / 16 - j < 16 := by simpa using hb
    refine WP.of_runBlock ⟨_, by orun [], Hk (by rfl) (by rfl) (by rfl) (by rfl) (by others_tac), ?_⟩
    simp [gpr_setReg, show min 16 (p.al / 16 - j) = 16 by omega_using [hlt]]

/-- After a chunk's call: the count back in `r5`, the buffer in `r8`. -/
theorem chunkB4_ok {p : Prm} (L : Lay p) {t₀ t₂ t₃ : State} {j c : Nat} (F : FillInv p t₀ j c t₂ c)
    (hc : c ≤ 16) (C : BlkPost encF (chunkCallSt p c t₂) p.K (p.W + BitVec.ofNat 32 bufO)
      (p.W + BitVec.ofNat 32 scrO) p.R c t₃) :
    WP isa (.block [addI .r8 .r11 bufO, .ldr .r5 .r11 cnO]) t₃ fun t' =>
      Env p t' ∧ t'.gpr .r5 = BitVec.ofNat 32 c ∧ t'.gpr .r8 = p.W + BitVec.ofNat 32 bufO := by
  have fw := L.ww
  have E₂ : Env p (chunkCallSt p c t₂) := (chunkCall_blk L F hc).2
  have E₃ : Env p t₃ := E₂.of_saved C.saved C.sp C.rd C.wr
  have eC : State.addr (p.W + BitVec.ofNat 32 212) = State.addr p.W + BitVec.ofNat 64 212 := L.wA (by decide)
  have eB : State.addr (p.W + BitVec.ofNat 32 bufO) = State.addr p.W + BitVec.ofNat 64 bufO := L.wA (by decide)
  have eS : State.addr (p.W + BitVec.ofNat 32 scrO) = State.addr p.W + BitVec.ofNat 64 scrO := L.wA (by decide)
  have fr := C.frame
  rw [eB, eS, E₂.sp] at fr
  have cnt₃ : t₃.mem.readW (State.addr p.W + BitVec.ofNat 64 212) 32 = BitVec.ofNat 32 c := by
    rw [fr.readW (r := ⟨State.addr p.W + BitVec.ofNat 64 212, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by simp only [bufO]; omega_using [hc])
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)]
    exact F.cnt
  have rC₃ : InRegions (t₃.rd ++ t₃.wr) (State.addr p.W + BitVec.ofNat 64 212) 4 := E₃.perm.wR (by decide)
  refine WP.of_runBlock ⟨_, by orun [E₃.r11, eC, rC₃, cnt₃], ?_, ?_, ?_⟩
  · exact E₃.of_others (rs := [.r5, .r8]) (by others_tac) (by rfl) (by rfl) (by rfl)
  · simp [gpr_setReg]
  · simp [gpr_setReg, E₃.r11, bufO]

theorem chunkB0_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r7]))
    (.block [.mov .r12 (.shifted .r7 .lsr 4), .cmp .r12 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkSelT_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [.mov .r5 (.reg .r7)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkSelF_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [.mov .r5 (imm 16)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkB1_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), addI .r8 .r11 bufO]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem chunkFill_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5, .r6, .r8]))
    (.loop hashFill .ne) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkB3_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (callArgs ++ [addI .r2 .r11 bufO, .ldr .r3 .r11 cnO])) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkB4_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block [addI .r8 .r11 bufO, .ldr .r5 .r11 cnO]) h).isSome = true := ⟨_, by taint_decide⟩

theorem chunkSum_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r5, .r8]))
    (.seq hashSum (.block [.cmp .r7 (imm 0)])) h).isSome = true := ⟨_, by taint_decide⟩

/-- A chunk, in two runs at the same block of the associated data. -/
theorem chunk_rel {p : Prm} (L : Lay p) {a b τ₁ τ₂ : State} {j : Nat} (H₁ : HInv p a τ₁ j) (H₂ : HInv p b τ₂ j)
    (hj : j < p.al / 16) : RelCT isa (Eq2 τ₁ τ₂) hashChunk TT := by
  have hc0 : 0 < min 16 (p.al / 16 - j) := by omega_using [hj]
  have hc : min 16 (p.al / 16 - j) ≤ 16 := Nat.min_le_left _ _
  have hjc : j + min 16 (p.al / 16 - j) ≤ p.al / 16 := by omega_using [hj]
  unfold hashChunk
  refine rel_seq (rel_env H₁.env H₂.env [.r7] (by simp [H₁.r7, H₂.r7]) chunkB0_check) (chunkB0_ok L H₁)
    (chunkB0_ok L H₂) fun u₁ u₂ ⟨U₁, z₁⟩ ⟨U₂, z₂⟩ => ?_
  refine rel_seq (rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_env U₁.env U₂.env [] (by simp) chunkSelT_check)
    (fun _ => rel_env U₁.env U₂.env [] (by simp) chunkSelF_check)) (chunkSel_ok U₁ z₁) (chunkSel_ok U₂ z₂)
    fun v₁ v₂ ⟨V₁, h5₁⟩ ⟨V₂, h5₂⟩ => ?_
  refine rel_seq (rel_env V₁.env V₂.env [] (by simp) chunkB1_check) (chunkHead_ok L V₁ hc hjc h5₁)
    (chunkHead_ok L V₂ hc hjc h5₂) fun w₁ w₂ F₁ F₂ => ?_
  refine rel_seq (rel_env F₁.env F₂.env [.r4, .r5, .r6, .r8] (by simp [F₁.r4, F₂.r4, F₁.r5, F₂.r5, F₁.r6, F₂.r6,
    F₁.r8, F₂.r8]) chunkFill_check) (fill_ok L hc0 hc hjc F₁) (fill_ok L hc0 hc hjc F₂) fun x₁ x₂ G₁ G₂ => ?_
  refine rel_seq (F₁ := fun y => y = chunkCallSt p _ x₁) (F₂ := fun y => y = chunkCallSt p _ x₂)
    (rel_env G₁.env G₂.env [] (by simp) chunkB3_check) (WP.of_runBlock ⟨_, chunkArgs_run L G₁, rfl⟩)
    (WP.of_runBlock ⟨_, chunkArgs_run L G₂, rfl⟩) fun y₁ y₂ e₁ e₂ => ?_
  subst e₁ e₂
  have B₁ := chunkCall_blk L G₁ hc
  have B₂ := chunkCall_blk L G₂ hc
  refine rel_seq (rel_blk encF B₁.1 B₂.1 (B₁.2.sp_eq B₂.2)) (blk_call encF B₁.1) (blk_call encF B₂.1)
    fun z₁ z₂ C₁ C₂ => ?_
  have E₁ : Env p z₁ := B₁.2.of_saved C₁.saved C₁.sp C₁.rd C₁.wr
  have E₂ : Env p z₂ := B₂.2.of_saved C₂.saved C₂.sp C₂.rd C₂.wr
  exact rel_seq (rel_env E₁ E₂ [] (by simp) chunkB4_check) (chunkB4_ok L G₁ hc C₁) (chunkB4_ok L G₂ hc C₂)
    fun _ _ ⟨D₁, r5₁, r8₁⟩ ⟨D₂, r5₂, r8₂⟩ => rel_env D₁ D₂ [.r5, .r8] (by simp [r5₁, r5₂, r8₁, r8₂]) chunkSum_check

/-! ## `HASH` -/

theorem hashHead_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24)
    (.block (Impl.AesGcm.Arm.zero16 sumO ++ Impl.AesGcm.Arm.zero16 ohO ++
      ([.ldrSp .r4 0, .ldrSp .r7 4, .mov .r7 (.shifted .r7 .lsr 4), .mov .r6 (imm 1), .cmp .r7 (imm 0)] :
        List Instr))) h).isSome =
      true := ⟨_, by taint_decide⟩

theorem hashMid_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24)
    (.block [.ldrSp .r5 4, .dp .and .r5 .r5 (imm 15), .cmp .r5 (imm 0)]) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestA_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (xorB .r11 .r10 .r11 ohO 240 ohO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestPad_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [.r4, .r5]))
    (padTo bufO) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestB_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (xorW ohO bufO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem hashRestC_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs []))
    (.block (xorW bufO sumO)) h).isSome = true := ⟨_, by taint_decide⟩

/-- The rest of the associated data, in two runs with the same pointer and
length. -/
theorem hashRest_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂)
    (h4 : τ₁.gpr .r4 = τ₂.gpr .r4) (h5 : τ₁.gpr .r5 = τ₂.gpr .r5) : RelCT isa (Eq2 τ₁ τ₂) hashRest TT :=
  rel_seqX (rel_env E₁ E₂ [] (by simp) hashRestA_check)
    (kept_of L E₁ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L E₂ [.r4, .r5] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ K₁ K₂ =>
  rel_seqX (rel_env K₁.env K₂.env [.r4, .r5] (by
      simp [K₁.gpr .r4 (by simp), K₂.gpr .r4 (by simp), K₁.gpr .r5 (by simp), K₂.gpr .r5 (by simp), h4, h5])
      hashRestPad_check)
    (kept_of L K₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L K₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ M₁ M₂ =>
  rel_seqX (rel_env M₁.env M₂.env [] (by simp) hashRestB_check)
    (kept_of L M₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L M₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun _ _ N₁ N₂ =>
  rel_seqX (encOne_rel L N₁.env N₂.env (.inr rfl))
    (exec_of_wp (encOne_ok L N₁.env (d := bufO) (by decide) (by decide)))
    (exec_of_wp (encOne_ok L N₂.env (d := bufO) (by decide) (by decide))) fun _ _ C₁ C₂ =>
  rel_env (C₁.env N₁.env) (C₂.env N₂.env) [] (by simp) hashRestC_check

/-- `HASH`, in two runs with the same public arguments. -/
theorem hash_rel {p : Prm} (L : Lay p) {τ₁ τ₂ : State} (E₁ : Env p τ₁) (E₂ : Env p τ₂) (A₁ : Args p τ₁.mem)
    (A₂ : Args p τ₂.mem)
    (hl₁ : blockAtMem τ₁.mem (State.addr p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (lstarOf p τ₁.mem) 0)
    (hl₂ : blockAtMem τ₂.mem (State.addr p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (lstarOf p τ₂.mem) 0) :
    RelCT isa (Eq2 τ₁ τ₂) Impl.AesOcb.Arm.hash TT := by
  unfold Impl.AesOcb.Arm.hash
  refine rel_seq (rel_envArg L E₁ E₂ A₁ A₂ [] (by simp) hashHead_check) (hashHead_ok L E₁ A₁ hl₁)
    (hashHead_ok L E₂ A₂ hl₂) fun u₁ u₂ ⟨U₁, z₁⟩ ⟨U₂, z₂⟩ => ?_
  refine rel_seq ?_ (hashWhole_ok L U₁ z₁) (hashWhole_ok L U₂ z₂) fun v₁ v₂ V₁ V₂ => ?_
  · refine rel_ite (eval_eq' z₁) (eval_eq' z₂) (fun _ => rel_skip) fun hb => ?_
    have hm : p.al / 16 ≠ 0 := by simpa using hb
    refine rel_loop (fun k σ₁ σ₂ => ∃ j, k = p.al / 16 - j ∧ j < p.al / 16 ∧ HInv p τ₁ σ₁ j ∧ HInv p τ₂ σ₂ j)
      (fun k σ₁ σ₂ ⟨j, hk, hj, H₁, H₂⟩ => ?_) (p.al / 16 - 0) ⟨0, rfl, by omega_using [hm], U₁, U₂⟩
    refine rel_wpQ (chunk_rel L H₁ H₂ hj) (hashChunk_ok L H₁ hj) (hashChunk_ok L H₂ hj)
      fun x y ⟨X, zx⟩ ⟨Y, zy⟩ => ⟨by rw [eval_ne' zx, eval_ne' zy], fun hc => ?_⟩
    rw [eval_ne' zx] at hc
    have hlt : j + min 16 (p.al / 16 - j) < p.al / 16 := by
      simp only [Option.some.injEq, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hc; omega_using [hc]
    exact ⟨p.al / 16 - (j + min 16 (p.al / 16 - j)), by omega_using [hk, hj], _, rfl, hlt, X, Y⟩
  · have Av₁ : Args p v₁.mem := A₁.mut L (hashR_mut L V₁.frame)
    have Av₂ : Args p v₂.mem := A₂.mut L (hashR_mut L V₂.frame)
    refine rel_seq (rel_envArg L V₁.env V₂.env Av₁ Av₂ [] (by simp) hashMid_check) (hashMid_ok L V₁ Av₁)
      (hashMid_ok L V₂ Av₂) fun w₁ w₂ ⟨W₁, h5₁, z₁'⟩ ⟨W₂, h5₂, z₂'⟩ => ?_
    exact rel_ite (eval_eq' z₁') (eval_eq' z₂') (fun _ => rel_skip)
      (fun _ => hashRest_rel L W₁.env W₂.env (by rw [W₁.r4, W₂.r4]) (by rw [h5₁, h5₂]))

end VG.Proof.AesOcb.Arm

end

end

/-!
# AES-OCB on ARMv7: `vg_aes_ocb_seal` and `vg_aes_ocb_open` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same
public arguments (`onePub`) have the same `prmOf`; each piece of `seal` and
`open` is related in the two runs by the lemmas of `CTPre.lean` and
`CTBody.lean`, the entry, the copy of the tag, the comparison, the mask and
the restore by the taint analysis (`seal_ct`, `open_ct`). `open` compares
the tags and masks the data without a branch: whether the tag is right, in
`r0`, is never branched on nor used as an address.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesOcb.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem)
open VG.Proof.Ocb (blockAtMem_frame)
open VG.Impl.AesGcm.Arm (imm addI restore)

/-- `(a; (b; (c; (d; e)))); f`, from `a; (b; (c; (d; (e; f))))`. -/
theorem rel_assoc5 {P Q : State → State → Prop} {a b c d e f : Prog isa}
    (h : RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e f))))) Q) :
    RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d e)))) f) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ f₁ => cases a₁ with | seq a₁ b₁ => cases b₁ with | seq b₁ c₁ => cases c₁ with
    | seq c₁ d₁ => cases d₁ with | seq d₁ e₁ =>
  cases e₂ with | seq a₂ f₂ => cases a₂ with | seq a₂ b₂ => cases b₂ with | seq b₂ c₂ => cases c₂ with
    | seq c₂ d₂ => cases d₂ with | seq d₂ e₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq e₁ f₁)))))
    (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq e₂ f₂)))))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- Two runs with the same public arguments have the same `prmOf`. -/
theorem prm_eq {s₁ s₂ : State} (h : onePub s₁ s₂) : prmOf s₂ = prmOf s₁ := by
  obtain ⟨q₀, q₁, q₂, q₃, q₄, qa⟩ := h
  simp only [prmOf, ← q₀, ← q₁, ← q₂, ← q₃, ← q₄, ← qa 0 (by decide), ← qa 1 (by decide), ← qa 2 (by decide),
    ← qa 3 (by decide), ← qa 4 (by decide), ← qa 5 (by decide), ← qa 6 (by decide)]

theorem entry_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint [.r0, .r1, .r2, .r3] 28) (.block entry) h).isSome =
    true := ⟨_, by taint_decide⟩

/-- The entry, in two runs with the same public arguments. -/
theorem entry_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (P₁ : Perm p σ₁) (P₂ : Perm p σ₂) (h₁ : σ₁.sp = p.SP)
    (h₂ : σ₂.sp = p.SP) (hq : onePub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  obtain ⟨-, q₀, q₁, q₂, q₃, qa⟩ := hq
  have spf := L.spf
  have hw : ∀ {σ : State}, σ.sp = p.SP → Perm p σ →
      σ.sp.toNat + 28 ≤ 2 ^ 32 ∧ ∀ r ∈ σ.wr, Region.Disjoint ⟨State.addr σ.sp, 28⟩ r := fun h P =>
    ⟨by rw [h]; omega_using [spf], fun r hr => by rw [h]; exact P.argw r hr⟩
  refine rel_arg [.r0, .r1, .r2, .r3] 28 (fun r hr => ?_) (by rw [h₁, h₂]) (hw h₁ P₁) (hw h₂ P₂)
    (fun k hk => argMem_of (j := 7) (by rw [h₁, h₂]) (by rw [h₁]; omega_using [spf]) qa k (by omega_using [hk])) entry_check
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [q₀, q₁, q₂, q₃]

/-- What the entry and `Offset_0` leave. -/
abbrev EN (p : Prm) (σ : State) (c : State) : Prop := ∃ a, EntryPost p σ a ∧ NonceOut p a c

/-- The entry and `Offset_0`. -/
theorem en_wp {p : Prm} (L : Lay p) {s₀ : State} (P : Perm p s₀) (A : Args p s₀.mem) (hsp : s₀.sp = p.SP)
    (h0 : s₀.gpr .r0 = p.K) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 p.R) (h2 : s₀.gpr .r2 = p.N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 p.nl) (hW : s₀.mem.readW (State.addr (s₀.sp + BitVec.ofNat 32 24)) 32 = p.W) :
    WP isa (.seq (.block entry) nonce) s₀ (EN p s₀) :=
  WP.seq (WP.mono (entry_wp L P hsp h0 h1 h2 h3 hW) fun a Ea =>
    WP.mono (nonce_ok L Ea.env (args_W L Ea.frame A) Ea.r4 Ea.r5) fun _ Nc => ⟨a, Ea, Nc⟩)

/-- The entry, `Offset_0` and `HASH`, in two runs with the same public
arguments. -/
theorem pre_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (P₁ : Perm p σ₁) (P₂ : Perm p σ₂) (A₁ : Args p σ₁.mem)
    (A₂ : Args p σ₂.mem) (hs₁ : σ₁.sp = p.SP) (hs₂ : σ₂.sp = p.SP)
    (h0₁ : σ₁.gpr .r0 = p.K) (h1₁ : σ₁.gpr .r1 = BitVec.ofNat 32 p.R) (h2₁ : σ₁.gpr .r2 = p.N)
    (h3₁ : σ₁.gpr .r3 = BitVec.ofNat 32 p.nl)
    (hW₁ : σ₁.mem.readW (State.addr (σ₁.sp + BitVec.ofNat 32 24)) 32 = p.W)
    (h0₂ : σ₂.gpr .r0 = p.K) (h1₂ : σ₂.gpr .r1 = BitVec.ofNat 32 p.R) (h2₂ : σ₂.gpr .r2 = p.N)
    (h3₂ : σ₂.gpr .r3 = BitVec.ofNat 32 p.nl)
    (hW₂ : σ₂.mem.readW (State.addr (σ₂.sp + BitVec.ofNat 32 24)) 32 = p.W) (hq : onePub σ₁ σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.seq (.block entry) nonce) Impl.AesOcb.Arm.hash) TT := by
  refine rel_seq (rel_seq (entry_rel L P₁ P₂ hs₁ hs₂ hq) (entry_wp L P₁ hs₁ h0₁ h1₁ h2₁ h3₁ hW₁)
    (entry_wp L P₂ hs₂ h0₂ h1₂ h2₂ h3₂ hW₂) fun a₁ a₂ E₁ E₂ => nonce_rel L E₁.env E₂.env (args_W L E₁.frame A₁)
      (args_W L E₂.frame A₂) (by rw [E₁.r4, E₂.r4]) (by rw [E₁.r5, E₂.r5]))
    (en_wp L P₁ A₁ hs₁ h0₁ h1₁ h2₁ h3₁ hW₁) (en_wp L P₂ A₂ hs₂ h0₂ h1₂ h2₂ h3₂ hW₂)
    fun _ _ ⟨a₁, E₁, N₁⟩ ⟨a₂, E₂, N₂⟩ => ?_
  have l0 : ∀ {σ a c : State}, EntryPost p σ a → NonceOut p a c →
      blockAtMem c.mem (State.addr p.W + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (lstarOf p c.mem) 0 := fun E N => by
    rw [blockAtMem_frame N.frame (by wdisj L), E.l0]
    exact congrArg (Spec.Ocb.lAt · 0) ((lstar_mut L (nonceR_mut L N.frame)).trans (lstar_W L E.frame)).symm
  exact hash_rel L N₁.env N₂.env ((args_W L E₁.frame A₁).mut L (nonceR_mut L N₁.frame))
    ((args_W L E₂.frame A₂).mut L (nonceR_mut L N₂.frame)) (l0 E₁ N₁) (l0 E₂ N₂)

theorem tagOut_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24) tagOut h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_check : ∃ h, (VG.Taint.check VG.Arm.taint (VG.Arm.Taint.ofRegs (pubRegs [])) (.block restore)
    h).isSome = true := ⟨_, by taint_decide⟩

/-- What `seal` and `open` know of a run at the entry. -/
structure Run (p : Prm) (σ : State) : Prop where
  perm : Perm p σ
  args : Args p σ.mem
  sp : σ.sp = p.SP
  r0 : σ.gpr .r0 = p.K
  r1 : σ.gpr .r1 = BitVec.ofNat 32 p.R
  r2 : σ.gpr .r2 = p.N
  r3 : σ.gpr .r3 = BitVec.ofNat 32 p.nl
  w : σ.mem.readW (State.addr (σ.sp + BitVec.ofNat 32 24)) 32 = p.W

theorem run_of {σ : State} (P : Perm (prmOf σ) σ) : Run (prmOf σ) σ :=
  ⟨P, args_of σ, rfl, rfl, (ofNat_toNat32' _).symm, rfl, (ofNat_toNat32' _).symm, rfl⟩

/-- `vg_aes_ocb_seal`, in two runs with the same public arguments. -/
theorem seal_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (R₁ : Run p σ₁) (R₂ : Run p σ₂) (hq : onePub σ₁ σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) «seal» TT := by
  unfold «seal» front
  refine rel_assoc5 (RelCT.assoc (RelCT.assoc (rel_seq (pre_rel L R₁.perm R₂.perm R₁.args R₂.args R₁.sp R₂.sp
    R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w hq)
    (WP.assoc' (pre_wp' L R₁.perm R₁.args R₁.sp R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w))
    (WP.assoc' (pre_wp' L R₂.perm R₂.args R₂.sp R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w)) fun e₁ e₂ P₁ P₂ => ?_)))
  refine rel_seq (bodySeal_rel L P₁.env P₂.env P₁.args P₂.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar])
    P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar]))
    (bodySeal_ok L P₁.env P₁.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar]))
    (bodySeal_ok L P₂.env P₂.args P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar])) fun f₁ f₂ B₁ B₂ => ?_
  refine rel_seq (tag_rel L B₁.env B₂.env (.inl rfl)) (tag_ok L B₁.env (.inl rfl)) (tag_ok L B₂.env (.inl rfl))
    fun g₁ g₂ T₁ T₂ => ?_
  have A₁ : Args p g₁.mem := (P₁.args.mut L (bodyR_mut L B₁.frame)).mut L (tagR_mut L (.inl (by decide)) T₁.frame)
  have A₂ : Args p g₂.mem := (P₂.args.mut L (bodyR_mut L B₂.frame)).mut L (tagR_mut L (.inl (by decide)) T₂.frame)
  exact rel_seqX (rel_envArg L T₁.env T₂.env A₁ A₂ [] (by simp) tagOut_check)
    (kept_of L T₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L T₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    fun _ _ K₁ K₂ => rel_env K₁.env K₂.env [] (by simp) restore_check

theorem recv_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24) recv h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem cmp_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24) cmp h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mask_check : ∃ h, (VG.Taint.check VG.Arm.taint (argTaint (pubRegs []) 24) mask h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- `vg_aes_ocb_open`, in two runs with the same public arguments. -/
theorem open_rel {p : Prm} (L : Lay p) {σ₁ σ₂ : State} (R₁ : Run p σ₁) (R₂ : Run p σ₂) (hq : onePub σ₁ σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) «open» TT := by
  unfold «open» front
  refine rel_assoc5 (RelCT.assoc (RelCT.assoc (rel_seq (pre_rel L R₁.perm R₂.perm R₁.args R₂.args R₁.sp R₂.sp
    R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w hq)
    (WP.assoc' (pre_wp' L R₁.perm R₁.args R₁.sp R₁.r0 R₁.r1 R₁.r2 R₁.r3 R₁.w))
    (WP.assoc' (pre_wp' L R₂.perm R₂.args R₂.sp R₂.r0 R₂.r1 R₂.r2 R₂.r3 R₂.w)) fun e₁ e₂ P₁ P₂ => ?_)))
  refine rel_seq (bodyOpen_rel L P₁.env P₂.env P₁.args P₂.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar])
    P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar]))
    (bodyOpen_ok L P₁.env P₁.args P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, P₁.lstar]))
    (bodyOpen_ok L P₂.env P₂.args P₂.ofs P₂.o0 P₂.ck (by rw [P₂.l0, P₂.lstar])) fun f₁ f₂ B₁ B₂ => ?_
  refine rel_seq (tag_rel L B₁.env B₂.env (.inr rfl)) (tag_ok L B₁.env (.inr rfl)) (tag_ok L B₂.env (.inr rfl))
    fun g₁ g₂ T₁ T₂ => ?_
  have A₁ : Args p g₁.mem :=
    (P₁.args.mut L (bodyR_mut L B₁.frame)).mut L (tagR_mut L (.inr ⟨by decide, by decide⟩) T₁.frame)
  have A₂ : Args p g₂.mem :=
    (P₂.args.mut L (bodyR_mut L B₂.frame)).mut L (tagR_mut L (.inr ⟨by decide, by decide⟩) T₂.frame)
  refine rel_seqX (rel_envArg L T₁.env T₂.env A₁ A₂ [] (by simp) recv_check)
    (kept_of L T₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L T₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun h₁ h₂ K₁ K₂ => ?_
  refine rel_seqX (rel_envArg L K₁.env K₂.env (K₁.args A₁) (K₂.args A₂) [] (by simp) cmp_check)
    (kept_of L K₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L K₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel)) fun i₁ i₂ M₁ M₂ => ?_
  exact rel_seqX (rel_envArg L M₁.env M₂.env (M₁.args (K₁.args A₁)) (M₂.args (K₂.args A₂)) [] (by simp) mask_check)
    (kept_of L M₁.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (kept_of L M₂.env [] (by decide +kernel) (by decide +kernel) (by decide +kernel))
    fun _ _ N₁ N₂ => rel_env N₁.env N₂.env [] (by simp) restore_check

theorem seal_ct : ConstantTime isa sealArm.pre sealArm.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have e := prm_eq hq
  have R₂ := run_of (sealPerm h₂)
  rw [e] at R₂
  exact seal_rel (lay_of h₁.2.2.1) (run_of (sealPerm h₁)) R₂ hq

theorem open_ct : ConstantTime isa openArm.pre openArm.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have e := prm_eq hq.1
  have R₂ := run_of (openPerm h₂)
  rw [e] at R₂
  exact open_rel (lay_of h₁.2.2) (run_of (openPerm h₁)) R₂ hq.1

end VG.Proof.AesOcb.Arm
