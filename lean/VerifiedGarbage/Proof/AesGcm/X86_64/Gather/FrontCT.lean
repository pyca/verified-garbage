module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.FrontFast
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.FrontFast
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyCT

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: constant time of the path of a TLS record's text

Untrusted: everything here is checked by Lean. Two runs from entry states with
the same public arguments and descriptors take the same path through
`frontTest` (`frontTest_rel`) and, for a TLS record's text, through
`frontFast` (`frontFast_rel`), whose addresses are public arguments or read
from the descriptors (each load of an address split from its use, as
`Gather/SplitCT.lean` does).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT rel_seq rel_ite rel_skip)
open VG.Proof.AesGcm.X86_64 (rel_block_split)
open VG.Proof.AesGcm.X86_64.Short (CopyPre)

theorem frontLen_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block (frontLen 256)) hc).isSome = true :=
  ⟨_, by simp only [frontLen]; taint_decide⟩

theorem frontArgs_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block frontArgs) hc).isSome = true :=
  ⟨_, by simp only [frontArgs]; taint_decide⟩

theorem ldSrc_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r10 (.mem (at_ .rsp 8))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem frontSlice_check (long : Bool) : ∃ hc, (taint.check (Taint.ofRegs [.r10, .rsp])
    (.block (frontSlice long).tail) hc).isSome = true := by
  cases long <;>
    exact ⟨_, by
      simp only [frontSlice, List.cons_append, List.nil_append, List.tail, Bool.false_eq_true, ↓reduceIte, imm]
      taint_decide⟩

theorem fZero_check : ∃ hc, (taint.check (Taint.ofRegs []) (.block [.alu .test .r11 (.reg .r11)]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem fastEntry_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block fastEntry.tail) hc).isSome = true :=
  ⟨_, by simp only [fastEntry, gCtx, gRounds]; taint_decide⟩

theorem fastLen2_check : ∃ hc, (taint.check (Taint.ofRegs [.r10]) (.block fastLen2) hc).isSome = true :=
  ⟨_, by simp only [fastLen2]; taint_decide⟩

theorem fastCopy_check : ∃ hc, (taint.check (Taint.ofRegs [.r10, .rsp]) (.block fastCopy) hc).isSome = true :=
  ⟨_, by simp only [fastCopy]; taint_decide⟩

theorem copy1_check : ∃ hc, (taint.check (Taint.ofRegs [.rsi, .rdi, .rcx, .r10])
    (.loop (.block copy1Body) .ne) hc).isSome = true :=
  ⟨_, by simp only [copy1Body, srcD, dstD]; taint_decide⟩

theorem fastArgs1_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp])
    (.block [.mov32 .rcx (imm 12), .mov .r10 (.mem (at_ .rsp 8))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem fastArgs2_check : ∃ hc, (taint.check (Taint.ofRegs [.r10, .rsp]) (.block fastArgs.tail.tail) hc).isSome =
    true := ⟨_, by simp only [fastArgs]; taint_decide⟩

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The first descriptor's address into `r10`, from a state `Same` as the entry. -/
theorem ldSrc_ok {st : State} (hs : Same s st) :
    WP isa (.block [.mov .r10 (.mem (at_ .rsp 8))]) st fun t => Same s t ∧ t.gpr .r10 = Src s := by
  obtain ⟨a₀, e₀⟩ := same_a hp hs (i := 0) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [a₀, e₀], ?_, by simp [gpr_setReg]⟩
  exact hs.step (fun r _ b _ => by simp [gpr_setReg, b]) (by simp [mem_setReg]) (by simp [rd_setReg])
    (by simp [wr_setReg])

/-- The first descriptor's address into `r10` and `rcx` set, in a state of the fast path. -/
theorem fastArgs1_ok {st : State} (h : FBase s st) :
    WP isa (.block [.mov32 .rcx (imm 12), .mov .r10 (.mem (at_ .rsp 8))]) st fun t =>
      t.gpr .r10 = Src s ∧ t.gpr .rsp = SP s := by
  obtain ⟨a₀, e₀⟩ := fa_in hp h (i := 0) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by xrun [a₀, e₀], by simp [gpr_setReg], by simp [gpr_setReg, h.rsp]⟩

end

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- The tests of `frontCore`, from two states `Same` as the entry states. -/
theorem frontCore_eq2 (long : Bool) {σ₁ σ₂ : State} (S₁ : Same s₀ σ₁) (S₂ : Same s₀' σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (frontCore long) TT := by
  have sp : ∀ {a b : State}, Same s₀ a → Same s₀' b → a.gpr .rsp = b.gpr .rsp := fun A B => by
    rw [same_rsp A, same_rsp B]; exact pb.rsp.symm
  unfold frontCore
  refine rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.rsp] (by simp [sp S₁ S₂]) frontArgs_check)
    (fArgs_ok hp S₁) (fArgs_ok hp' S₂) fun υ₁ υ₂ ⟨U₁, cf₁', r11₁⟩ ⟨U₂, cf₂', r11₂⟩ => ?_
  refine rel_seq ?_ (fMid_wp hp long U₁ cf₁' r11₁) (fMid_wp hp' long U₂ cf₂' r11₂)
    fun _ _ _ _ => ChaCha20Poly1305.X86_64.Gather.rel_regs [] (by simp) fZero_check
  refine rel_ite (b := !decide ((stackArg s₀ 1 - 1#64).toNat < (2#64).toNat))
    (by simp only [eval, cf₁', Option.map_some]) (by simp only [eval, cf₂', Option.map_some, pb.a 1 (by decide)])
    (fun _ => rel_skip) fun _ => ?_
  rw [show frontSlice long = [.mov .r10 (.mem (at_ .rsp 8))] ++ (frontSlice long).tail from rfl]
  refine rel_block_split (rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.rsp] (by simp [sp U₁ U₂]) ldSrc_check)
    (ldSrc_ok hp U₁) (ldSrc_ok hp' U₂) fun ω₁ ω₂ ⟨W₁, r10₁⟩ ⟨W₂, r10₂⟩ => ?_)
  exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.r10, .rsp] (by simp [r10₁, r10₂, pb.src, sp W₁ W₂])
    (frontSlice_check long)

/-- The test, from two states `Same` as the entry states. -/
theorem frontTest_eq2 (long : Bool) {σ₁ σ₂ : State} (S₁ : Same s₀ σ₁) (S₂ : Same s₀' σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (frontTest long) TT := by
  cases long
  · simp only [frontTest, Bool.false_eq_true, ↓reduceIte]; exact frontCore_eq2 hp hp' pb false S₁ S₂
  simp only [frontTest, ↓reduceIte]
  refine rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.rsp]
      (by simp [same_rsp S₁, same_rsp S₂, pb.rsp]) frontLen_check) (fLen_ok hp S₁) (fLen_ok hp' S₂)
    fun τ₁ τ₂ ⟨T₁, cf₁, _⟩ ⟨T₂, cf₂, _⟩ => ?_
  exact rel_ite (b := decide ((stackArg s₀ 3).toNat < (256#64).toNat))
    (by simp only [eval, cf₁]) (by simp only [eval, cf₂, pb.a 3 (by decide)]) (fun _ => rel_skip)
    fun _ => frontCore_eq2 hp hp' pb true T₁ T₂

/-- The test, in two runs from the entry states. -/
theorem frontTest_rel (long : Bool) :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (frontTest long) fun s₁ s₂ =>
      (Same s₀ s₁ ∧ s₁.zf = some (frontGo long s₀)) ∧ (Same s₀' s₂ ∧ s₂.zf = some (frontGo long s₀')) :=
  pstep (F₁ := (· = s₀)) (F₂ := (· = s₀'))
    (rel_of_eq2 fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h; exact frontTest_eq2 hp hp' pb long (Same.refl _) (Same.refl _))
    (fun _ h => by rw [h]; exact frontTest_wp hp long) (fun _ h => by rw [h]; exact frontTest_wp hp' long)


/-- The path of a TLS record's text, from two states `Same` as the entry states. -/
theorem frontFast_eq2 (S : SplitFn M) {long : Bool} (hg : frontGo long s₀ = true) {σ₁ σ₂ : State}
    (S₁ : Same s₀ σ₁) (S₂ : Same s₀' σ₂) : RelCT isa (Eq2 σ₁ σ₂) (frontFast S.fn) TT := by
  have hg' : frontGo long s₀' = true := by rw [pb.eFront]; exact hg
  obtain ⟨hn, hcnt, hsub⟩ := front_facts hp hg
  obtain ⟨hn', hcnt', hsub'⟩ := front_facts hp' hg'
  have ec := pb.cnt
  unfold frontFast
  refine rel_seq ?_ (fastEntry_ok hp S₁) (fastEntry_ok hp' S₂) fun τ₁ τ₂ ⟨F₁, r10₁, zf₁⟩ ⟨F₂, r10₂, zf₂⟩ => ?_
  · rw [show fastEntry = .mov .r11 (.mem (at_ .rsp 48)) :: fastEntry.tail from rfl]
    refine rel_wt [.rsp] (by simp) (fun _ _ h r hr => ?_) (fun _ _ h => ?_) fastEntry_check
    · obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr
      rw [same_rsp S₁, same_rsp S₂]; exact pb.rsp.symm
    · obtain ⟨rfl, rfl⟩ := h
      obtain ⟨a₁, e₁⟩ := same_a hp S₁ (i := 5) (by decide)
      obtain ⟨a₂, e₂⟩ := same_a hp' S₂ (i := 5) (by decide)
      exact ⟨by rw [e₁, e₂]; exact pb.w.symm, a₁, a₂⟩
  refine rel_seq ?_ (fastTail_wp hp hcnt hsub F₁ r10₁ zf₁) (fastTail_wp hp' hcnt' hsub' F₂ r10₂ zf₂)
    fun υ₁ υ₂ ⟨G₁, O₁⟩ ⟨G₂, O₂⟩ => ?_
  · refine rel_ite (b := decide (Cnt s₀ = 1)) (by simp only [eval, zf₁]) (by simp only [eval, zf₂, ec])
      (fun _ => rel_skip) fun e => ?_
    have hc : Cnt s₀ = 2 := by have : Cnt s₀ ≠ 1 := by simpa using e
                               omega
    have hc' : Cnt s₀' = 2 := by rw [ec]; exact hc
    refine rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r10] (by simp [r10₁, r10₂, pb.src]) fastLen2_check)
      (fastLen2_ok hp hc F₁ r10₁) (fastLen2_ok hp' hc' F₂ r10₂) fun ω₁ ω₂ ⟨H₁, r10₁', cx₁, zf₁'⟩ ⟨H₂, r10₂', cx₂, zf₂'⟩ => ?_
    have esl : sl s₀' 1 = sl s₀ 1 := pb.sl (by omega)
    refine rel_ite (b := decide (sl s₀ 1 = 0)) (by simp only [eval, zf₁']) (by simp only [eval, zf₂', esl])
      (fun _ => rel_skip) fun e => ?_
    have hgl := gl_two hp hc
    have hgl' := gl_two hp' hc'
    have hfl := fl_le hp
    refine rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r10, .rsp]
        (by simp [r10₁', r10₂', pb.src, H₁.rsp, H₂.rsp, SP, pb.rsp]) fastCopy_check)
      (fastCopy_ok hp hc (by omega) H₁ r10₁' cx₁) (fastCopy_ok hp' hc' (by rw [esl]; omega) H₂ r10₂' cx₂)
      fun ξ₁ ξ₂ ⟨_, P₁, i₁⟩ ⟨_, P₂, i₂⟩ => ?_
    exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.rsi, .rdi, .rcx, .r10]
      (by simp [P₁.rsi, P₂.rsi, P₁.rdi, P₂.rdi, P₁.rcx, P₂.rcx, i₁, i₂, pb.sb (show 1 < Cnt s₀ by omega), pb.dst,
        pb.eFl, esl]) copy1_check
  refine rel_seq ?_ (fastArgs_ok hp hn (by omega) G₁ O₁) (fastArgs_ok hp' hn' (by omega) G₂ O₂)
    fun ω₁ ω₂ ⟨B₁, R₁⟩ ⟨B₂, R₂⟩ => splitCall_rel hp hp' pb S B₁ R₁ B₂ R₂
  rw [show fastArgs = [.mov32 .rcx (imm 12), .mov .r10 (.mem (at_ .rsp 8))] ++ fastArgs.tail.tail from rfl]
  refine rel_block_split (rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.rsp]
      (by simp [G₁.rsp, G₂.rsp, SP, pb.rsp]) fastArgs1_check) (fastArgs1_ok hp G₁) (fastArgs1_ok hp' G₂)
    fun _ _ a b => ?_)
  exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.r10, .rsp] (by simp [a.1, b.1, a.2, b.2, pb.src, SP, pb.rsp])
    fastArgs2_check

end

end VG.Proof.AesGcm.X86_64.Gather
