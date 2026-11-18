module

public import VerifiedGarbage.Proof.Gcm.PrecomputedContract
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.FrontFast
import VerifiedGarbage.Proof.AesGcm.X86_64.VerifiedP
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.CT
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.AesSiv.X86_64.Verified
import VerifiedGarbage.Proof.AesGcm.ScratchGather
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.FrontFast
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Impl.AesGcm.X86_64.SealGather
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Callee
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx512
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Gcm.Ctr
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Gcm.Stream

/-! ### `AesGcm.X86_64.Gather.FrontCT`, which only this module used -/

section

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
                               omega_arith
    have hc' : Cnt s₀' = 2 := by rw [ec]; exact hc
    refine rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r10] (by simp [r10₁, r10₂, pb.src]) fastLen2_check)
      (fastLen2_ok hp hc F₁ r10₁) (fastLen2_ok hp' hc' F₂ r10₂) fun ω₁ ω₂ ⟨H₁, r10₁', cx₁, zf₁'⟩ ⟨H₂, r10₂', cx₂, zf₂'⟩ => ?_
    have esl : sl s₀' 1 = sl s₀ 1 := pb.sl (by omega_arith)
    refine rel_ite (b := decide (sl s₀ 1 = 0)) (by simp only [eval, zf₁']) (by simp only [eval, zf₂', esl])
      (fun _ => rel_skip) fun e => ?_
    have hgl := gl_two hp hc
    have hgl' := gl_two hp' hc'
    have hfl := fl_le hp
    refine rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r10, .rsp]
        (by simp [r10₁', r10₂', pb.src, H₁.rsp, H₂.rsp, SP, pb.rsp]) fastCopy_check)
      (fastCopy_ok hp hc (by omega_arith) H₁ r10₁' cx₁) (fastCopy_ok hp' hc' (by rw [esl]; omega_arith) H₂ r10₂' cx₂)
      fun ξ₁ ξ₂ ⟨_, P₁, i₁⟩ ⟨_, P₂, i₂⟩ => ?_
    exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.rsi, .rdi, .rcx, .r10]
      (by simp [P₁.rsi, P₂.rsi, P₁.rdi, P₂.rdi, P₁.rcx, P₂.rcx, i₁, i₂, pb.sb (show 1 < Cnt s₀ by omega_arith), pb.dst,
        pb.eFl, esl]) copy1_check
  refine rel_seq ?_ (fastArgs_ok hp hn (by omega_arith) G₁ O₁) (fastArgs_ok hp' hn' (by omega_arith) G₂ O₂)
    fun ω₁ ω₂ ⟨B₁, R₁⟩ ⟨B₂, R₂⟩ => splitCall_rel hp hp' pb S B₁ R₁ B₂ R₂
  rw [show fastArgs = [.mov32 .rcx (imm 12), .mov .r10 (.mem (at_ .rsp 8))] ++ fastArgs.tail.tail from rfl]
  refine rel_block_split (rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.rsp]
      (by simp [G₁.rsp, G₂.rsp, SP, pb.rsp]) fastArgs1_check) (fastArgs1_ok hp G₁) (fastArgs1_ok hp' G₂)
    fun _ _ a b => ?_)
  exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.r10, .rsp] (by simp [a.1, b.1, a.2, b.2, pb.src, SP, pb.rsp])
    fastArgs2_check

end

end VG.Proof.AesGcm.X86_64.Gather

end

end

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
of `vg_aes_gcm_seal_gather` calling any `vg_aes_gcm_stream_init`,
`vg_aes_gcm_stream_aad`, `vg_aes_gcm_stream_encrypt_to` and
`vg_aes_gcm_stream_finish` (`CallFn`), its code's static facts (no load of
`mxcsr`, `rsp` written only in frames, 4888 bytes of stack), the shared
contracts with a `scratch` buffer appended (`sealGatherScratchContract`),
and the shared contracts of `Spec/Gcm/OutOfPlace.lean` in a frame of 240
bytes holding the working space (`Verified.stackArgScratchL`): its 184
bytes, a copy of the five other stack arguments, and 16 more, for 5128
bytes of stack in all; for the key contexts of `vg_aes_gcm_init` and
`vg_aes_gcm_init_precomputed`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT)
open VG.Proof.AesSiv.X86_64 (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

/-! ## The callees -/

theorem framedS_mx {bytes : Nat} {r : Reg} {c : Prog isa} (h : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    (Impl.StackScratch.X86_64.withStackScratch bytes r c).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq] at h ⊢
  simp only [Impl.StackScratch.X86_64.withStackScratch, instrs, List.all_append, List.all_cons, List.all_nil, h,
    Bool.and_true, Bool.true_and]
  rfl

theorem framedS_xdepth {bytes d : Nat} {r : Reg} {c : Prog isa} (h : c.x86_64Depth ≤ d) :
    (Impl.StackScratch.X86_64.withStackScratch bytes r c).x86_64Depth ≤ d + bytes := by
  simp only [Impl.StackScratch.X86_64.withStackScratch, Code.x86_64Depth, X86_64.Instr.frameBytes]
  omega_using [h]

/-! ## The code -/

/-- A short path of `vg_aes_gcm_seal_gather`: a test that sets `CF` to `go`
of the arguments, which two runs with the same public data agree on, and the
code it runs then, with what correctness, constant time and the static facts
need of them. -/
structure ShortFn (M : CtxMode) where
  q : Nat
  quick : Prog isa
  quickWp : ∀ {s : State}, SG M s → ∀ st, E2 s st → WP isa quick st fun st' =>
    E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (decide (L s < q))
  quickRel : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' →
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) quick fun s₁ s₂ =>
      (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (decide (L s₀ < q))) ∧
      (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (decide (L s₀' < q)))
  quickMx : quick.allInstrs (fun i => !loadsMxcsr i) = true
  quickSp : quick.all (fun i => !X86_64.isa.writesSp i) = true
  quickXd : quick.x86_64Depth ≤ 4888
  fast : Prog isa
  fastWp : ∀ {s : State}, SG M s → L s < q → ∀ st, E2 s st → st.gpr .r11 = W s → WP isa fast st (Done s)
  fastRel : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → L s₀ < q → ∀ {σ₁ σ₂ : State},
    E2 s₀ σ₁ → σ₁.gpr .r11 = W s₀ → E2 s₀' σ₂ → σ₂.gpr .r11 = W s₀' → RelCT isa (Eq2 σ₁ σ₂) fast TT
  fastMx : fast.allInstrs (fun i => !loadsMxcsr i) = true
  fastSp : fast.all (fun i => !X86_64.isa.writesSp i) = true
  fastXd : fast.x86_64Depth ≤ 4888
  test : Prog isa
  code : Prog isa
  go : State → Bool
  hgo : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → go s₀' = go s₀
  testWp : ∀ {s : State}, SG M s → ∀ st, E2 s st →
    WP isa test st fun st' => E2 s st' ∧ st'.gpr .r11 = W s ∧ st'.cf = some (go s)
  testRel : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' →
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) test fun s₁ s₂ =>
      (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (go s₀)) ∧
      (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (go s₀'))
  wp : ∀ {s : State}, SG M s → go s = true → ∀ st, E2 s st → st.gpr .r11 = W s → WP isa code st (Done s)
  rel : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → go s₀ = true → ∀ {σ₁ σ₂ : State},
    E2 s₀ σ₁ → σ₁.gpr .r11 = W s₀ → E2 s₀' σ₂ → σ₂.gpr .r11 = W s₀' → RelCT isa (Eq2 σ₁ σ₂) code TT
  testMx : test.allInstrs (fun i => !loadsMxcsr i) = true
  codeMx : code.allInstrs (fun i => !loadsMxcsr i) = true
  testSp : test.all (fun i => !X86_64.isa.writesSp i) = true
  codeSp : code.all (fun i => !X86_64.isa.writesSp i) = true
  testXd : test.x86_64Depth ≤ 4888
  codeXd : code.x86_64Depth ≤ 4888

/-- The test of the texts the short path takes, whatever the threshold. -/
theorem splitTest_mx (t : Nat) : (splitTest t : Prog isa).allInstrs (fun i => !loadsMxcsr i) = true := rfl
theorem splitTest_spAll (t : Nat) : (splitTest t : Prog isa).all (fun i => !X86_64.isa.writesSp i) = true := rfl
theorem splitTest_xdepth (t : Nat) : (splitTest t : Prog isa).x86_64Depth = 0 := rfl

/-- The short path, for a text shorter than `t` bytes or whose first slice
holds all its whole blocks: sealed from its first slice by `Sp`
(`vg_aes_gcm_seal_split`) if that slice holds all the whole blocks and at
least `ts` bytes, and otherwise copied whole to the output and sealed there
by `Se` (`vg_aes_gcm_seal`). -/
def ShortFn.ofBoth {M : CtxMode} (Se : SealFn M) (Sp : SplitFn M) {t ts : Nat} (ht : t < 2 ^ 31) (hts : 1 ≤ ts)
    (htt : ts + 16 ≤ t) : ShortFn M where
  q := ts
  quick := .block (quickTest ts)
  quickWp := fun hp _ h => w_quick hp (by omega_using [ht, htt]) h
  quickRel := fun hp hp' pb => quick_rel hp hp' pb (by omega_using [ht, htt])
  quickMx := rfl
  quickSp := rfl
  quickXd := Nat.zero_le _
  fast := copySeal Se.fn
  fastWp := fun hp e st E r11 => sealShort_wp hp Se ht (by simp only [decide_eq_true_eq]; omega_using [htt, e]) st E r11
  fastRel := fun hp hp' pb e _ _ E₁ r₁ E₂ r₂ => sealShort_rel Se hp hp' pb
    (by simp only [decide_eq_true_eq]; omega_using [htt, e]) ht E₁ r₁ E₂ r₂
  fastMx := by
    simp only [copySeal, gatherCopy, copy, Code.allInstrs, Se.mx, Bool.true_and, Bool.and_true]
    rfl
  fastSp := by
    simp only [copySeal, gatherCopy, copy, Code.all, Se.spAll, Bool.true_and, Bool.and_true]
    rfl
  fastXd := by
    have s₀ := Se.xd
    simp only [copySeal, gatherCopy, copy, Code.x86_64Depth, X86_64.Instr.frameBytes, List.length_cons,
      List.length_nil, Nat.max_le]
    omega_using [s₀]
  test := splitTest t
  code := copyShort ts Se.fn Sp.fn
  go s := decide (shortLen s < t)
  hgo := fun _ _ pb => by simp only [shortLen, pb.eL, pb.eFl]
  testWp := fun hp _ h => splitTest_wp hp ht h
  testRel := fun hp hp' pb => splitTest_rel hp hp' pb ht
  wp := fun {s} hp e st E r11 => by
    have hs : shortLen s < t := by simpa using e
    unfold copyShort
    refine WP.seq (WP.mono (selTest_wp hp (ts := ts) (by omega_using [ht, htt]) E) fun st' ⟨E', r11', cf'⟩ => ?_)
    refine WP.ite (decide (selLen s < ts)) (by simp only [eval, cf']) (fun h => ?_) (fun h => ?_)
    · exact sealShort_wp hp Se ht (by simpa using lt_of_sel hp htt hs (by simpa using h)) st' E' r11'
    · exact copySplit_wp hp Sp (sub_lt_of_sel hp hts (by simpa using h)) E'.1 r11' E'.2.2.1 E'.2.2.2.1
  rel := fun {s₀ s₀'} hp hp' pb e σ₁ σ₂ E₁ r₁ E₂ r₂ => by
    have hs : shortLen s₀ < t := by simpa using e
    have esel : selLen s₀' = selLen s₀ := by simp only [selLen, pb.eL, pb.eFl]
    unfold copyShort
    refine RelCT.seq (R := fun (a b : State) => (E2 s₀ a ∧ a.gpr .r11 = W s₀ ∧ a.cf = some (decide (selLen s₀ < ts))) ∧
        (E2 s₀' b ∧ b.gpr .r11 = W s₀' ∧ b.cf = some (decide (selLen s₀' < ts))))
      ((selTest_rel hp hp' pb (ts := ts) (by omega_using [ht, htt])).mono (fun a b h => by rw [h.1, h.2]; exact ⟨E₁, E₂⟩)
        fun _ _ h => h)
      (RelCT.ite (fun _ _ g => by simp only [eval, g.1.2.2, g.2.2.2, esel]) ?_ ?_)
    · refine StreamTo.RelCT.of_imp (selLen s₀ < ts) (fun _ _ g => by
        have c := g.2; simp only [eval, g.1.1.2.2] at c; simpa using c) fun h => ?_
      exact rel_of_eq2 fun _ _ g => sealShort_rel Se hp hp' pb (by simpa using lt_of_sel hp htt hs h) ht g.1.1.1
        g.1.1.2.1 g.1.2.1 g.1.2.2.1
    · refine StreamTo.RelCT.of_imp (¬selLen s₀ < ts) (fun _ _ g => by
        have c := g.2; simp only [eval, g.1.1.2.2] at c; simpa using c) fun h => ?_
      exact rel_of_eq2 fun _ _ g => splitShort_rel Sp hp hp' pb e ht g.1.1.1 g.1.1.2.1 g.1.2.1 g.1.2.2.1
  testMx := splitTest_mx t
  codeMx := by
    simp only [copyShort, selTest, lenTest, selLast, copySeal, copySplit, gatherCopy, copy, Code.allInstrs, Se.mx,
      Sp.mx, Bool.true_and, Bool.and_true]
    rfl
  testSp := splitTest_spAll t
  codeSp := by
    simp only [copyShort, selTest, lenTest, selLast, copySeal, copySplit, gatherCopy, copy, Code.all, Se.spAll,
      Sp.spAll, Bool.true_and, Bool.and_true]
    rfl
  testXd := by rw [splitTest_xdepth]; decide
  codeXd := by
    have s₀ := Se.xd
    have s₁ := Sp.xd
    simp only [copyShort, selTest, lenTest, selLast, copySeal, copySplit, gatherCopy, copy, Code.x86_64Depth,
      X86_64.Instr.frameBytes, List.length_cons, List.length_nil, Nat.max_le]
    omega_using [s₀, s₁]

section
variable {M : CtxMode} (Sh : ShortFn M) (I : InitFn) (A : AadFn) (T : ToFn M) (F : FinFn)

theorem sealGather_mx (inl : Bool := false) : (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl).allInstrs (fun i => !loadsMxcsr i) = true := by
  cases inl <;>
  simp only [sealGather, gatherRest, Code.allInstrs, Sh.quickMx, Sh.fastMx, Sh.testMx, Sh.codeMx, stream, text, slices, I.mx, A.mx, T.mx, F.mx,
    callOr, Bool.false_eq_true, ↓reduceIte, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem sealGather_spAll (inl : Bool := false) :
    (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl).all (fun i => !X86_64.isa.writesSp i) = true := by
  cases inl <;>
  simp only [sealGather, gatherRest, Code.all, Sh.quickSp, Sh.fastSp, Sh.testSp, Sh.codeSp, stream, text, slices, I.spAll, A.spAll, T.spAll,
    F.spAll, callOr, Bool.false_eq_true, ↓reduceIte, Bool.true_and, Bool.and_true] <;>
  decide +kernel

theorem sealGather_xdepth (inl : Bool := false) : (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl).x86_64Depth ≤ 4888 := by
  have s₃ := Sh.quickXd
  have s₂ := Sh.fastXd
  have s₀ := Sh.testXd
  have s₁ := Sh.codeXd
  have i := I.xd
  have a := A.xd
  have tt := T.xd
  have f := F.xd
  cases inl <;>
  simp only [sealGather, gatherRest, stream, text, slices, callOr, Bool.false_eq_true, ↓reduceIte, Code.x86_64Depth,
    X86_64.Instr.frameBytes, List.length_cons, List.length_nil, Nat.max_le] <;>
  omega_using [s₃, s₂, s₀, s₁, i, a, tt, f]

theorem sealGather_correct (inl : Bool) (s : State) (hs : (Proof.AesGcm.sealGatherX86_64M M).pre s) :
    ∃ tr s', Exec isa (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl) s tr s' ∧ abiPreserved s s' ∧
      Proof.AesGcm.sealGatherPostG s s' := by
  have hp := SG.ofM hs
  obtain ⟨tr, s', he, hg, hpo⟩ := sealGatherG_wp hp (go := Sh.go s) (fun _ h => Sh.quickWp hp _ h)
    (fun e st E r11 => Sh.fastWp hp e st E r11) (fun st h => Sh.testWp hp st h)
    (fun e st E r11 => Sh.wp hp e st E r11) inl I A T F (Same.refl s)
  exact ⟨tr, s', he, abiPreserved_of_exec (sealGather_mx Sh I A T F inl) he hg, hpo⟩

theorem sealGather_ct (inl : Bool := false) :
    ConstantTime isa (Proof.AesGcm.sealGatherX86_64M M).pre Proof.AesGcm.sealGatherPub
      (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl) :=
  sealGatherG_ct Sh.go Sh.hgo Sh.quickRel Sh.fastRel Sh.testRel Sh.rel inl I A T F

end


/-! ## With the path of a TLS record's text first -/

section
variable {M : CtxMode} (Sh : ShortFn M) (I : InitFn) (A : AadFn) (T : ToFn M) (F : FinFn) (Sp : SplitFn M)
  (long : Bool)

theorem withFront_mx (inl : Bool := false) : (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl)).allInstrs
    (fun i => !loadsMxcsr i) = true := by
  simp only [withFront, frontTest, frontFast, Code.allInstrs, sealGather_mx Sh I A T F inl, Sp.mx, Bool.true_and,
    Bool.and_true]
  cases long <;> decide +kernel

theorem withFront_spAll (inl : Bool := false) : (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl)).all
    (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [withFront, frontTest, frontFast, Code.all, sealGather_spAll Sh I A T F inl, Sp.spAll, Bool.true_and,
    Bool.and_true]
  cases long <;> decide +kernel

theorem withFront_xdepth (inl : Bool := false) :
    (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl)).x86_64Depth ≤ 4888 := by
  have s₀ := sealGather_xdepth Sh I A T F inl
  have s₁ := Sp.xd
  cases long <;> simp only [withFront, frontTest, frontCore, frontFast, Code.x86_64Depth, X86_64.Instr.frameBytes,
    List.length_cons, List.length_nil, Nat.max_le, Bool.false_eq_true, ↓reduceIte] <;> omega_using [s₀, s₁]

theorem withFront_correct (inl : Bool) (s : State) (hs : (Proof.AesGcm.sealGatherX86_64M M).pre s) :
    ∃ tr s', Exec isa (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl))
      s tr s' ∧ abiPreserved s s' ∧ Proof.AesGcm.sealGatherPostG s s' := by
  have hp := SG.ofM hs
  have w : WP isa (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl)) s
      (Done s) := by
    unfold withFront
    exact WP.seq (WP.mono (frontTest_wp hp long) fun st ⟨S, zf⟩ =>
      WP.ite (frontGo long s) (by simp only [eval, zf]) (fun e => frontFast_wp hp Sp e S)
        (fun _ => sealGatherG_wp hp (go := Sh.go s) (fun _ h => Sh.quickWp hp _ h)
          (fun e st E r11 => Sh.fastWp hp e st E r11) (fun st h => Sh.testWp hp st h)
          (fun e st E r11 => Sh.wp hp e st E r11) inl I A T F S))
  obtain ⟨tr, s', he, hg, hpo⟩ := w
  exact ⟨tr, s', he, abiPreserved_of_exec (withFront_mx Sh I A T F Sp long inl) he hg, hpo⟩

theorem withFront_ct (inl : Bool := false) :
    ConstantTime isa (Proof.AesGcm.sealGatherX86_64M M).pre Proof.AesGcm.sealGatherPub
      (withFront long Sp.fn (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn inl)) := by
  refine ct_of_rel (k := Proof.AesGcm.sealGatherX86_64M M) fun s₀ s₀' h h' hq => ?_
  have hp := SG.ofM h
  have hp' := SG.ofM h'
  have pb := Pub.of hq
  unfold withFront
  refine RelCT.seq (frontTest_rel hp hp' pb long)
    (RelCT.ite (fun _ _ h => by simp only [eval, h.1.2, h.2.2, pb.eFront]) ?_ ?_)
  · refine rel_of_eq2 fun σ₁ σ₂ ⟨⟨⟨S₁, z₁⟩, ⟨S₂, _⟩⟩, ev⟩ => ?_
    have e : frontGo long s₀ = true := by simp only [eval, z₁] at ev; simpa using ev
    exact frontFast_eq2 hp hp' pb Sp e S₁ S₂
  · exact (sealGatherG_rel Sh.go Sh.hgo Sh.quickRel Sh.fastRel Sh.testRel Sh.rel inl I A T F hp hp' pb).mono
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h

end

/-! ## The contracts -/

theorem stackArgs_six (s : State) : List.map (stackArg s) (List.range 6) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5] := rfl

set_option linter.unusedSimpArgs false in
theorem gatherPre_of {s : State} (h : (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888).pre s) :
    Proof.AesGcm.sealGatherPreM CtxMode.base s := by
  sig_pre [Proof.AesGcm.sealGatherScratchContract, Proof.AesGcm.sealGatherScratchSig, Spec.Gcm.sealGatherPre,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  -- the conjuncts in one step each level (`sig_split`), not a `cases` for each of the fifty names
  sig_split h
  rename_i w₁ w₂ rd wr g₁ _ _ _ rdd rt rw g₂ ok on oa od ot ow g₃ hr
  sig_split g₁
  rename_i kd kt kw nd nt nw ad at_ aw dt dw dds dd tw tds tt wds wl
  sig_split g₂
  rename_i _ _ bk bn ba bd bt bw bds bl
  obtain ⟨dl, da⟩ := dd
  obtain ⟨tl, ta⟩ := tt
  obtain ⟨ods, ol⟩ := g₃
  simp only [Proof.AesGcm.sealGatherPreM, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, Proof.AesGcm.stkG,
    Proof.AesGcm.slicesG, Proof.AesGcm.rounds, VG.X86_64.below, CtxMode.base]
  simp only [show (2 * (64 / 8) : Nat) = 16 from rfl] at *
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, dds.symm, tds.symm, wds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm, (wl r hr').symm⟩, dt, dw, tw, da, ta, g₁, rdd, rt, rw,
    bk, bn, ba, bds, bl, bd, bt, bw, ok, on, oa, ods, ol, od, ot, ow, w₁, w₂, hr, h, trivial⟩

set_option linter.unusedSimpArgs false in
theorem gatherPreP_of {s : State}
    (h : (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888).pre s) :
    Proof.AesGcm.sealGatherPreM CtxMode.powers s := by
  sig_pre [Proof.AesGcm.sealGatherPrecomputedScratchContract, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Proof.Gcm.sealGatherPrecomputedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at h
  rw [Sig.pairFacts, Sig.pairFacts, Sig.pairFacts, pairFacts_ro _ (by simp)] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or, Bool.or_true,
    Bool.false_or, Bool.or_false, List.cons_append, List.singleton_append, Sig.descRegion] at h
  sig_split h
  rename_i w₁ w₂ rd wr g₁ _ _ _ rdd rt rw g₂ ok on oa od ot ow g₃ hr hg
  sig_split g₁
  rename_i kd kt kw nd nt nw ad at_ aw dt dw dds dd tw tds tt wds wl
  sig_split g₂
  rename_i _ _ bk bn ba bd bt bw bds bl
  obtain ⟨dl, da⟩ := dd
  obtain ⟨tl, ta⟩ := tt
  obtain ⟨ods, ol⟩ := g₃
  simp only [Proof.AesGcm.sealGatherPreM, Proof.AesGcm.arg, Proof.AesGcm.args, Proof.AesGcm.ret, Proof.AesGcm.stkG,
    Proof.AesGcm.slicesG, Proof.AesGcm.rounds, VG.X86_64.below, CtxMode.powers]
  simp only [show (2 * (64 / 8) : Nat) = 16 from rfl] at *
  exact ⟨rd, wr, kd, kt, kw, nd, nt, nw, ad, at_, aw, dds.symm, tds.symm, wds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm, (wl r hr').symm⟩, dt, dw, tw, da, ta, g₁, rdd, rt, rw,
    bk, bn, ba, bds, bl, bd, bt, bw, ok, on, oa, ods, ol, od, ot, ow, w₁, w₂, hr, hg, h⟩


theorem gatherPost_of {s s' : State} (h : Proof.AesGcm.sealGatherPostG s s') :
    (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888).post s s' := by
  sig_post [Proof.AesGcm.sealGatherScratchContract, Proof.AesGcm.sealGatherScratchSig, Proof.AesGcm.sealGatherRoundsPost,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888).pub s₁ s₂) :
    Proof.AesGcm.sealGatherPub s₁ s₂ := by
  sig_pub_keep [Proof.AesGcm.sealGatherScratchContract, Proof.AesGcm.sealGatherScratchSig, Spec.Gcm.sealGatherPre,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, qMd, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, fun i hi => hd i (by simpa using hi), qMd⟩

theorem gatherPostP_of {s s' : State} (h : Proof.AesGcm.sealGatherPostG s s') :
    (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888).post s s' := by
  sig_post [Proof.AesGcm.sealGatherPrecomputedScratchContract, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Proof.AesGcm.sealGatherRoundsPost, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq]
  exact fun _ _ => h

theorem gatherPubP_of {s₁ s₂ : State}
    (hp : (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888).pub s₁ s₂) :
    Proof.AesGcm.sealGatherPub s₁ s₂ := by
  sig_pub_keep [Proof.AesGcm.sealGatherPrecomputedScratchContract, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Proof.Gcm.sealGatherPrecomputedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] at hp
  simp only [List.getD_cons_succ, List.getD_cons_zero, Sig.descRegion] at hp
  obtain ⟨q₇, qMd, q₁, q₂, q₃, q₄, q₅, q₆, a₀, a₁, a₂, a₃, a₄, a₅, hd⟩ := hp
  exact ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂, a₃, a₄, a₅, fun i hi => hd i (by simpa using hi), qMd⟩

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather` with its
working space: no slices, no nonce, additional data or text; the tag at
`0x5000`, the working space at `0x6000`. -/
def gatherSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x9000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x9000 ≤ a.toNat then
    (if a = 0x9009 then 0x40 else if a = 0x9029 then 0x50 else if a = 0x9031 then 0x60 else 0) else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 48⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩, ⟨0x6000, 184⟩]

theorem gatherSat_pre : ∃ s, (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888).pre s := by
  sig_implies_sat [Proof.AesGcm.sealGatherScratchContract, Proof.AesGcm.sealGatherScratchSig, Spec.Gcm.sealGatherPre,
    X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq] [gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using gatherSat


/-- The key context at `0x1000` is below the stack arguments. -/
theorem ctx_low {i : Nat} (hi : i < 128 * 8) : ¬ (0x9000 ≤ (0x1000 + BitVec.ofNat 64 i : Addr).toNat) := by
  have h : (0x1000 : Addr).toNat = 4096 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega_using [hi]), h]
  omega_using [hi]

/-- `gatherSat`, with a key context of 1024 bytes. -/
def gatherSatP : State :=
  { gatherSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 48⟩] }

theorem gatherSatP_pre : ∃ s, (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888).pre s := by
  refine ⟨gatherSatP, ?_⟩
  sig_pre [Proof.AesGcm.sealGatherPrecomputedScratchContract, Proof.AesGcm.sealGatherPrecomputedScratchSig,
    Proof.Gcm.sealGatherPrecomputedPre, X86_64.abi, X86_64.argRegs, stackArgs_six, List.append_eq,
    gatherSatP, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem gather_implies : (Proof.AesGcm.sealGatherX86_64M CtxMode.base).Implies
    (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888) :=
  ⟨fun _ h => gatherPre_of h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem gatherP_implies : (Proof.AesGcm.sealGatherX86_64M CtxMode.powers).Implies
    (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888) :=
  ⟨fun _ h => gatherPreP_of h, fun _ _ _ h => gatherPostP_of h, fun _ _ _ _ h => gatherPubP_of h, gatherSatP_pre⟩

theorem sealGather_core (Sh : ShortFn CtxMode.base) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.base) (F : FinFn) :
    Verified X86_64.target (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn)
      (Proof.AesGcm.sealGatherScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M CtxMode.base) (sealGather_correct Sh I A T F false)
    (sealGather_ct Sh I A T F) gather_implies

theorem sealGatherP_core (Sh : ShortFn CtxMode.powers) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.powers) (F : FinFn) :
    Verified X86_64.target (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn)
      (Proof.AesGcm.sealGatherPrecomputedScratchContract X86_64.abi 4888) :=
  Verified.of_correct (k := Proof.AesGcm.sealGatherX86_64M CtxMode.powers) (sealGather_correct Sh I A T F false)
    (sealGather_ct Sh I A T F) gatherP_implies

/-! ## In its frame -/

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather`, without
the working space. -/
def gatherFrameSat : State :=
  { gatherSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 40⟩]
                   wr := [⟨0, 0⟩, ⟨0x5000, 16⟩] }

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

theorem gatherFrameSat_pre : ∃ s, (Proof.AesGcm.sealGatherRoundsContract X86_64.abi 5128).pre s := by
  sig_implies_sat [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre,
    X86_64.abi, X86_64.argRegs, stackArgs_five, List.append_eq]
    [gatherFrameSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using gatherFrameSat

theorem sealGather_framed (Sh : ShortFn CtxMode.base) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.base) (F : FinFn) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5 (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn))
      (Proof.AesGcm.sealGatherRoundsContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (hpostOut := fun vs m m₁ m₂ r hl _ hb _ => (Proof.AesGcm.sealGatherPostOut_local _) vs m m₁ m₂ r hl hb) (sig := Spec.Gcm.sealGatherSig) (nm := "scratch") (e := .u64) (n := 23)
    (pre := Spec.Gcm.sealGatherPre X86_64.abi.ptrBits) (post := Proof.AesGcm.sealGatherRoundsPost X86_64.abi.ptrBits)
    (wa := true) (stack := 4888) (bytes := 240) (sealGather_core Sh I A T F) (by decide) (by decide) (by decide)
    (sealGather_spAll Sh I A T F) (sealGather_xdepth Sh I A T F) (Proof.AesGcm.sealGatherPre_local _)
    (Proof.AesGcm.sealGatherPost_local _) gatherFrameSat_pre

/-- `gatherFrameSat`, with a key context of 1024 bytes. -/
def gatherFrameSatP : State :=
  { gatherFrameSat with rd := [⟨0x1000, 1024⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 40⟩] }

theorem gatherFrameSatP_pre : ∃ s, (Proof.AesGcm.sealGatherPrecomputedRoundsContract X86_64.abi 5128).pre s := by
  refine ⟨gatherFrameSatP, ?_⟩
  sig_pre [Proof.AesGcm.sealGatherPrecomputedRoundsContract, Proof.Gcm.sealGatherPrecomputedSig,
    Proof.Gcm.sealGatherPrecomputedPre, X86_64.abi, X86_64.argRegs, stackArgs_five, List.append_eq,
    gatherFrameSatP, gatherFrameSat, gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact powersRepr_of_zero fun _ hi => by simp only [ctx_low hi, ite_false]

theorem sealGatherP_framed (Sh : ShortFn CtxMode.powers) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.powers) (F : FinFn) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratch 240 5 (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn))
      (Proof.AesGcm.sealGatherPrecomputedRoundsContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchL (hpostOut := fun vs m m₁ m₂ r hl _ hb _ => (Proof.AesGcm.sealGatherPrecomputedPostOut_local _) vs m m₁ m₂ r hl hb) (sig := Proof.Gcm.sealGatherPrecomputedSig) (nm := "scratch") (e := .u64)
    (n := 23) (pre := Proof.Gcm.sealGatherPrecomputedPre X86_64.abi.ptrBits)
    (post := Proof.AesGcm.sealGatherRoundsPost X86_64.abi.ptrBits) (wa := true) (stack := 4888) (bytes := 240)
    (sealGatherP_core Sh I A T F) (by decide) (by decide) (by decide) (sealGather_spAll Sh I A T F)
    (sealGather_xdepth Sh I A T F) (Proof.AesGcm.sealGatherPrecomputedPre_local _)
    (Proof.AesGcm.sealGatherPrecomputedPost_local _) gatherFrameSatP_pre

end VG.Proof.AesGcm.X86_64.Gather
