module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCall
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.SplitCall
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Impl.AesGcm.X86_64
meta import VerifiedGarbage.Impl.AesGcm.X86_64.SealGather
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Run
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: constant time of a short copy to `vg_aes_gcm_seal_split`

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments and descriptors test the same number of bytes after
the first slice, whose length is in a descriptor (`splitTest_rel`), and so
take the same path; a short one copies the slices after the first and calls
`vg_aes_gcm_seal_split` with the same public arguments in both
(`copySplit_rel`), from states the correctness proof describes, related as
`CopyCT.lean` relates them (`Eq2`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT)
open VG.Proof.AesGcm.X86_64 (rel_block_split)

/-- `work`, from above the five arguments pushed. -/
theorem ldW88_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 88) 8) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 88))]) s (LdF .r11 .rsp 88 s) := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a; simp [gpr_setReg, a]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

theorem splitT1_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp])
    (.block [.mov32 .r10 (imm 0), .mov .rax (.mem (at_ .r11 gLeft)), .alu .test .rax (.reg .rax)]) hc).isSome =
      true := ⟨_, by simp only [gLeft]; taint_decide⟩

theorem quickT_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp])
    (.block [.mov .rax (.mem (at_ .r11 gLen))]) hc).isSome = true := ⟨_, by simp only [gLen]; taint_decide⟩

theorem splitT2_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r10]) (.block [.mov .r10 (.mem (at_ .r10 8))]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem selT3_check : ∃ hc, (taint.check (Taint.ofRegs [.r11])
    (.block [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4, .mov32 .r8 (imm 0),
      .alu .cmp .r10 (.reg .rax), .cmov .b .r10 (.reg .r8)]) hc).isSome = true :=
  ⟨_, by simp only [gLen, imm]; taint_decide⟩

theorem splitT3_check : ∃ hc, (taint.check (Taint.ofRegs [.r11])
    (.block [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4, .alu .cmp .r10 (.reg .rax),
      .mov .rax (.mem (at_ .r11 gLen)), .mov32 .r10 (imm 0), .cmov .ae .rax (.reg .r10)]) hc).isSome = true :=
  ⟨_, by simp only [gLen, imm]; taint_decide⟩

theorem splitEntry_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block splitEntry) hc).isSome = true :=
  ⟨_, by simp only [splitEntry, gState, gLeft, gDst, gDesc]; taint_decide⟩

theorem splitFirst_check : ∃ hc, (taint.check (Taint.ofRegs [.r10]) (.block splitFirst) hc).isSome = true :=
  ⟨_, by simp only [splitFirst]; taint_decide⟩

theorem splitKeep_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block splitKeep) hc).isSome = true :=
  ⟨_, by simp only [splitKeep, gState]; taint_decide⟩

theorem splitArgs_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block splitArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ldW88_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 88))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

theorem splitCtx_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block splitCtx.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {s₀ s₀' : State} (pb : Pub s₀ s₀')
include pb

theorem Pub.eK0 : k0 s₀' = k0 s₀ := by simp only [k0, pb.cnt]

theorem Pub.eFl : fl s₀' = fl s₀ := by
  unfold fl
  rw [pb.eK0]; exact pb.gl (k0_le s₀)

theorem Pub.eFb : fb s₀' = fb s₀ := by
  by_cases hc : Cnt s₀ = 0
  · simp only [fb, pb.cnt, hc, ↓reduceIte, pb.src]
  · simp only [fb, pb.cnt, hc, ↓reduceIte]; exact pb.sb (by omega)

end

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- The lengths, then `last`, from two states. -/
theorem lenTest_eq2 {last : List Instr}
    (h₃ : ∀ υ₁ υ₂, G2 s₀ υ₁ → G2 s₀' υ₂ → RelCT isa (Eq2 υ₁ υ₂) (.block last) TT) {σ₁ σ₂ : State}
    (E₁ : E2 s₀ σ₁) (E₂ : E2 s₀' σ₂) : RelCT isa (Eq2 σ₁ σ₂) (lenTest last) TT := by
  have ec : Cnt s₀' = Cnt s₀ := pb.cnt
  unfold lenTest
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq ?_ (w_splitT1 hp E₁) (w_splitT1 hp' E₂) fun τ₁ τ₂ G₁ G₂ => ?_
  · refine (rel_wt [.rsp] (by simp) (fun _ _ h r hr => ?_) (fun _ _ h => ?_) splitT1_check).mono
      (fun _ _ h => h) fun _ _ _ => trivial
    · obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_singleton] at hr; subst hr
      rw [E₁.1.rsp, E₂.1.rsp]; exact pb.rsp.symm
    · obtain ⟨rfl, rfl⟩ := h
      exact base_hW hp hp' pb E₁.1 E₂.1
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_ite (b := decide (Cnt s₀ = 0)) G₁.2.2.2 (by simp only [eval, G₂.2.2.2, ec]) (fun _ => ChaCha20Poly1305.X86_64.Gather.rel_skip)
    fun hf => ?_) (w_splitIte hp G₁) (w_splitIte hp' G₂) fun υ₁ υ₂ H₁ H₂ => ?_
  · have hc : Cnt s₀ ≠ 0 := by simpa using hf
    have w₁ : τ₁.gpr .r11 = W s₀ := G₁.2.1
    have w₂ : τ₂.gpr .r11 = W s₀ := by rw [G₂.2.1, pb.w]
    have i₁ : InRegions (τ₁.rd ++ τ₁.wr) (τ₁.gpr .r11 + BitVec.ofNat 64 56) 8 := by
      rw [w₁]; exact G₁.1.1.slot hp (by decide)
    have i₂ : InRegions (τ₂.rd ++ τ₂.wr) (τ₂.gpr .r11 + BitVec.ofNat 64 56) 8 := by
      rw [G₂.2.1]; exact G₂.1.1.slot hp' (by decide)
    have d₁ : τ₁.mem.readW (τ₁.gpr .r11 + BitVec.ofNat 64 56) 64 = Src s₀ + BitVec.ofNat 64 (16 * 0) := by
      rw [w₁]; exact G₁.1.1.kept.desc
    have d₂ : τ₂.mem.readW (τ₂.gpr .r11 + BitVec.ofNat 64 56) 64 = Src s₀ + BitVec.ofNat 64 (16 * 0) := by
      rw [G₂.2.1, G₂.1.1.kept.desc, pb.src]
    refine rel_block_split (l₁ := [.mov .r10 (.mem (at_ .r11 gDesc))]) (l₂ := [.mov .r10 (.mem (at_ .r10 8))])
      (ChaCha20Poly1305.X86_64.Gather.rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r11] (by simp [w₁, w₂]) ldD_check) (ldD_ok i₁) (ldD_ok i₂) fun ω₁ ω₂ L₁ L₂ => ?_)
    exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.r10] (by simp [L₁.1, L₂.1, d₁, d₂]) splitT2_check
  · exact h₃ υ₁ υ₂ H₁ H₂

/-- The test of the text's length alone, from two states. -/
theorem quick_eq2 (q : Nat) {σ₁ σ₂ : State} (E₁ : E2 s₀ σ₁) (E₂ : E2 s₀' σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (.block (quickTest q)) TT := by
  refine rel_block_split (l₁ := [.mov .r11 (.mem (at_ .rsp 48)), .mov .rax (.mem (at_ .r11 gLen))])
    (l₂ := [.alu .cmp .rax (imm q)]) (RelCT.seq (R := fun _ _ => True) ?_ (rel_cmpImm .rax q))
  refine (rel_wt [.rsp] (by simp) (fun _ _ h r hr => ?_) (fun _ _ h => ?_) quickT_check).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · obtain ⟨rfl, rfl⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    rw [E₁.1.rsp, E₂.1.rsp]; exact pb.rsp.symm
  · obtain ⟨rfl, rfl⟩ := h
    exact base_hW hp hp' pb E₁.1 E₂.1

/-- The test of the text's length alone, in two runs. -/
theorem quick_rel {q : Nat} (hq : q < 2 ^ 31) :
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) (.block (quickTest q)) fun s₁ s₂ =>
      (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (decide (L s₀ < q))) ∧
      (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (decide (L s₀' < q))) :=
  pstep (rel_of_eq2 fun _ _ h => quick_eq2 hp hp' pb q h.1 h.2)
    (fun _ h => w_quick hp hq h) (fun _ h => w_quick hp' hq h)

/-- The length alone if the text is shorter than `q`, otherwise the lengths
then `last`, from two states. -/
theorem lenTestQ_eq2 {q : Nat} (hq : q < 2 ^ 31) {last : List Instr}
    (h₃ : ∀ υ₁ υ₂, G2 s₀ υ₁ → G2 s₀' υ₂ → RelCT isa (Eq2 υ₁ υ₂) (.block last) TT) {σ₁ σ₂ : State}
    (E₁ : E2 s₀ σ₁) (E₂ : E2 s₀' σ₂) : RelCT isa (Eq2 σ₁ σ₂) (lenTestQ q last) TT := by
  unfold lenTestQ
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq (quick_eq2 hp hp' pb q E₁ E₂) (w_quick hp hq E₁) (w_quick hp' hq E₂)
    fun τ₁ τ₂ G₁ G₂ => ?_
  exact ChaCha20Poly1305.X86_64.Gather.rel_ite (b := decide (L s₀ < q)) G₁.2.2 (by simp only [eval, G₂.2.2, pb.eL])
    (fun _ => ChaCha20Poly1305.X86_64.Gather.rel_skip) fun _ => lenTest_eq2 hp hp' pb h₃ G₁.1 G₂.1

omit hp hp' in
/-- The last block of the test of the texts the short path takes, from two states. -/
theorem splitLast_eq2 {t : Nat} {υ₁ υ₂ : State} (H₁ : G2 s₀ υ₁) (H₂ : G2 s₀' υ₂) :
    RelCT isa (Eq2 υ₁ υ₂) (.block (splitLast t)) TT := by
  have w₁ : υ₁.gpr .r11 = W s₀ := H₁.2.1
  have w₂ : υ₂.gpr .r11 = W s₀ := by rw [H₂.2.1, pb.w]
  refine rel_block_split (l₁ := [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4,
      .alu .cmp .r10 (.reg .rax), .mov .rax (.mem (at_ .r11 gLen)), .mov32 .r10 (imm 0), .cmov .ae .rax (.reg .r10)])
    (l₂ := [.alu .cmp .rax (imm t)]) (RelCT.seq (R := fun _ _ => True) ?_ (rel_cmpImm .rax t))
  exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.r11] (by simp [w₁, w₂]) splitT3_check

omit hp hp' in
/-- The last block of the choice between copying the text whole and sealing
it from its first slice, from two states. -/
theorem selLast_eq2 {ts : Nat} {υ₁ υ₂ : State} (H₁ : G2 s₀ υ₁) (H₂ : G2 s₀' υ₂) :
    RelCT isa (Eq2 υ₁ υ₂) (.block (selLast ts)) TT := by
  have w₁ : υ₁.gpr .r11 = W s₀ := H₁.2.1
  have w₂ : υ₂.gpr .r11 = W s₀ := by rw [H₂.2.1, pb.w]
  refine rel_block_split (l₁ := [.mov .rax (.mem (at_ .r11 gLen)), .shift .shr .rax 4, .shift .shl .rax 4,
      .mov32 .r8 (imm 0), .alu .cmp .r10 (.reg .rax), .cmov .b .r10 (.reg .r8)])
    (l₂ := [.alu .cmp .r10 (imm ts)]) (RelCT.seq (R := fun _ _ => True) ?_ (rel_cmpImm .r10 ts))
  exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.r11] (by simp [w₁, w₂]) selT3_check

/-- The test of the texts the short path takes, in two runs. -/
theorem splitTest_rel {t : Nat} (ht : t < 2 ^ 31) :
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) (splitTest t) fun s₁ s₂ =>
      (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (decide (shortLen s₀ < t))) ∧
      (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (decide (shortLen s₀' < t))) :=
  pstep (rel_of_eq2 fun _ _ h => lenTestQ_eq2 hp hp' pb ht (fun _ _ H₁ H₂ => splitLast_eq2 pb H₁ H₂) h.1 h.2)
    (fun _ h => splitTest_wp hp ht h) (fun _ h => splitTest_wp hp' ht h)

/-- The choice between copying the text whole and sealing it from its first
slice, in two runs. -/
theorem selTest_rel {ts : Nat} (hts : ts < 2 ^ 31) :
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) (selTest ts) fun s₁ s₂ =>
      (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (decide (selLen s₀ < ts))) ∧
      (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (decide (selLen s₀' < ts))) :=
  pstep (rel_of_eq2 fun _ _ h => lenTest_eq2 hp hp' pb (fun _ _ H₁ H₂ => selLast_eq2 pb H₁ H₂) h.1 h.2)
    (fun _ h => selTest_wp hp hts h) (fun _ h => selTest_wp hp' hts h)

/-- `ctx` and `rounds`, in two runs. -/
theorem splitCtx_rel {σ₁ σ₂ p₁ p₂ : State} (h₁ : SCBase s₀ σ₁) (h₂ : SCBase s₀' σ₂)
    (hP₁ : p₁.gpr .rsp = SP s₀ - BitVec.ofNat 64 40) (hrd₁ : p₁.rd = σ₁.rd)
    (hwr₁ : p₁.wr = ⟨SP s₀ - BitVec.ofNat 64 40, 40⟩ :: σ₁.wr)
    (hf₁ : Frame [⟨SP s₀ - BitVec.ofNat 64 40, 40⟩] σ₁.mem p₁.mem)
    (hP₂ : p₂.gpr .rsp = SP s₀' - BitVec.ofNat 64 40) (hrd₂ : p₂.rd = σ₂.rd)
    (hwr₂ : p₂.wr = ⟨SP s₀' - BitVec.ofNat 64 40, 40⟩ :: σ₂.wr)
    (hf₂ : Frame [⟨SP s₀' - BitVec.ofNat 64 40, 40⟩] σ₂.mem p₂.mem) :
    RelCT isa (Eq2 p₁ p₂) (.block splitCtx) TT := by
  obtain ⟨a₁, e₁⟩ := pushedW hp h₁ hP₁ hrd₁ hwr₁ hf₁
  obtain ⟨a₂, e₂⟩ := pushedW hp' h₂ hP₂ hrd₂ hwr₂ hf₂
  refine rel_block_split (l₁ := [.mov .r11 (.mem (at_ .rsp 88))]) (l₂ := splitCtx.tail)
    (ChaCha20Poly1305.X86_64.Gather.rel_seq (ChaCha20Poly1305.X86_64.Gather.rel_regs [.rsp] (by simp [hP₁, hP₂, SP, pb.rsp]) ldW88_check) (ldW88_ok a₁) (ldW88_ok a₂)
      fun ω₁ ω₂ L₁ L₂ => ?_)
  exact ChaCha20Poly1305.X86_64.Gather.rel_regs [.r11] (by simp [L₁.1, L₂.1, e₁, e₂, pb.w]) splitCtx_check

/-- The call itself, in two runs. -/
theorem splitCallX_rel (S : SplitFn M) {σ₁ σ₂ : State} (h₁ : SCBase s₀ σ₁) (g₁ : SplitRegs s₀ σ₁)
    (h₂ : SCBase s₀' σ₂) (g₂ : SplitRegs s₀' σ₂) {q₁ q₂ : State} (Q₁ : SplitQ s₀ σ₁ q₁) (Q₂ : SplitQ s₀' σ₂ q₂) :
    RelCT isa (Eq2 q₁ q₂) (.call S.fn.name S.fn.code) TT := by
  have hP₁ : (pushed [.rax, .r10, .r11, .rdi, .rsi] σ₁).gpr .rsp = SP s₀ - BitVec.ofNat 64 40 := by
    rw [pushed_rsp, h₁.rsp]; rfl
  have hP₂ : (pushed [.rax, .r10, .r11, .rdi, .rsi] σ₂).gpr .rsp = SP s₀' - BitVec.ofNat 64 40 := by
    rw [pushed_rsp, h₂.rsp]; rfl
  refine RelCT.callEx (k := splitK M) S.ok S.ct fun _ _ hab => ?_
  rw [hab.1, hab.2]
  obtain ⟨p₁, c₁, w₁, a₀₁, a₁₁, a₂₁, a₃₁, a₄₁⟩ := splitCallEntry hp h₁ g₁ Q₁
  obtain ⟨p₂, c₂, w₂, a₀₂, a₁₂, a₂₂, a₃₂, a₄₂⟩ := splitCallEntry hp' h₂ g₂ Q₂
  have q₁sp : q₁.gpr .rsp = SP s₀ - BitVec.ofNat 64 40 := by rw [Q₁.g _ (by decide) (by decide) (by decide), hP₁]
  have q₂sp : q₂.gpr .rsp = SP s₀ - BitVec.ofNat 64 40 := by
    rw [Q₂.g _ (by decide) (by decide) (by decide), hP₂, show SP s₀' = SP s₀ from pb.rsp]
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [q₁sp, q₂sp]⟩
  have u : ∀ {q : State} {r : Reg} (rd wr : List Region), r ≠ .rsp → (q.callEntry.withRegions rd wr).gpr r = q.gpr r :=
    fun _ _ h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h]
  have x₁ : ∀ r, r ≠ .rsp → r ≠ .rdi → r ≠ .rsi → r ≠ .r11 →
      (q₁.callEntry.withRegions (splitRd s₀ M) (sealWr s₀)).gpr r = σ₁.gpr r :=
    fun r a b c d => by rw [u _ _ a, Q₁.g r b c d, pushed_gpr _ _ a]
  have x₂ : ∀ r, r ≠ .rsp → r ≠ .rdi → r ≠ .rsi → r ≠ .r11 →
      (q₂.callEntry.withRegions (splitRd s₀' M) (sealWr s₀')).gpr r = σ₂.gpr r :=
    fun r a b c d => by rw [u _ _ a, Q₂.g r b c d, pushed_gpr _ _ a]
  simp only [splitK, splitPubK, Proof.AesGcm.arg, a₀₁, a₁₁, a₂₁, a₃₁, a₄₁, a₀₂, a₁₂, a₂₂, a₃₂, a₄₂,
    u _ _ (by decide : Reg.rdi ≠ .rsp), u _ _ (by decide : Reg.rsi ≠ .rsp), Q₁.di, Q₂.di, Q₁.si, Q₂.si,
    x₁ .rdx (by decide) (by decide) (by decide) (by decide), x₂ .rdx (by decide) (by decide) (by decide) (by decide),
    x₁ .rcx (by decide) (by decide) (by decide) (by decide), x₂ .rcx (by decide) (by decide) (by decide) (by decide),
    x₁ .r8 (by decide) (by decide) (by decide) (by decide), x₂ .r8 (by decide) (by decide) (by decide) (by decide),
    x₁ .r9 (by decide) (by decide) (by decide) (by decide), x₂ .r9 (by decide) (by decide) (by decide) (by decide),
    g₁.rdx, g₂.rdx, g₁.rcx, g₂.rcx, g₁.r8, g₂.r8, g₁.r9, g₂.r9, State.withRegions_gpr, State.callEntry_rsp, q₁sp,
    q₂sp, K, Nn, Ad, AL, pb.rdi, pb.rsi, pb.rdx, pb.rcx, pb.r8, pb.r9, pb.eFb, pb.eFl, pb.dst, pb.len, pb.tg, and_self]

/-- The call of `vg_aes_gcm_seal_split`, in two runs. -/
theorem splitCall_rel (S : SplitFn M) {σ₁ σ₂ : State} (h₁ : SCBase s₀ σ₁) (g₁ : SplitRegs s₀ σ₁)
    (h₂ : SCBase s₀' σ₂) (g₂ : SplitRegs s₀' σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.push [.rax, .r10, .r11, .rdi, .rsi])
      (.seq (.block splitCtx) (.call S.fn.name S.fn.code)) (.pop .rax 5)) TT := by
  have wsp := hp.w_sp
  have wsp' := hp'.w_sp
  have hn₁ : 8 * [Reg.rax, .r10, .r11, .rdi, .rsi].length ≤ (σ₁.gpr .rsp).toNat := by rw [h₁.rsp]; simp; omega
  have hn₂ : 8 * [Reg.rax, .r10, .r11, .rdi, .rsi].length ≤ (σ₂.gpr .rsp).toNat := by rw [h₂.rsp]; simp; omega
  obtain ⟨hpf₁, -⟩ := pushRegs_mem σ₁ [.rax, .r10, .r11, .rdi, .rsi] (by decide) hn₁
  obtain ⟨hpf₂, -⟩ := pushRegs_mem σ₂ [.rax, .r10, .r11, .rdi, .rsi] (by decide) hn₂
  have hP₁ : (pushed [.rax, .r10, .r11, .rdi, .rsi] σ₁).gpr .rsp = SP s₀ - BitVec.ofNat 64 40 := by
    rw [pushed_rsp, h₁.rsp]; rfl
  have hP₂ : (pushed [.rax, .r10, .r11, .rdi, .rsi] σ₂).gpr .rsp = SP s₀' - BitVec.ofNat 64 40 := by
    rw [pushed_rsp, h₂.rsp]; rfl
  have hf₁ : Frame [⟨SP s₀ - BitVec.ofNat 64 40, 40⟩] σ₁.mem (pushed [.rax, .r10, .r11, .rdi, .rsi] σ₁).mem := by
    rw [h₁.rsp] at hpf₁; exact hpf₁
  have hf₂ : Frame [⟨SP s₀' - BitVec.ofNat 64 40, 40⟩] σ₂.mem (pushed [.rax, .r10, .r11, .rdi, .rsi] σ₂).mem := by
    rw [h₂.rsp] at hpf₂; exact hpf₂
  have hw₁ : (pushed [.rax, .r10, .r11, .rdi, .rsi] σ₁).wr = ⟨SP s₀ - BitVec.ofNat 64 40, 40⟩ :: σ₁.wr := by
    rw [pushed_wr, h₁.rsp]; rfl
  have hw₂ : (pushed [.rax, .r10, .r11, .rdi, .rsi] σ₂).wr = ⟨SP s₀' - BitVec.ofNat 64 40, 40⟩ :: σ₂.wr := by
    rw [pushed_wr, h₂.rsp]; rfl
  refine RelCT.frame (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; rw [h₁.rsp, h₂.rsp]; exact pb.rsp.symm)
    ((ChaCha20Poly1305.X86_64.Gather.rel_seq
      (splitCtx_rel hp hp' pb h₁ h₂ hP₁ (pushed_rd _ _) hw₁ hf₁ hP₂ (pushed_rd _ _) hw₂ hf₂)
      (splitCtx_ok hp h₁ hP₁ (pushed_rd _ _) hw₁ hf₁) (splitCtx_ok hp' h₂ hP₂ (pushed_rd _ _) hw₂ hf₂)
      fun q₁ q₂ ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ =>
        splitCallX_rel hp hp' pb S h₁ g₁ h₂ g₂ ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩).mono (fun _ _ h => by
        obtain ⟨_, _, ⟨rfl, rfl⟩, rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩) fun _ _ h => h)

/-- The arguments of `vg_aes_gcm_seal_split`, in two runs. -/
theorem splitArgs_rel {σ₁ σ₂ : State} (h₁ : SPBase s₀ σ₁) (h₂ : SPBase s₀' σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (.block splitArgs) TT := by
  rw [show splitArgs = .mov .r11 (.mem (at_ .rsp 48)) :: splitArgs.tail from rfl]
  refine (rel_wt [.rsp] (by simp) (fun _ _ h r hr => ?_) (fun _ _ h => ?_) splitArgs_check).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · obtain ⟨rfl, rfl⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.rsp, h₂.rsp]; exact pb.rsp.symm
  · obtain ⟨rfl, rfl⟩ := h
    exact base_hW hp hp' pb h₁.toBase h₂.toBase

/-- The path of a text whose slices after the first are short, in two runs. -/
theorem copySplit_rel (S : SplitFn M) (hL : L s₀ - fl s₀ < 2 ^ 63) {σ₁ σ₂ : State}
    (h₁ : Base s₀ (AL s₀) 0 σ₁) (r11₁ : σ₁.gpr .r11 = W s₀) (si₁ : σ₁.gpr .rsi = Nn s₀)
    (dx₁ : σ₁.gpr .rdx = s₀.gpr .rcx) (h₂ : Base s₀' (AL s₀') 0 σ₂) (r11₂ : σ₂.gpr .r11 = W s₀')
    (si₂ : σ₂.gpr .rsi = Nn s₀') (dx₂ : σ₂.gpr .rdx = s₀'.gpr .rcx) :
    RelCT isa (Eq2 σ₁ σ₂) (copySplit S.fn) TT := by
  have hL' : L s₀' - fl s₀' < 2 ^ 63 := by rw [pb.eL, pb.eFl]; exact hL
  unfold copySplit
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq ?_ (splitHead_wp hp h₁ r11₁ si₁ dx₁)
    (splitHead_wp hp' h₂ r11₂ si₂ dx₂) fun τ₁ τ₂ ⟨F₁, C₁⟩ ⟨F₂, C₂⟩ => ?_
  · refine ChaCha20Poly1305.X86_64.Gather.rel_seq
      (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r11] (by simp [r11₁, r11₂, pb.w]) splitEntry_check)
      (splitEntry_ok hp h₁ r11₁ si₁ dx₁) (splitEntry_ok hp' h₂ r11₂ si₂ dx₂)
      fun υ₁ υ₂ ⟨_, _, r10₁, _, _, zf₁, _, _, _⟩ ⟨_, _, r10₂, _, _, zf₂, _, _, _⟩ => ?_
    exact ChaCha20Poly1305.X86_64.Gather.rel_ite (b := decide (Cnt s₀ = 0)) (by simp only [eval, zf₁])
      (by simp only [eval, zf₂, pb.cnt]) (fun _ => ChaCha20Poly1305.X86_64.Gather.rel_skip)
      fun _ => ChaCha20Poly1305.X86_64.Gather.rel_regs [.r10] (by simp [r10₁, r10₂, pb.src]) splitFirst_check
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq
    (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r11] (by simp [F₁.2.2.2.2.2, F₂.2.2.2.2.2, pb.w]) splitKeep_check)
    (splitKeep_ok hp F₁ C₁) (splitKeep_ok hp' F₂ C₂)
    fun υ₁ υ₂ ⟨P₁, r9₁, di₁, r11₁', _⟩ ⟨P₂, r9₂, di₂, r11₂', _⟩ => ?_
  have G₁ := splitGatherPre hp hL P₁.toBase r9₁ di₁ r11₁'
  have G₂o := splitGatherPre hp' hL' P₂.toBase r9₂ di₂ r11₂'
  have G₂ := G₂o
  rw [pb.eFl, pb.eK0, pb.src, pb.dst, pb.cnt, pb.eL] at G₂
  have hd : ∀ j < (Cnt s₀ - k0 s₀) * 16, υ₁.mem (Src s₀ + BitVec.ofNat 64 (16 * k0 s₀) + BitVec.ofNat 64 j) =
      υ₂.mem (Src s₀ + BitVec.ofNat 64 (16 * k0 s₀) + BitVec.ofNat 64 j) := by
    intro j hj
    have hk := k0_le s₀
    have hw := hp.w_ds
    have hj' : 16 * k0 s₀ + j < Cnt s₀ * 16 := by rw [Nat.sub_mul] at hj; omega
    rw [BitVec.add_assoc, ofNat_add_ofNat]
    have hc : (Sig.descRegion 64 (Src s₀) (Cnt s₀)).Contains (Src s₀ + BitVec.ofNat 64 (16 * k0 s₀ + j)) 1 :=
      Offset.contains_base _ (show 16 * k0 s₀ + j + 1 ≤ Cnt s₀ * (2 * (64 / 8)) by simp; omega) (by omega)
    have hc' : (Sig.descRegion 64 (Src s₀') (Cnt s₀')).Contains (Src s₀ + BitVec.ofNat 64 (16 * k0 s₀ + j)) 1 := by
      rw [pb.src, pb.cnt]; exact hc
    rw [desc_byte hp P₁.frame _ hc, desc_byte hp' P₂.frame _ hc', pb.desc _ hj']
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq (gatherCopy_rel hd G₁ G₂) (gatherCopy_wp υ₁ G₁)
    (gatherCopy_wp υ₂ G₂o) fun ω₁ ω₂ ⟨m₁, k₁⟩ ⟨m₂, k₂⟩ => ?_
  have B₁ := split_after hp P₁ m₁ k₁
  have B₂ := split_after hp' P₂ m₂ k₂
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq (splitArgs_rel hp hp' pb B₁ B₂) (splitArgs_ok hp B₁)
    (splitArgs_ok hp' B₂) fun ξ₁ ξ₂ a₁ a₂ => ?_
  obtain ⟨dx₁', cx₁, r8₁, r9₁', ax₁, r10₁, di₁', si₁', r11₁'', cs₁, m₁', rd₁, wr₁⟩ := a₁
  obtain ⟨dx₂', cx₂, r8₂, r9₂', ax₂, r10₂, di₂', si₂', r11₂'', cs₂, m₂', rd₂, wr₂⟩ := a₂
  exact splitCall_rel hp hp' pb S (B₁.regs m₁' cs₁ rd₁ wr₁).toSC ⟨dx₁', cx₁, r8₁, r9₁', ax₁, r10₁, di₁', si₁', r11₁''⟩
    (B₂.regs m₂' cs₂ rd₂ wr₂).toSC ⟨dx₂', cx₂, r8₂, r9₂', ax₂, r10₂, di₂', si₂', r11₂''⟩

end

/-- The short path of `copySplit S`, for the texts `splitTest t` passes, in two runs. -/
theorem splitShort_rel {M : CtxMode} (S : SplitFn M) {t : Nat} {s₀ s₀' : State} (hp : SG M s₀)
    (hp' : SG M s₀') (pb : Pub s₀ s₀') (e : decide (shortLen s₀ < t) = true) (ht : t < 2 ^ 31)
    {σ₁ σ₂ : State} (E₁ : E2 s₀ σ₁) (r₁ : σ₁.gpr .r11 = W s₀) (E₂ : E2 s₀' σ₂) (r₂ : σ₂.gpr .r11 = W s₀') :
    RelCT isa (Eq2 σ₁ σ₂) (copySplit S.fn) TT := by
  exact copySplit_rel hp hp' pb S (sub_lt_of_shortLen hp ht (by simpa using e)) E₁.1 r₁ E₁.2.2.1 E₁.2.2.2.1 E₂.1 r₂ E₂.2.2.1 E₂.2.2.2.1

end VG.Proof.AesGcm.X86_64.Gather
