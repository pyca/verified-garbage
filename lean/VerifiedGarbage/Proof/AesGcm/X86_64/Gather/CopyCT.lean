import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Fn

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: constant time of the whole function

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments and descriptors test the same length against the
same threshold (`shortTest_rel`; the comparison with an immediate accesses
no memory, `rel_cmpImm`), and so take the same path: a short text is copied
and sealed in both (`copySeal_rel`), from states the correctness proof
describes, related as ChaCha20-Poly1305's gathering relates them
(`Proof/ChaCha20Poly1305/X86_64/Gather/LoopCT.lean`, `Eq2`); a longer one
streams in both (`stream_rel`, from `CT.lean`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.ChaCha20Poly1305.X86_64.Gather (Eq2 TT)
open VG.Proof.AesGcm.X86_64 (rel_block_split)

/-- A comparison of a register with an immediate accesses no memory. -/
theorem rel_cmpImm {P : State → State → Prop} (d : Reg) (k : Nat) :
    RelCT isa P (.block [.alu .cmp d (imm k)]) fun _ _ => True := by
  have h0 : ∀ s s' t, execBlock isa [.alu .cmp d (imm k)] s = some (s', t) → t = [] := by
    intro s s' t h
    simp only [execBlock] at h
    split at h
    · cases h
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; rfl
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ => exact ⟨by rw [h0 _ _ _ h₁, h0 _ _ _ h₂], trivial⟩

/-- Related runs, from relating each pair of states. -/
theorem rel_of_eq2 {P : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : RelCT isa P c fun _ _ => True :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

theorem shortTest_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp])
    (.block [.mov .rax (.mem (at_ .r11 gLen))]) hc).isSome = true := ⟨_, by simp only [gLen]; taint_decide⟩

theorem copyEntry_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block copyEntry) hc).isSome = true :=
  ⟨_, by simp only [copyEntry, gState, gLeft, gDst, gDesc]; taint_decide⟩

theorem sealArgs_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block sealArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- The test of the length, in two runs. -/
theorem shortTest_rel {t : Nat} (ht : t < 2 ^ 31) :
    RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) (.block (shortTest t)) fun s₁ s₂ =>
      E3 s₀ t s₁ ∧ E3 s₀' t s₂ := by
  refine pstep ?_ (fun _ => w_shortTest hp ht) (fun _ => w_shortTest hp' ht)
  rw [show shortTest t = [.mov .r11 (.mem (at_ .rsp 48)), .mov .rax (.mem (at_ .r11 gLen))] ++
    [.alu .cmp .rax (imm t)] from rfl]
  refine rel_block_split (RelCT.seq (R := fun _ _ => True) ?_ (rel_cmpImm .rax t))
  exact rel_base hp hp' pb (fun _ _ h => ⟨_, _, _, _, h.1.1, h.2.1⟩) shortTest_check

/-- The arguments of `vg_aes_gcm_seal`, in two runs. -/
theorem sealArgs_rel {σ₁ σ₂ : State} (h₁ : SBase s₀ σ₁) (h₂ : SBase s₀' σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (.block sealArgs) TT := by
  rw [show sealArgs = .mov .r11 (.mem (at_ .rsp 48)) :: sealArgs.tail from rfl]
  refine (rel_wt [.rsp] (by simp) (fun _ _ h r hr => ?_) (fun _ _ h => ?_) sealArgs_check).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  · obtain ⟨rfl, rfl⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.rsp, h₂.rsp]; exact pb.rsp.symm
  · obtain ⟨rfl, rfl⟩ := h
    exact base_hW hp hp' pb h₁.toBase h₂.toBase

/-- The call of `vg_aes_gcm_seal`, in two runs. -/
theorem sealCall_rel (S : SealFn M) {σ₁ σ₂ : State} (h₁ : SBase s₀ σ₁) (g₁ : SealRegs s₀ σ₁)
    (h₂ : SBase s₀' σ₂) (g₂ : SealRegs s₀' σ₂) :
    RelCT isa (Eq2 σ₁ σ₂) (.frame (.push [.rax, .r10, .r11]) (.call S.fn.name S.fn.code) (.pop .rax 3)) TT := by
  refine RelCT.frame (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; rw [h₁.rsp, h₂.rsp]; exact pb.rsp.symm)
    (RelCT.callEx (k := sealK M) S.ok S.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, h, ha, hb⟩ := hab
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨p₁, c₁, w₁, a₀₁, a₁₁, a₂₁⟩ := sealEntry hp h₁ g₁
  obtain ⟨p₂, c₂, w₂, a₀₂, a₁₂, a₂₂⟩ := sealEntry hp' h₂ g₂
  subst ha hb
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by
    rw [pushed_rsp, pushed_rsp, h₁.rsp, h₂.rsp, show SP s₀' = SP s₀ from pb.rsp]⟩
  have g : ∀ {t : State} {r : Reg} (rd wr : List Region), r ≠ .rsp →
      ((pushed [.rax, .r10, .r11] t).callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun _ _ h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h, pushed_gpr _ _ h]
  simp only [sealK, sealPubK, Proof.AesGcm.arg, a₀₁, a₁₁, a₂₁, a₀₂, a₁₂, a₂₂, g _ _ (by decide : Reg.rdi ≠ .rsp),
    g _ _ (by decide : Reg.rsi ≠ .rsp), g _ _ (by decide : Reg.rdx ≠ .rsp), g _ _ (by decide : Reg.rcx ≠ .rsp),
    g _ _ (by decide : Reg.r8 ≠ .rsp), g _ _ (by decide : Reg.r9 ≠ .rsp), g₁.rdi, g₂.rdi, g₁.rsi, g₂.rsi,
    g₁.rdx, g₂.rdx, g₁.rcx, g₂.rcx, g₁.r8, g₂.r8, g₁.r9, g₂.r9, State.withRegions_gpr, State.callEntry_rsp,
    pushed_rsp, h₁.rsp, h₂.rsp, K, Nn, Ad, AL, pb.rdi, pb.rsi, pb.rdx, pb.rcx, pb.r8, pb.r9, pb.rsp, SP, pb.dst,
    pb.len, pb.tg, and_self]

/-- The path of a short text, in two runs. -/
theorem copySeal_rel (S : SealFn M) (hL : L s₀ < 2 ^ 63) {σ₁ σ₂ : State}
    (h₁ : Base s₀ (AL s₀) 0 σ₁) (r11₁ : σ₁.gpr .r11 = W s₀) (si₁ : σ₁.gpr .rsi = Nn s₀)
    (dx₁ : σ₁.gpr .rdx = s₀.gpr .rcx) (h₂ : Base s₀' (AL s₀') 0 σ₂) (r11₂ : σ₂.gpr .r11 = W s₀')
    (si₂ : σ₂.gpr .rsi = Nn s₀') (dx₂ : σ₂.gpr .rdx = s₀'.gpr .rcx) :
    RelCT isa (Eq2 σ₁ σ₂) (copySeal S.fn) TT := by
  have hL' : L s₀' < 2 ^ 63 := by rw [pb.eL]; exact hL
  unfold copySeal
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq
    (ChaCha20Poly1305.X86_64.Gather.rel_regs [.r11] (by simp [r11₁, r11₂, pb.w]) copyEntry_check)
    (copyEntry_ok hp h₁ r11₁ si₁ dx₁) (copyEntry_ok hp' h₂ r11₂ si₂ dx₂)
    fun τ₁ τ₂ ⟨r9₁, rdi₁, r11₁', _, C₁⟩ ⟨r9₂, rdi₂, r11₂', _, C₂⟩ => ?_
  have G₁ := copyGatherPre hp hL C₁.toBase r9₁ rdi₁ r11₁'
  have G₂o := copyGatherPre hp' hL' C₂.toBase r9₂ rdi₂ r11₂'
  have G₂ := G₂o
  rw [pb.src, pb.dst, pb.cnt, pb.eL] at G₂
  have hd : ∀ j < Cnt s₀ * 16, τ₁.mem (Src s₀ + BitVec.ofNat 64 j) = τ₂.mem (Src s₀ + BitVec.ofNat 64 j) := by
    intro j hj
    have hw := hp.w_ds
    have hc : (Sig.descRegion 64 (Src s₀) (Cnt s₀)).Contains (Src s₀ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ (show j + 1 ≤ Cnt s₀ * (2 * (64 / 8)) by simp; omega) (by omega)
    have hc' : (Sig.descRegion 64 (Src s₀') (Cnt s₀')).Contains (Src s₀ + BitVec.ofNat 64 j) 1 := by
      rw [pb.src, pb.cnt]; exact hc
    rw [desc_byte hp C₁.frame _ hc, desc_byte hp' C₂.frame _ hc', pb.desc j hj]
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq (gatherCopy_rel hd G₁ G₂) (gatherCopy_wp τ₁ G₁)
    (gatherCopy_wp τ₂ G₂o) fun υ₁ υ₂ ⟨m₁, k₁⟩ ⟨m₂, k₂⟩ => ?_
  have B₁ := gathered_after hp C₁ m₁ k₁
  have B₂ := gathered_after hp' C₂ m₂ k₂
  refine ChaCha20Poly1305.X86_64.Gather.rel_seq (sealArgs_rel hp hp' pb B₁ B₂) (sealArgs_ok hp B₁)
    (sealArgs_ok hp' B₂) fun ω₁ ω₂ a₁ a₂ => ?_
  obtain ⟨di₁, si₁', dx₁', cx₁, r8₁, r9₁', ax₁, r10₁, r11₁'', cs₁, m₁', rd₁, wr₁⟩ := a₁
  obtain ⟨di₂, si₂', dx₂', cx₂, r8₂, r9₂', ax₂, r10₂, r11₂'', cs₂, m₂', rd₂, wr₂⟩ := a₂
  exact sealCall_rel hp hp' pb S (B₁.regs m₁' cs₁ rd₁ wr₁) ⟨di₁, si₁', dx₁', cx₁, r8₁, r9₁', ax₁, r10₁, r11₁''⟩
    (B₂.regs m₂' cs₂ rd₂ wr₂) ⟨di₂, si₂', dx₂', cx₂, r8₂, r9₂', ax₂, r10₂, r11₂''⟩

end

/-- `vg_aes_gcm_seal_gather` is constant time. -/
theorem sealGather_ct {M : CtxMode} (S : SealFn M) {t : Nat} (ht : t < 2 ^ 31) (I : InitFn) (A : AadFn)
    (T : ToFn M) (F : FinFn) :
    ConstantTime isa (Proof.AesGcm.sealGatherX86_64M M).pre Proof.AesGcm.sealGatherPub
      (sealGather S.fn t I.fn A.fn T.fn F.fn) := by
  refine ct_of_rel (k := Proof.AesGcm.sealGatherX86_64M M) fun s₀ s₀' h h' hq => ?_
  have hp := SG.ofM h
  have hp' := SG.ofM h'
  have pb := Pub.of hq
  unfold sealGather
  refine RelCT.seq (entry1_rel hp hp' pb) (RelCT.seq (entry2_rel hp hp' pb) (RelCT.seq (shortTest_rel hp hp' pb ht)
    (RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, pb.eL]) ?_
      ((stream_rel hp hp' pb I A T F).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h))))
  refine rel_of_eq2 fun σ₁ σ₂ ⟨⟨⟨E₁, r₁, c₁⟩, ⟨E₂, r₂, c₂⟩⟩, ev⟩ => ?_
  have hL : L s₀ < t := by simp only [eval, c₁] at ev; simpa using ev
  exact copySeal_rel hp hp' pb S (by omega) E₁.1 r₁ E₁.2.2.1 E₁.2.2.2.1 E₂.1 r₂ E₂.2.2.1 E₂.2.2.2.1

end VG.Proof.AesGcm.X86_64.Gather
