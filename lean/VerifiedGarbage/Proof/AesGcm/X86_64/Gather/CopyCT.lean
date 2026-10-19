module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.LoopCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CopyLoop
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.Gcm.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CallTo
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Calls
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Steps
import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Callee
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Impl.Gcm.X86_64
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksContract
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CryptCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.CallTo
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Calls
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Copy
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Steps
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Mask
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Callee
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
meta import VerifiedGarbage.Proof.Gcm.Be64
meta import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Spec

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: constant time of the whole function

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments and descriptors take the same path (a comparison with
an immediate accesses no memory, `rel_cmpImm`): a text copied whole is
copied and sealed in both (`copySeal_rel`), from states the correctness
proof describes, related as ChaCha20-Poly1305's gathering relates them
(`Proof/ChaCha20Poly1305/X86_64/Gather/LoopCT.lean`, `Eq2`); a longer one
streams in both (`stream_rel`, from `CT.lean`), whatever the test
(`sealGatherG_ct`).
-/

@[expose] public section

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

theorem copyEntry_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block copyEntry) hc).isSome = true :=
  ⟨_, by simp only [copyEntry, gState, gLeft, gDst, gDesc]; taint_decide⟩

theorem sealArgs_check :
    ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block sealArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

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

/-- `sealGatherG_ct`, in two runs from states the entry states are but for
`rax`, `r10`, `r11` and the flags (`Same`). -/
theorem sealGatherG_rel {M : CtxMode} {q : Nat} {quick fast test short : Prog isa} (go : State → Bool)
    (hgo : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → go s₀' = go s₀)
    (hquick : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' →
      RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) quick fun s₁ s₂ =>
        (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (decide (L s₀ < q))) ∧
        (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (decide (L s₀' < q))))
    (hfast : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → L s₀ < q → ∀ {σ₁ σ₂ : State},
      E2 s₀ σ₁ → σ₁.gpr .r11 = W s₀ → E2 s₀' σ₂ → σ₂.gpr .r11 = W s₀' → RelCT isa (Eq2 σ₁ σ₂) fast TT)
    (htest : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' →
      RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) test fun s₁ s₂ =>
        (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (go s₀)) ∧
        (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (go s₀')))
    (hshort : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → go s₀ = true → ∀ {σ₁ σ₂ : State},
      E2 s₀ σ₁ → σ₁.gpr .r11 = W s₀ → E2 s₀' σ₂ → σ₂.gpr .r11 = W s₀' → RelCT isa (Eq2 σ₁ σ₂) short TT)
    (I : InitFn) (A : AadFn) (T : ToFn M) (F : FinFn)
    {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀') (pb : Pub s₀ s₀') :
    RelCT isa (fun a b => Same s₀ a ∧ Same s₀' b) (sealGather quick fast test short I.fn A.fn T.fn F.fn)
      fun _ _ => True := by
  have eg := hgo hp hp' pb
  unfold sealGather gatherRest
  refine RelCT.seq (entry1_rel hp hp' pb) (RelCT.seq (entry2_rel hp hp' pb) (RelCT.seq (hquick hp hp' pb)
    (RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, pb.eL]) ?_
      ((RelCT.seq (htest hp hp' pb)
        (RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, eg]) ?_
          ((stream_rel hp hp' pb I A T F).mono (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h))).mono
        (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h))))
  · refine rel_of_eq2 fun σ₁ σ₂ ⟨⟨⟨E₁, r₁, c₁⟩, ⟨E₂, r₂, c₂⟩⟩, ev⟩ => ?_
    have e : L s₀ < q := by simp only [eval, c₁] at ev; simpa using ev
    exact hfast hp hp' pb e E₁ r₁ E₂ r₂
  refine rel_of_eq2 fun σ₁ σ₂ ⟨⟨⟨E₁, r₁, c₁⟩, ⟨E₂, r₂, c₂⟩⟩, ev⟩ => ?_
  have e : go s₀ = true := by simp only [eval, c₁] at ev; simpa using ev
  exact hshort hp hp' pb e E₁ r₁ E₂ r₂

/-- `vg_aes_gcm_seal_gather`, running `fast` for a text shorter than `q`
bytes (as `quick` sets `CF`), and otherwise `short` when `test` sets `CF` (to
`go` of the arguments, which two runs with the same public data agree on), is
constant time, if `quick`, `fast`, `test` and `short` are. -/
theorem sealGatherG_ct {M : CtxMode} {q : Nat} {quick fast test short : Prog isa} (go : State → Bool)
    (hgo : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → go s₀' = go s₀)
    (hquick : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' →
      RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) quick fun s₁ s₂ =>
        (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (decide (L s₀ < q))) ∧
        (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (decide (L s₀' < q))))
    (hfast : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → L s₀ < q → ∀ {σ₁ σ₂ : State},
      E2 s₀ σ₁ → σ₁.gpr .r11 = W s₀ → E2 s₀' σ₂ → σ₂.gpr .r11 = W s₀' → RelCT isa (Eq2 σ₁ σ₂) fast TT)
    (htest : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' →
      RelCT isa (fun s₁ s₂ => E2 s₀ s₁ ∧ E2 s₀' s₂) test fun s₁ s₂ =>
        (E2 s₀ s₁ ∧ s₁.gpr .r11 = W s₀ ∧ s₁.cf = some (go s₀)) ∧
        (E2 s₀' s₂ ∧ s₂.gpr .r11 = W s₀' ∧ s₂.cf = some (go s₀')))
    (hshort : ∀ {s₀ s₀' : State}, SG M s₀ → SG M s₀' → Pub s₀ s₀' → go s₀ = true → ∀ {σ₁ σ₂ : State},
      E2 s₀ σ₁ → σ₁.gpr .r11 = W s₀ → E2 s₀' σ₂ → σ₂.gpr .r11 = W s₀' → RelCT isa (Eq2 σ₁ σ₂) short TT)
    (I : InitFn) (A : AadFn) (T : ToFn M) (F : FinFn) :
    ConstantTime isa (Proof.AesGcm.sealGatherX86_64M M).pre Proof.AesGcm.sealGatherPub
      (sealGather quick fast test short I.fn A.fn T.fn F.fn) :=
  ct_of_rel (k := Proof.AesGcm.sealGatherX86_64M M) fun _ _ h h' hq =>
    (sealGatherG_rel go hgo hquick hfast htest hshort I A T F (SG.ofM h) (SG.ofM h') (Pub.of hq)).mono
      (fun _ _ e => by obtain ⟨rfl, rfl⟩ := e; exact ⟨Same.refl _, Same.refl _⟩) fun _ _ e => e

/-- The short path of `copySeal S` below `t` bytes, in two runs. -/
theorem sealShort_rel {M : CtxMode} (S : SealFn M) {t : Nat} {s₀ s₀' : State} (hp : SG M s₀) (hp' : SG M s₀')
    (pb : Pub s₀ s₀') (e : decide (L s₀ < t) = true) (ht : t < 2 ^ 31) {σ₁ σ₂ : State}
    (E₁ : E2 s₀ σ₁) (r₁ : σ₁.gpr .r11 = W s₀) (E₂ : E2 s₀' σ₂) (r₂ : σ₂.gpr .r11 = W s₀') :
    RelCT isa (Eq2 σ₁ σ₂) (copySeal S.fn) TT := by
  have hL : L s₀ < t := by simpa using e
  exact copySeal_rel hp hp' pb S (by omega) E₁.1 r₁ E₁.2.2.1 E₁.2.2.2.1 E₂.1 r₂ E₂.2.2.1 E₂.2.2.2.1

end VG.Proof.AesGcm.X86_64.Gather
