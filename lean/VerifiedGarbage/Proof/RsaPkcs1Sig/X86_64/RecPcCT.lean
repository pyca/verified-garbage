module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcContract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcContract
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Compare
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_pkcs1_recover_precomputed` on x86-64: constant time

Before the call, as for `vg_rsa_pkcs1_recover` (`RecoverCT`), for entry
states related to the anchor by `contract` (`PR`), and the call, constant
time for its contract, which makes `pre`'s words public too. After it,
whatever the call left: the blocks and loops are checked by the taint
analysis from the registers correctness fixes, and the one branch, on
whether `encode` succeeds, depends on `hash`, `n_len` and `out_len` alone
(`encodeId_isSome`), not on `EM₁`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.RecPcCT

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed (maskM maskArgs fin)
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 ret0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR frame_sub test0_ok relCT_alloc entry_regs regs_eq
  stackArg_entry callEntry_frame below_sub)
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open RecPc

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def PR (a s : State) : Prop := contract.pre s ∧ contract.pub a s

theorem pr_sib : ∀ a s, PR a s → Rec.Sib a s := fun _ _ h => ⟨(pre_of h.1).toPreR, h.2.1⟩

theorem pub_refl (s : State) : contract.pub s s := ⟨Rec.pub_refl s, rfl, rfl, rfl⟩

def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, PR a s ∧ J s t

theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Rec.Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : At J a t₁) (h₂ : At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ (pr_sib _ _ S₁), hs _ _ (pr_sib _ _ S₂)]

theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, Rec.Sib a s → f s = f a) :
    ∀ a t₁ t₂, At J a t₁ → At J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ (pr_sib _ _ S₁), hs _ _ (pr_sib _ _ S₂)]

theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → t.gpr .rsp = fb s) : Pins (At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pin fb hJ (fun _ _ h => h.fb) h₁ h₂

theorem two_and {J : State → State → Prop} {P : State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (At fun s t => J s t ∧ P t)) c Q) :
    RelCT isa (Two fun a t => At J a t ∧ P t) c Q :=
  h.mono (fun _ _ ⟨a, ⟨⟨s₁, S₁, j₁⟩, p₁⟩, ⟨⟨s₂, S₂, j₂⟩, p₂⟩⟩ => ⟨a, ⟨s₁, S₁, j₁, p₁⟩, ⟨s₂, S₂, j₂, p₂⟩⟩)
    fun _ _ h => h

/-! ## Before the call -/

theorem lenCheck_two : RelCT isa (Two (At Rec.J0)) (.block lenCheck) (Two (At Rec.JL)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin (fun s => s.gpr .rsp) (fun s t h => by rw [show t = s from h]) (fun _ _ S => S.gpr (by decide))
        h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      rw [show t = s from ht]
      exact WP.mono (Rec.lenCheck_ok (pr_sib _ _ S).1) fun _ h => ⟨s, S, h⟩

theorem zeroOut0_ct : RelCT isa (Two fun a t => At Rec.JL a t ∧ isa.eval .ne t = some true) zeroOut fun _ _ => True :=
  two_and (Rec.zeroOut_taint fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pin (fun s => s.gpr .rdi) (fun _ _ h => h.1.1.gpr (by decide)) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.1.1.gpr (by decide)) (fun _ _ S => S.gpr (by decide)) h₁ h₂)

theorem pubArgs_two : RelCT isa (Two (At Rec.JA)) (.block Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.pubArgs)
    (Two (At RecPc.J1)) :=
  two_piece [.rsp] (pins_rsp fun s t ⟨t₀, ⟨k₀, _, _⟩, _, ht⟩ => by
      subst ht; show t₀.gpr .rsp - _ = _; rw [k₀.gpr (by decide)]) (by taint_decide)
    fun _ t ⟨s, S, t₀, ⟨k₀, hm₀, _⟩, hg, ht⟩ => by
      subst ht
      have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
      have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
      have hA : Keep [.rax] (allocState frameBytes s) (allocState frameBytes t₀) :=
        ⟨fun r hr => by
          simp only [Ver.allocState_gpr, fb, hsp₀]
          split
          · rfl
          · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
      exact WP.mono (RecPc.pubArgs_ok (pre_of S.1) hg hA hm₀) fun _ h => ⟨s, S, h.1⟩

/-! ## The call -/

theorem pub_view {a s t : State} (S : PR a s) (h : RecPc.J1 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr =
      [off (fb a) oEM1, a.gpr .rcx, stackArg a 5, stackArg a 6, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (callRd s) (Rec.pubWr s)) 0 = stackArg a 1 ∧
    stackArg (t.callEntry.withRegions (callRd s) (Rec.pubWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (callRd s) (Rec.pubWr s)) 2 = stackArg a 3 ∧
    stackArg (t.callEntry.withRegions (callRd s) (Rec.pubWr s)) 3 = stackArg a 4 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (callRd s) (Rec.pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (callRd s) (Rec.pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (callRd s) (Rec.pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, -⟩ := h
  have hp := pre_of S.1
  have S' := pr_sib _ _ S
  have hfE : Frame [stkR s, Rec.outR s, scrR s] s.mem t.callEntry.mem :=
    Rec.frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S'.fb, S'.gpr (r := .rcx) (by decide),
      S.2.2.1, S.2.2.2.1, S'.gpr (r := .r8) (by decide), S'.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S'.arg (by decide) (by decide)]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S'.gpr (r := .rcx) (by decide)]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S'.arg (by decide) (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S'.arg (by decide) (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [State.withRegions_mem, pre_words hp hfE, S.2.2.2.2]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [Rec.entryBytes he _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega), S'.e]

theorem call_ct (v : PublicImpl) : RelCT isa (Two (At RecPc.J1)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pdChkContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := call_covers (pre_of S₁.1) j₁.2.2.2.2.2.2.2.2.2.2.2 j₁.1
  obtain ⟨c₂, w₂⟩ := call_covers (pre_of S₂.1) j₂.2.2.2.2.2.2.2.2.2.2.2 j₂.1
  have p₁ := call_pre (pre_of S₁.1) j₁
  have p₂ := call_pre (pre_of S₂.1) j₂
  have hpub : pdChkContract.pub (t₁.callEntry.withRegions (callRd s₁) (Rec.pubWr s₁))
      (t₂.callEntry.withRegions (callRd s₂) (Rec.pubWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩
  exact ⟨callRd s₁, Rec.pubWr s₁, callRd s₂, Rec.pubWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [j₁.1.rsp, j₂.1.rsp, (pr_sib _ _ S₁).fb, (pr_sib _ _ S₂).fb]⟩

/-- In the frame. -/
def JE (s t : State) : Prop := Rec.Env s t

theorem call_two (v : PublicImpl) : RelCT isa (Two (At RecPc.J1)) (.call v.name v.code) (Two (Rec.At JE)) :=
  two_post (call_ct v) fun _ _ ⟨s, S, h⟩ =>
    WP.mono (call_ok v (pre_of S.1) h) fun _ h => ⟨s, pr_sib _ _ S, h.1⟩

/-! ## After the call -/

/-- `encode`'s status depends only on the length of the hash value. -/
theorem encodeId_isSome {x : BitVec 32} {H H' : List Byte} {k : Nat} (hl : H.length = H'.length) :
    (encodeId x H k).isSome = (encodeId x H' k).isSome := by
  unfold encodeId
  split
  · simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, hl]
    split <;> rfl
  · rfl

/-- Whether `encode` succeeds, from the entry state. -/
def stat (s : State) : Bool :=
  (encodeId ((stackArg s 0).setWidth 32) (List.replicate (s.gpr .rsi).toNat 0) (s.gpr .rcx).toNat).isSome

theorem stat_sib {a s : State} (S : Rec.Sib a s) : stat s = stat a := by
  simp only [stat, S.h, S.gpr (r := .rsi) (by decide), S.gpr (r := .rcx) (by decide)]

def JH (s t : State) : Prop :=
  Rec.Env s t ∧ t.gpr .r8 = off (fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .r9 = s.gpr .rsi ∧ t.gpr .rsi = Rec.valA s

theorem head_ok {s t : State} (hp : Rec.PreR s) (he : Rec.Env s t) :
    WP isa (.block (([.store (sp 0) .rax] : List Instr) ++ encArgs)) t (JH s) := by
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp he) fun t₁ ⟨k₁, hm₁⟩ => ?_
  have he₁ : Rec.Env s t₁ := Env.low he (d := 0) (by decide) (k₁.gpr (by decide)) k₁.2.1 k₁.2.2 hm₁
  refine WP.mono (Rec.encArgs_ok hp he₁) fun u ⟨hK, hm, h8, hcx, hdx, h9, hsi⟩ =>
    ⟨he₁.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, h8, hcx, hdx, h9, hsi⟩

theorem head_two : RelCT isa (Two (Rec.At JE)) (.block (([.store (sp 0) .rax] : List Instr) ++ encArgs)) (Two (Rec.At JH)) :=
  two_piece [.rsp] (Rec.pins_rsp fun _ _ h => h.rsp) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (head_ok S.1 he) fun _ h => ⟨s, S, h⟩

def JS (s t : State) : Prop :=
  ∃ t₄, JH s t₄ ∧ Keep clob t₄ t ∧ ∃ H : List Byte, H.length = (s.gpr .rsi).toNat ∧
    EOut t₄ t (encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat)

theorem encode_two : RelCT isa (Two (Rec.At JH)) encode (Two (Rec.At JS)) :=
  two_piece [.rsp, .r8, .rcx, .rdx, .rsi, .r9] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Rec.pin fb (fun _ _ h => h.1.rsp) (fun _ _ S => S.fb) h₁ h₂
      · exact Rec.pin (fun s => off (fb s) oEM2) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact Rec.pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
      · exact Rec.pin (fun s => ((stackArg s 0).setWidth 32).setWidth 64) (fun _ _ h => h.2.2.2.1)
          (fun _ _ S => by rw [S.h]) h₁ h₂
      · exact Rec.pin Rec.valA (fun _ _ h => h.2.2.2.2.2) (fun _ _ S => S.valA) h₁ h₂
      · exact Rec.pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, j⟩ => by
      obtain ⟨he, h8, hcx, hdx, h9, hsi⟩ := j
      refine WP.mono (encode_ok (Rec.encPre S.1 he h8 hcx hdx h9 hsi)) fun u ⟨hK, hout⟩ =>
        ⟨s, S, t, ⟨he, h8, hcx, hdx, h9, hsi⟩, hK, _, by rw [bytesAt_length, h9], hout⟩

def JT (s t : State) : Prop := ∃ t₅, JS s t₅ ∧ SameF t₅ t ∧ t.zf = some !(stat s)

theorem test0_two : RelCT isa (Two (Rec.At JS)) (.block test0) (Two (Rec.At JT)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, j⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ => ⟨s, S, t, j, hs, by
      obtain ⟨t₄, -, -, H, hl, hout⟩ := j
      have hst : stat s = (encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat).isSome :=
        encodeId_isSome (by rw [hl, List.length_replicate])
      rw [hz, hst]
      cases h : encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat with
      | none => rw [h] at hout; rw [hout.1]; rfl
      | some em' => rw [h] at hout; rw [hout.1]; rfl⟩

theorem JT_none {s t : State} (h : JT s t) (he : isa.eval .e t = some true) : Rec.Env s t := by
  obtain ⟨t₅, ⟨t₄, j₄, hK, H, hl, hout⟩, hs, hz⟩ := h
  have hn : encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat = none := by
    have : stat s = false := by
      simp only [eval, hz, Option.some.injEq, Bool.not_eq_true'] at he; exact he
    rw [stat, ← encodeId_isSome (by rw [hl, List.length_replicate])] at this
    simpa using this
  rw [hn] at hout
  exact (j₄.1.regs (by rw [hK.gpr (by decide)]) hout.2 hK.2.1 hK.2.2).regs (by rw [hs.1]) hs.2.1 hs.2.2.1
    hs.2.2.2

def JC (s t : State) : Prop :=
  Rec.Env s t ∧ t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = off (fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rcx

theorem cmpArgs_two : RelCT isa (Two fun a t => Rec.At JT a t ∧ isa.eval .e t = some false) (.block cmpArgs)
    (Two (Rec.At JC)) :=
  Rec.two_and (two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact Rec.pin fb (fun s t h => by
        obtain ⟨⟨t₅, ⟨t₄, j₄, hK, _⟩, hs, _⟩, _⟩ := h
        rw [hs.1, hK.gpr (by decide)]; exact j₄.1.rsp) (fun _ _ S => S.fb) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ⟨t₅, ⟨t₄, j₄, hK, H, hl, hout⟩, hs, hz⟩, he⟩ => by
      have hp := S.1
      have hsome : (encodeId ((stackArg s 0).setWidth 32) H (s.gpr .rcx).toNat).isSome = true := by
        have : stat s = true := by
          simp only [eval, hz, Option.some.injEq, Bool.not_eq_false'] at he; exact he
        rwa [stat, encodeId_isSome (by rw [hl, List.length_replicate])] at this
      obtain ⟨em', hem'⟩ := Option.isSome_iff_exists.mp hsome
      rw [hem'] at hout
      obtain ⟨he₄, h8₄, hcx₄, -, -, -⟩ := j₄
      obtain ⟨he₅, -, -, -⟩ := Rec.encDone hp he₄ hK h8₄ (Rec.encodeId_length hem') hout
      have he₆ : Rec.Env s t := he₅.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2
      refine WP.mono (Rec.cmpArgs_ok he₆) fun u ⟨hK', hm, hdi, hsi⟩ =>
        ⟨s, S, he₆.regs (hK'.gpr (by decide)) hm hK'.2.1 hK'.2.2, hdi, hsi, ?_⟩
      rw [hK'.gpr (by decide), hs.1, hK.gpr (by decide), hcx₄])

def JQ (s t : State) : Prop := Rec.Env s t ∧ t.gpr .rcx = s.gpr .rcx

theorem compare_two : RelCT isa (Two (Rec.At JC)) compare (Two (Rec.At JQ)) :=
  two_piece [.rdi, .rsi, .rcx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact Rec.pin (fun s => off (fb s) oEM1) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact Rec.pin (fun s => off (fb s) oEM2) (fun _ _ h => h.2.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact Rec.pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, he, hdi, hsi, hcx⟩ => by
      have hp := S.1
      have hk1 := hp.k1
      have hk2 := hp.k2
      have hr : ∀ i < (s.gpr .rcx).toNat, InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
          InRegions (t.rd ++ t.wr) (t.gpr .rsi + BitVec.ofNat 64 i) 1 := fun i hi => by
        rw [hdi, hsi, he.wr]
        obtain ⟨r₁, h₁, c₁⟩ := Rec.frame_bytes' hp (d := oEM1) (n := (s.gpr .rcx).toNat)
          (by unfold oEM1 frameBytes; omega) i hi
        obtain ⟨r₂, h₂, c₂⟩ := Rec.frame_bytes' hp (d := oEM2) (n := (s.gpr .rcx).toNat)
          (by unfold oEM2 frameBytes; omega) i hi
        exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
      exact WP.mono (compare_ok (by rw [hcx]) (by omega) hr) fun u ⟨hK, hm, _⟩ =>
        ⟨s, S, he.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, by rw [hK.gpr (by decide), hcx]⟩

theorem maskM_two : RelCT isa (Two (Rec.At JQ)) (.block maskM) (Two (Rec.At JQ)) :=
  two_piece [.rsp] (Rec.pins_rsp fun _ _ h => h.1.rsp) (by taint_decide)
    fun _ _ ⟨s, S, he, hcx⟩ => WP.mono (maskM_ok S.1 he) fun _ ⟨k, hm, _⟩ =>
      ⟨s, S, Env.low he (d := 8) (by decide) (k.gpr (by decide)) k.2.1 k.2.2 hm,
        by rw [k.gpr (by decide), hcx]⟩

theorem copyOut_two : RelCT isa (Two (Rec.At JQ)) copyOut (Two (Rec.At JE)) :=
  two_post (Rec.copyOut_ct fun _ _ h => h) fun _ _ ⟨s, S, he, hcx⟩ =>
    WP.mono (Rec.copyOut_ok S.1 he hcx) fun _ h => ⟨s, S, h.1⟩

def JM (s t : State) : Prop :=
  t.gpr .rsp = fb s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rsi ∧ t.gpr .r10 = BitVec.ofNat 64 0

theorem maskArgs_two : RelCT isa (Two (Rec.At JE)) (.block maskArgs) (Two (Rec.At JM)) :=
  two_piece [.rsp] (Rec.pins_rsp fun _ _ h => h.rsp) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (maskArgs_ok S.1 he) fun _ ⟨k, _, hdi, hcx, _, h10⟩ =>
      ⟨s, S, (k.gpr (by decide)).trans he.rsp, hdi, hcx, h10⟩

theorem mask_ct : RelCT isa (Two (Rec.At JM))
    (.seq Impl.RsaPkcs1Enc.X86_64.Encrypt.maskLoop (.block fin)) fun _ _ => True :=
  two_taint [.rsp, .rdi, .rcx, .r10] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Rec.pin fb (fun _ _ h => h.1) (fun _ _ S => S.fb) h₁ h₂
    · exact Rec.pin (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact Rec.pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact Rec.pin (fun _ => BitVec.ofNat 64 0) (fun _ _ h => h.2.2.2) (fun _ _ _ => rfl) h₁ h₂)
    (by taint_decide)

theorem release_ct : RelCT isa (Two (Rec.At JQ)) RecoverPrecomputed.release fun _ _ => True := by
  unfold RecoverPrecomputed.release
  exact RelCT.seq maskM_two (RelCT.seq copyOut_two (RelCT.seq maskArgs_two mask_ct))

theorem tail_ct : RelCT isa (Two (Rec.At JS)) RecoverPrecomputed.tail fun _ _ => True := by
  unfold RecoverPrecomputed.tail
  refine RelCT.seq test0_two (two_ite ?_ (Rec.two_and (Rec.zeroSlots_ct fun _ _ h => JT_none h.1 h.2))
    (RelCT.seq cmpArgs_two (RelCT.seq compare_two release_ct)))
  · exact Rec.pinEval (fun s => some !(stat s)) (fun s t h => by
      obtain ⟨_, _, _, hz⟩ := h; simp only [eval, hz]) fun _ _ S => by rw [stat_sib S]

theorem afterPub_ct : RelCT isa (Two (Rec.At JE)) RecoverPrecomputed.afterPub fun _ _ => True := by
  unfold RecoverPrecomputed.afterPub
  exact RelCT.seq head_two (RelCT.seq encode_two tail_ct)

/-! ## The whole function -/

theorem body_ct (v : PublicImpl) : RelCT isa (Two (At Rec.JA))
    (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.body v.name v.code) fun _ _ => True :=
  RelCT.seq pubArgs_two (RelCT.seq (call_two v) afterPub_ct)

theorem code_ct (v : PublicImpl) : RelCT isa (Two (At Rec.J0))
    (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code) fun _ _ => True := by
  unfold Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code
  refine RelCT.seq lenCheck_two (two_ite ?_ zeroOut0_ct (relCT_alloc ((body_ct v).mono ?_ fun _ _ h => h)))
  · refine pinEval (fun s => some (!(stackArg s 2 == s.gpr .rcx))) (fun s t h => by
      simp only [eval, h.2.2, Option.map_some]) ?_
    intro a s S
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  · rintro _ _ ⟨t₁, t₂, ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩, rfl, rfl⟩
    have hg : ∀ {s t}, Rec.JL s t → isa.eval .ne t = some false → stackArg s 2 = s.gpr .rcx := fun j e => by
      simp only [eval, j.2.2, Option.map_some, Option.some.injEq, Bool.not_eq_false', beq_iff_eq] at e
      exact e
    exact ⟨a, ⟨s₁, S₁, t₁, j₁, hg j₁ e₁, rfl⟩, ⟨s₂, S₂, t₂, j₂, hg j₂ e₂, rfl⟩⟩

theorem code_constantTime (v : PublicImpl) :
    ConstantTime isa contract.pre contract.pub (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code) :=
  RelCT.constantTime ((code_ct v).mono
    (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩) fun _ _ h => h)

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_recover_precomputed`, calling the implementation `v` of
`vg_rsa_public_precomputed_checked`, meets the shared contract. -/
theorem code_verified (v : PublicImpl) :
    Verified target (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi verStack) :=
  Verified.of_correct (k := contract) (code_correct v) (code_constantTime v) implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PublicImpl) :
    (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code, Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.body,
    Code.all, v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Sig.X86_64.RecPcCT
