import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.PrecomputedContract
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT

namespace VG.Proof.RsaPkcs1Sig.X86_64.PcCT

open Ver Pc
open VG.Proof.Rsa.X86_64 (PublicImpl pdChkContract)
open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def Sib (a s : State) : Prop := contract.pre s ∧ contract.pub a s

theorem pub_refl (s : State) : contract.pub s s := ⟨Ver.pub_refl s, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem Sib.r8 {a s : State} (h : Sib a s) : (s.gpr .r8).setWidth 32 = (a.gpr .r8).setWidth 32 := h.2.1.2.1.symm

theorem Sib.arg {a s : State} (h : Sib a s) {i : Nat} (hi : i < 5) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.1.2.2.1) i (List.mem_range.mpr hi)).symm

theorem Sib.e {a s : State} (h : Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.1.2.2.2.2.1.symm

theorem Sib.fb {a s : State} (h : Sib a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

theorem Sib.pre {a s : State} (h : Sib a s) :
    Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat := h.2.2.2.2.symm

theorem Sib.prePtr {a s : State} (h : Sib a s) : stackArg s 5 = stackArg a 5 := h.2.2.1.symm

theorem Sib.preLen {a s : State} (h : Sib a s) : stackArg s 6 = stackArg a 6 := h.2.2.2.1.symm

/-- A point of a run, described by `J` from the run's entry state. -/
def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : At J a t₁) (h₂ : At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- A condition `J` gives as a function of the public data. -/
theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, Sib a s → f s = f a) :
    ∀ a t₁ t₂, At J a t₁ → At J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- In the frame, `rsp` is public. -/
theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → t.gpr .rsp = fb s) : Pins (At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pin fb hJ (fun _ _ h => h.fb) h₁ h₂

/-! ## The points of the code -/

def J0 (s t : State) : Prop := t = s

def JL (s t : State) : Prop := Keep [.rax] s t ∧ t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rsi)

def JA (s t : State) : Prop :=
  ∃ t₀, JL s t₀ ∧ stackArg s 2 = s.gpr .rsi ∧ t = allocState frameBytes t₀

def J1 (s t : State) : Prop :=
  Env s t ∧ word t.mem (fb s) 0 = stackArg s 1 ∧ word t.mem (fb s) 8 = s.gpr .rsi ∧
    word t.mem (fb s) 16 = stackArg s 3 ∧ word t.mem (fb s) 24 = stackArg s 4 ∧
    t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = stackArg s 5 ∧
    t.gpr .rcx = stackArg s 6 ∧ t.gpr .r8 = s.gpr .rdx ∧ t.gpr .r9 = s.gpr .rcx ∧ stackArg s 2 = s.gpr .rsi

def J2 (s t : State) : Prop := Env s t

def JS (s t : State) : Prop := Env s t ∧ t.gpr .rax = 1

def J3 (s t : State) : Prop := Env s t ∧ t.zf = some false

def J4 (s t : State) : Prop :=
  Env s t ∧ t.gpr .r8 = off (fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rsi ∧
    t.gpr .rdx = ((s.gpr .r8).setWidth 32).setWidth 64 ∧ t.gpr .rsi = s.gpr .r9 ∧ t.gpr .r9 = stackArg s 0

/-! ## The call -/

/-- What the precomputed public operation's contract makes public. -/
theorem pub_view {a s t : State} (S : Sib a s) (h : J1 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (callRd s) (pubWr s)).gpr =
      [off (fb a) oEM1, a.gpr .rsi, stackArg a 5, stackArg a 6, a.gpr .rdx, a.gpr .rcx, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 0 = stackArg a 1 ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 1 = a.gpr .rsi ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 2 = stackArg a 3 ∧
    stackArg (t.callEntry.withRegions (callRd s) (pubWr s)) 3 = stackArg a 4 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 5) (stackArg a 6).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (callRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (callRd s) (pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, -⟩ := h
  have hp := Pc.pre_of S.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rsi) (by decide),
      S.prePtr, S.preLen, S.gpr (r := .rdx) (by decide), S.gpr (r := .rcx) (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.gpr (r := .rsi) (by decide)]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [State.withRegions_mem, pre_words hp (frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)), S.pre]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [entryBytes he _ _ hp.dKe hp.des.symm (by have := hp.wE; omega), S.e]

theorem call_ct (v : PublicImpl) : RelCT isa (Two (At J1)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pdChkContract) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := call_covers (Pc.pre_of S₁.1) j₁.2.2.2.2.2.2.2.2.2.2.2 j₁.1
  obtain ⟨c₂, w₂⟩ := call_covers (Pc.pre_of S₂.1) j₂.2.2.2.2.2.2.2.2.2.2.2 j₂.1
  obtain ⟨he₁, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁, hg₁⟩ := j₁
  obtain ⟨he₂, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂, hg₂⟩ := j₂
  have p₁ := Pc.call_pre (Pc.pre_of S₁.1) hg₁ he₁.rsp hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ := Pc.call_pre (Pc.pre_of S₂.1) hg₂ he₂.rsp hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pdChkContract.pub (t₁.callEntry.withRegions (callRd s₁) (pubWr s₁))
      (t₂.callEntry.withRegions (callRd s₂) (pubWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩
  exact ⟨callRd s₁, pubWr s₁, callRd s₂, pubWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## The pieces -/

theorem lenCheck_two : RelCT isa (Two (At J0)) (.block lenCheck) (Two (At JL)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin (fun s => s.gpr .rsp) (fun s t h => by rw [h]) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      rw [show t = s from ht]
      exact WP.mono (lenCheck_ok (Pc.pre_of S.1).toPreV) fun _ h => ⟨s, S, h⟩

theorem pubArgs_two : RelCT isa (Two (At JA)) (.block Impl.RsaPkcs1Sig.X86_64.Precomputed.pubArgs) (Two (At J1)) :=
  two_piece [.rsp] (pins_rsp fun s t ⟨t₀, ⟨k₀, _, _⟩, _, ht⟩ => by
      subst ht; show t₀.gpr .rsp - _ = _; rw [k₀.gpr (by decide)]) (by taint_decide)
    fun _ t ⟨s, S, t₀, ⟨k₀, hm₀, _⟩, hg, ht⟩ => by
      subst ht
      have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
      have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
      have hA : Keep [.rax] (allocState frameBytes s) (allocState frameBytes t₀) :=
        ⟨fun r hr => by
          simp only [allocState_gpr, fb, hsp₀]
          split
          · rfl
          · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
      exact WP.mono (args_ok (Pc.pre_of S.1) hA hm₀)
        fun _ ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, _⟩ =>
          ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩

theorem call_two (v : PublicImpl) : RelCT isa (Two (At J1)) (.call v.name v.code) (Two (At J2)) :=
  two_post (call_ct v) fun _ _ ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩ =>
    WP.mono (call_ok v (Pc.pre_of S.1) hg he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) fun _ h =>
      ⟨s, S, h.1⟩

theorem save_two : RelCT isa (Two (At J2))
    (.block [.store (sp 0) .rax, .mov32 .rax (.imm 1)]) (Two (At JS)) :=
  two_piece [.rsp] (pins_rsp fun _ _ h => h.rsp) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (save_ok (Pc.pre_of S.1) he) fun _ h => ⟨s, S, h.1, h.2.1⟩

theorem test0_two : RelCT isa (Two (At JS)) (.block test0) (Two (At J3)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, he, ha⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ =>
      ⟨s, S, he.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2, by rw [hz, ha]; rfl⟩

theorem encArgs_two : RelCT isa (Two fun a t => At J3 a t ∧ isa.eval .e t = some false) (.block encArgs)
    (Two (At J4)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pins_rsp (J := J3) (fun _ _ h => h.1.rsp) _ _ _ h₁.1 h₂.1 _ (List.mem_singleton_self _))
    (by taint_decide)
    fun _ t ⟨⟨s, S, he, _⟩, _⟩ => WP.mono (encArgs_ok (Pc.pre_of S.1).toPreV he)
      fun u ⟨hK, hm, h8, hcx, hdx, hsi, h9⟩ =>
        ⟨s, S, he.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, h8, hcx, hdx, hsi, h9⟩

theorem encTail_ct : RelCT isa (Two (At J4)) (.seq encode tail) fun _ _ => True :=
  encTail_taint fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact pin fb (fun _ _ h => h.1.rsp) (fun _ _ S => S.fb) h₁ h₂
    · exact pin (fun s => off (fb s) oEM2) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
    · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pin (fun s => ((s.gpr .r8).setWidth 32).setWidth 64) (fun _ _ h => h.2.2.2.1)
        (fun _ _ S => by rw [S.r8]) h₁ h₂
    · exact pin (fun s => s.gpr .r9) (fun _ _ h => h.2.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pin (fun s => stackArg s 0) (fun _ _ h => h.2.2.2.2.2) (fun _ _ S => S.arg (by decide)) h₁ h₂

theorem padding_ct : RelCT isa (Two (At JS)) afterPub fun _ _ => True := by
  unfold afterPub
  refine RelCT.seq test0_two (two_ite ?_ ret0_ct (RelCT.seq encArgs_two encTail_ct))
  exact pinEval (fun _ => some false) (fun _ _ h => by simp only [eval, h.2]) (fun _ _ _ => rfl)

theorem padding_two : RelCT isa (Two (At JS)) afterPub (Two (At J2)) :=
  two_post padding_ct fun _ t ⟨s, S, he, ha⟩ =>
    WP.mono (afterPub_checked (some (Spec.Rsa.bytesAt t.mem (off (fb s) oEM1) (s.gpr .rsi).toNat))
      (Pc.pre_of S.1).toPreV he ⟨by rw [ha]; decide, rfl⟩) fun _ h => ⟨s, S, h.1⟩

theorem mask_ct : RelCT isa (Two (At J2))
    (.block [.mov .rcx (.mem (sp 0)), .alu32 .and .rax (.reg .rcx)]) fun _ _ => True :=
  two_taint [.rsp] (pins_rsp fun _ _ h => h.rsp) (by taint_decide)

theorem afterPub_ct : RelCT isa (Two (At J2)) Impl.RsaPkcs1Sig.X86_64.Precomputed.afterPub fun _ _ => True :=
  RelCT.seq save_two (RelCT.seq padding_two mask_ct)

theorem body_ct (v : PublicImpl) : RelCT isa (Two (At JA))
    (Impl.RsaPkcs1Sig.X86_64.Precomputed.body v.name v.code) fun _ _ => True :=
  RelCT.seq pubArgs_two (RelCT.seq (call_two v) afterPub_ct)

/-! ## The frame -/

theorem code_ct (v : PublicImpl) : RelCT isa (Two (At J0)) (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) fun _ _ => True := by
  unfold Impl.RsaPkcs1Sig.X86_64.Precomputed.code
  refine RelCT.seq lenCheck_two (two_ite ?_ ret0_ct (relCT_alloc ((body_ct v).mono ?_ fun _ _ h => h)))
  · refine pinEval (fun s => some (!(stackArg s 2 == s.gpr .rsi))) (fun s t h => by simp only [eval, h.2.2, Option.map_some]) ?_
    intro a s S
    rw [S.arg (by decide), S.gpr (by decide)]
  · rintro _ _ ⟨t₁, t₂, ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩, rfl, rfl⟩
    have hg : ∀ {s t}, JL s t → isa.eval .ne t = some false → stackArg s 2 = s.gpr .rsi := fun j e => by
      simp only [eval, j.2.2, Option.map_some, Option.some.injEq, Bool.not_eq_false', beq_iff_eq] at e
      exact e
    exact ⟨a, ⟨s₁, S₁, t₁, j₁, hg j₁ e₁, rfl⟩, ⟨s₂, S₂, t₂, j₂, hg j₂ e₂, rfl⟩⟩

theorem code_constantTime (v : PublicImpl) :
    ConstantTime isa contract.pre contract.pub (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) :=
  RelCT.constantTime ((code_ct v).mono
    (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩) fun _ _ h => h)

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_verify_precomputed`, calling the implementation `v` of
`vg_rsa_public_precomputed_checked`, meets the shared contract. -/
theorem code_verified (v : PublicImpl) :
    Verified target (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verStack) :=
  have hct : ConstantTime isa contract.pre contract.pub (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code) := code_constantTime v
  Verified.of_correct (k := contract) (Pc.code_correct v) hct Pc.implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PublicImpl) : (Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.RsaPkcs1Sig.X86_64.Precomputed.code, Impl.RsaPkcs1Sig.X86_64.Precomputed.body, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Sig.X86_64.PcCT
