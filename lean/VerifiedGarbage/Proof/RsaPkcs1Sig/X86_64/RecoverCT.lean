import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT

/-!
# `vg_rsa_pkcs1_recover` on x86-64: constant time

As for `vg_rsa_pkcs1_verify` (`VerifyCT.lean`): each point of the code is
described, in each run, by what correctness says of it from that run's entry
state, which agrees with an anchor on the public data (`At`). The blocks
between the call and the branches are checked by the taint analysis from the
registers this fixes, each branch's condition is fixed by it too, and the
call is constant time for its callee's contract. The zeros and the copy to
`out` take its address and length from the frame's slots, which the taint
analysis does not know public: their loads are a piece of their own, and the
loops after them are checked from the registers correctness fixes.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 ret0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR frame_sub test0_ok relCT_alloc entry_regs regs_eq
  written_r stackArg_entry callEntry_frame below_sub)

/-! ## The taint checks -/

theorem lenCheck_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block lenCheck) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem zeroOut_taint {Φ : State → State → Prop} (h : Pins Φ [.rdi, .rsi]) :
    RelCT isa (Two Φ) zeroOut fun _ _ => True := two_taint [.rdi, .rsi] h (by taint_decide)

theorem pubArgs_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem zeroHead_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl))]) fun _ _ => True :=
  two_taint [.rsp] h (by taint_decide)

theorem encArgs_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block encArgs) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem encode_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp, .r8, .rcx, .rdx, .rsi, .r9]) :
    RelCT isa (Two Φ) encode fun _ _ => True :=
  two_taint [.rsp, .r8, .rcx, .rdx, .rsi, .r9] h (by taint_decide)

theorem cmpArgs_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block cmpArgs) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem compare_taint {Φ : State → State → Prop} (h : Pins Φ [.rdi, .rsi, .rcx]) :
    RelCT isa (Two Φ) compare fun _ _ => True := two_taint [.rdi, .rsi, .rcx] h (by taint_decide)

theorem copyHead_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block ([.mov .r8 (.mem (sp oOut)), .mov .rdi (.reg .r8), .mov .r9 (.mem (sp oOl))] ++ valPtr))
      fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem copyRest_taint {Φ : State → State → Prop} (h : Pins Φ [.rsi, .rdi, .r9]) :
    RelCT isa (Two Φ) (.seq copyLoop (.block [.mov32 .rax (.imm 1)])) fun _ _ => True :=
  two_taint [.rsi, .rdi, .r9] h (by taint_decide)

/-! ## Entry states and the anchor -/

def Sib (a s : State) : Prop := recContract.pre s ∧ recContract.pub a s

theorem pub_refl (s : State) : recContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.h {a s : State} (h : Sib a s) : (stackArg s 0).setWidth 32 = (stackArg a 0).setWidth 32 :=
  h.2.2.1.symm

theorem Sib.arg {a s : State} (h : Sib a s) {i : Nat} (hi : 1 ≤ i) (hi' : i < 5) : stackArg s i = stackArg a i := by
  have := h.2.2.2.1
  simp only [List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, -⟩ := this
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm

theorem Sib.n {a s : State} (h : Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.2.2.2.1.symm

theorem Sib.e {a s : State} (h : Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.2.2.2.2.2.1.symm

theorem Sib.g {a s : State} (h : Sib a s) :
    Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat =
      Spec.Rsa.bytesAt a.mem (stackArg a 1) (stackArg a 2).toNat :=
  h.2.2.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : Sib a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

theorem Sib.valA {a s : State} (h : Sib a s) : valA s = valA a := by
  show off (Ver.fb s) _ = off (Ver.fb a) _
  rw [h.fb, h.gpr (r := .rcx) (by decide), h.gpr (r := .rsi) (by decide)]

def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, Sib a s ∧ J s t

theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : At J a t₁) (h₂ : At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, Sib a s → f s = f a) :
    ∀ a t₁ t₂, At J a t₁ → At J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → t.gpr .rsp = fb s) : Pins (At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pin fb hJ (fun _ _ h => h.fb) h₁ h₂

/-- `At` with a condition on the state. -/
theorem at_and {J : State → State → Prop} {P : State → Prop} {a t : State} (h : At J a t ∧ P t) :
    At (fun s t => J s t ∧ P t) a t :=
  let ⟨⟨s, S, j⟩, p⟩ := h; ⟨s, S, j, p⟩

theorem two_and {J : State → State → Prop} {P : State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (At fun s t => J s t ∧ P t)) c Q) :
    RelCT isa (Two fun a t => At J a t ∧ P t) c Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, at_and h₁, at_and h₂⟩) fun _ _ h => h

/-! ## The points of the code -/

def J0 (s t : State) : Prop := t = s

def JL (s t : State) : Prop := Keep [.rax] s t ∧ t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rcx)

def JA (s t : State) : Prop :=
  ∃ t₀, JL s t₀ ∧ stackArg s 2 = s.gpr .rcx ∧ t = allocState frameBytes t₀

def J1 (s t : State) : Prop :=
  Env s t ∧ word t.mem (fb s) 0 = stackArg s 1 ∧ word t.mem (fb s) 8 = s.gpr .rcx ∧
    word t.mem (fb s) 16 = stackArg s 3 ∧ word t.mem (fb s) 24 = stackArg s 4 ∧
    t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧
    t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9 ∧ stackArg s 2 = s.gpr .rcx

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rcx).toNat)

theorem pubOut_sib {a s : State} (S : Sib a s) (hs : stackArg s 2 = s.gpr .rcx) : pubOut s = pubOut a := by
  have ha : stackArg a 2 = a.gpr .rcx := by rw [← S.arg (by decide) (by decide), hs, S.gpr (by decide)]
  have hg := S.g
  rw [hs, ha] at hg
  unfold pubOut; rw [S.n, S.e, hg]

def J2 (s t : State) : Prop :=
  Env s t ∧ Spec.Rsa.written t.mem (off (fb s) oEM1) (s.gpr .rcx).toNat ((t.gpr .rax).setWidth 32) (pubOut s) ∧
    stackArg s 2 = s.gpr .rcx

def J3 (s t : State) : Prop := J2 s t ∧ t.zf = some !(pubOut s).isSome

/-- `EM`, if RSAVP1 succeeds. -/
def emOut (s : State) : List Byte := (pubOut s).getD []

def J4 (s t : State) : Prop :=
  Env s t ∧ t.gpr .r8 = off (fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .r9 = s.gpr .rsi ∧ t.gpr .rsi = valA s ∧
    Spec.Rsa.bytesAt t.mem (off (fb s) oEM1) (s.gpr .rcx).toNat = emOut s ∧ stackArg s 2 = s.gpr .rcx

/-- The encoding of the last `out_len` bytes of `EM`. -/
def encRes (s : State) : Option (List Byte) :=
  encodeId ((stackArg s 0).setWidth 32) ((emOut s).drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat))
    (s.gpr .rcx).toNat

def J5 (s t : State) : Prop := ∃ t₄, J4 s t₄ ∧ Keep clob t₄ t ∧ EOut t₄ t (encRes s)

def J6 (s t : State) : Prop := ∃ t₅, J5 s t₅ ∧ SameF t₅ t ∧ t.zf = some !(encRes s).isSome

/-- The encoding, if it succeeds. -/
def encVal (s : State) : List Byte := (encRes s).getD []

def J7 (s t : State) : Prop :=
  Env s t ∧ t.gpr .rdi = off (fb s) oEM1 ∧ t.gpr .rsi = off (fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rcx ∧
    Spec.Rsa.bytesAt t.mem (off (fb s) oEM1) (s.gpr .rcx).toNat = emOut s ∧
    Spec.Rsa.bytesAt t.mem (off (fb s) oEM2) (s.gpr .rcx).toNat = encVal s ∧ stackArg s 2 = s.gpr .rcx

def J8 (s t : State) : Prop :=
  Env s t ∧ t.gpr .rcx = s.gpr .rcx ∧ (t.gpr .rdx = 0 ↔ emOut s = encVal s) ∧ stackArg s 2 = s.gpr .rcx

def J9 (s t : State) : Prop :=
  Env s t ∧ t.gpr .rcx = s.gpr .rcx ∧ t.zf = some (decide (emOut s = encVal s)) ∧ stackArg s 2 = s.gpr .rcx

theorem emOut_sib {a s : State} (S : Sib a s) (hs : stackArg s 2 = s.gpr .rcx) : emOut s = emOut a := by
  simp only [emOut, pubOut_sib S hs]

theorem encRes_sib {a s : State} (S : Sib a s) (hs : stackArg s 2 = s.gpr .rcx) : encRes s = encRes a := by
  simp only [encRes, emOut_sib S hs, S.h, S.gpr (r := .rcx) (by decide), S.gpr (r := .rsi) (by decide)]

theorem encVal_sib {a s : State} (S : Sib a s) (hs : stackArg s 2 = s.gpr .rcx) : encVal s = encVal a := by
  simp only [encVal, encRes_sib S hs]

theorem encodeId_length {x : BitVec 32} {H : List Byte} {k : Nat} {em' : List Byte}
    (h : encodeId x H k = some em') : em'.length = k := by
  unfold encodeId at h
  split at h
  · exact VG.Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-! ## The call -/

theorem entryBytes {s t : State} (he : Env s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact bytes_of_frame (frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)) hk ho hs hl

theorem pub_view {a s t : State} (S : Sib a s) (h : J1 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (pubRd s) (pubWr s)).gpr =
      [off (fb a) oEM1, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 0 = stackArg a 1 ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 2 = stackArg a 3 ∧
    stackArg (t.callEntry.withRegions (pubRd s) (pubWr s)) 3 = stackArg a 4 ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pubRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pubRd s) (pubWr s)).mem
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (pubRd s) (pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, -⟩ := h
  have hp := preR_of S.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rcx) (by decide),
      S.gpr (r := .rdx) (by decide), S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide) (by decide)]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.gpr (r := .rcx) (by decide)]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide) (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide) (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [entryBytes he _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), S.n]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [entryBytes he _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega), S.e]

theorem call_ct (v : PubImpl) : RelCT isa (Two (At J1)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pubChk) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := pub_covers (preR_of S₁.1) j₁.2.2.2.2.2.2.2.2.2.2.2 j₁.1
  obtain ⟨c₂, w₂⟩ := pub_covers (preR_of S₂.1) j₂.2.2.2.2.2.2.2.2.2.2.2 j₂.1
  obtain ⟨he₁, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁, hg₁⟩ := j₁
  obtain ⟨he₂, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂, hg₂⟩ := j₂
  have p₁ := pub_pre (preR_of S₁.1) hg₁ he₁.rsp hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ := pub_pre (preR_of S₂.1) hg₂ he₂.rsp hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pubChk.pub (t₁.callEntry.withRegions (pubRd s₁) (pubWr s₁))
      (t₂.callEntry.withRegions (pubRd s₂) (pubWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩
  exact ⟨pubRd s₁, pubWr s₁, pubRd s₂, pubWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## Zeros and the copy to `out` -/

def JZ (s t : State) : Prop := t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi

def JC (s t : State) : Prop := t.gpr .rsi = valA s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rsi

theorem zeroSlots_ct {J : State → State → Prop} (hJ : ∀ s t, J s t → Env s t) :
    RelCT isa (Two (At J)) zeroSlots fun _ _ => True := by
  unfold zeroSlots
  refine RelCT.seq (two_piece [.rsp] (pins_rsp fun s t h => (hJ s t h).rsp) (by taint_decide)
    (Ψ := At JZ) fun _ t ⟨s, S, h⟩ => WP.mono (zeroHead_ok (preR_of S.1) (hJ s t h))
      fun _ ⟨_, _, hdi, hsi⟩ => ⟨s, S, hdi, hsi⟩) (zeroOut_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact pin (fun s => s.gpr .rdi) (fun _ _ h => h.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
  · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂

theorem copyOut_ct {J : State → State → Prop} (hJ : ∀ s t, J s t → Env s t ∧ t.gpr .rcx = s.gpr .rcx) :
    RelCT isa (Two (At J)) copyOut fun _ _ => True := by
  unfold copyOut
  refine RelCT.seq (two_piece [.rsp] (pins_rsp fun s t h => (hJ s t h).1.rsp) (by taint_decide)
    (Ψ := At JC) fun _ t ⟨s, S, h⟩ => WP.mono (copyHead_ok (preR_of S.1) (hJ s t h).1 (hJ s t h).2)
      fun _ ⟨_, _, _, hdi, h9, hsi⟩ => ⟨s, S, hsi, hdi, h9⟩) (copyRest_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact pin valA (fun _ _ h => h.1) (fun _ _ S => S.valA) h₁ h₂
  · exact pin (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
  · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂

/-! ## The pieces -/

theorem lenCheck_two : RelCT isa (Two (At J0)) (.block lenCheck) (Two (At JL)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin (fun s => s.gpr .rsp) (fun s t h => by rw [show t = s from h]) (fun _ _ S => S.gpr (by decide))
        h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      rw [show t = s from ht]
      exact WP.mono (lenCheck_ok (preR_of S.1)) fun _ h => ⟨s, S, h⟩

theorem zeroOut0_ct : RelCT isa (Two fun a t => At JL a t ∧ isa.eval .ne t = some true) zeroOut fun _ _ => True :=
  two_and (zeroOut_taint fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact pin (fun s => s.gpr .rdi) (fun _ _ h => h.1.1.gpr (by decide)) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.1.1.gpr (by decide)) (fun _ _ S => S.gpr (by decide)) h₁ h₂)

theorem pubArgs_two : RelCT isa (Two (At JA)) (.block pubArgs) (Two (At J1)) :=
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
      exact WP.mono (pubArgs_ok (preR_of S.1) hA hm₀)
        fun _ ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, _⟩ =>
          ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩

theorem call_two (v : PubImpl) : RelCT isa (Two (At J1)) (.call v.name v.code) (Two (At J2)) :=
  two_post (call_ct v) fun _ _ ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩ =>
    WP.mono (pub_call v (preR_of S.1) hg he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) fun _ h =>
      ⟨s, S, h.1, h.2.1, hg⟩

theorem test0_two : RelCT isa (Two (At J2)) (.block test0) (Two (At J3)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, he, hw, hg⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ =>
      ⟨s, S, ⟨he.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2, by rw [hs.2.1, hs.1]; exact hw, hg⟩, by
        rw [hz, written_r hw]; cases (pubOut s).isSome <;> rfl⟩

theorem encArgs_two : RelCT isa (Two fun a t => At J3 a t ∧ isa.eval .e t = some false) (.block encArgs)
    (Two (At J4)) :=
  two_and (two_piece [.rsp] (pins_rsp fun _ _ h => h.1.1.1.rsp) (by taint_decide)
    fun _ t ⟨s, S, ⟨⟨he, hw, hg⟩, hz⟩, he'⟩ => by
      have hsome : (pubOut s).isSome = true := by
        simp only [eval, hz, Option.some.injEq, Bool.not_eq_false'] at he'; simpa using he'
      obtain ⟨em, hem⟩ := Option.isSome_iff_exists.mp hsome
      rw [hem] at hw
      refine WP.mono (encArgs_ok (preR_of S.1) he) fun u ⟨hK, hm, h8, hcx, hdx, h9, hsi⟩ =>
        ⟨s, S, he.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, h8, hcx, hdx, h9, hsi, ?_, hg⟩
      rw [hm, hw.2]; simp [emOut, hem])

theorem encode_two : RelCT isa (Two (At J4)) encode (Two (At J5)) :=
  two_piece [.rsp, .r8, .rcx, .rdx, .rsi, .r9] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact pin fb (fun _ _ h => h.1.rsp) (fun _ _ S => S.fb) h₁ h₂
      · exact pin (fun s => off (fb s) oEM2) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
      · exact pin (fun s => ((stackArg s 0).setWidth 32).setWidth 64) (fun _ _ h => h.2.2.2.1)
          (fun _ _ S => by rw [S.h]) h₁ h₂
      · exact pin valA (fun _ _ h => h.2.2.2.2.2.1) (fun _ _ S => S.valA) h₁ h₂
      · exact pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, j⟩ => by
      obtain ⟨he, h8, hcx, hdx, h9, hsi, hem, hg⟩ := j
      have hp := preR_of S.1
      refine WP.mono (encode_ok (encPre hp he h8 hcx hdx h9 hsi)) fun u ⟨hK, hout⟩ =>
        ⟨s, S, t, ⟨he, h8, hcx, hdx, h9, hsi, hem, hg⟩, hK, ?_⟩
      rw [hsi, h9, valBytes hp, hem] at hout
      exact hout

def J5n (s t : State) : Prop := J6 s t ∧ isa.eval .e t = some true
def J5s (s t : State) : Prop := J6 s t ∧ isa.eval .e t = some false

theorem test0_two5 : RelCT isa (Two (At J5)) (.block test0) (Two (At J6)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, j⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ => ⟨s, S, t, j, hs, by
      obtain ⟨t₄, -, -, hout⟩ := j
      rw [hz]
      cases h : encRes s with
      | none => rw [h] at hout; rw [hout.1]; rfl
      | some em' => rw [h] at hout; rw [hout.1]; rfl⟩

theorem J5n_env {s t : State} (h : J5n s t) : Env s t := by
  obtain ⟨⟨t₅, ⟨t₄, j₄, hK, hout⟩, hs, hz⟩, he⟩ := h
  have hn : encRes s = none := by
    simp only [eval, hz, Option.some.injEq, Bool.not_eq_true'] at he
    simpa using he
  rw [hn] at hout
  exact (j₄.1.regs (by rw [hK.gpr (by decide)]) hout.2 hK.2.1 hK.2.2).regs (by rw [hs.1]) hs.2.1 hs.2.2.1
    hs.2.2.2

theorem cmpArgs_two : RelCT isa (Two (At J5s)) (.block cmpArgs) (Two (At J7)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pin fb (fun s t h => by
        obtain ⟨⟨t₅, ⟨t₄, j₄, hK, _⟩, hs, _⟩, _⟩ := h
        rw [hs.1, hK.gpr (by decide)]; exact j₄.1.rsp) (fun _ _ S => S.fb) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ⟨t₅, ⟨t₄, j₄, hK, hout⟩, hs, hz⟩, he⟩ => by
      have hp := preR_of S.1
      have hsome : (encRes s).isSome = true := by
        simp only [eval, hz, Option.some.injEq, Bool.not_eq_false'] at he; simpa using he
      obtain ⟨em', hem'⟩ := Option.isSome_iff_exists.mp hsome
      rw [hem'] at hout
      obtain ⟨he₄, h8₄, hcx₄, -, -, -, hem₄, hg₄⟩ := j₄
      obtain ⟨he₅, -, h2, hkeep⟩ := encDone hp he₄ hK h8₄ (encodeId_length hem') hout
      have h1 : Spec.Rsa.bytesAt t₅.mem (off (fb s) oEM1) (s.gpr .rcx).toNat = emOut s := by
        rw [hkeep (EM12_disjoint hp) (by have := hp.k2; omega), hem₄]
      have he₆ : Env s t := he₅.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2
      refine WP.mono (cmpArgs_ok he₆) fun u ⟨hK', hm, hdi, hsi⟩ =>
        ⟨s, S, he₆.regs (hK'.gpr (by decide)) hm hK'.2.1 hK'.2.2, hdi, hsi, ?_, ?_, ?_, hg₄⟩
      · rw [hK'.gpr (by decide), hs.1, hK.gpr (by decide), hcx₄]
      · rw [hm, hs.2.1, h1]
      · rw [hm, hs.2.1, h2]; simp [encVal, hem']

theorem compare_two : RelCT isa (Two (At J7)) compare (Two (At J8)) :=
  two_piece [.rdi, .rsi, .rcx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact pin (fun s => off (fb s) oEM1) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact pin (fun s => off (fb s) oEM2) (fun _ _ h => h.2.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, he, hdi, hsi, hcx, h1, h2, hg⟩ => by
      have hp := preR_of S.1
      have hk1 := hp.k1
      have hk2 := hp.k2
      have hr : ∀ i < (s.gpr .rcx).toNat, InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
          InRegions (t.rd ++ t.wr) (t.gpr .rsi + BitVec.ofNat 64 i) 1 := fun i hi => by
        rw [hdi, hsi, he.wr]
        obtain ⟨r₁, h₁, c₁⟩ := frame_bytes' hp (d := oEM1) (n := (s.gpr .rcx).toNat)
          (by unfold oEM1 frameBytes; omega) i hi
        obtain ⟨r₂, h₂, c₂⟩ := frame_bytes' hp (d := oEM2) (n := (s.gpr .rcx).toNat)
          (by unfold oEM2 frameBytes; omega) i hi
        exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
      refine WP.mono (compare_ok (by rw [hcx]) (by omega) hr) fun u ⟨hK, hm, hdx⟩ =>
        ⟨s, S, he.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, by rw [hK.gpr (by decide), hcx], ?_, hg⟩
      rw [hdx, hdi, hsi, Ver.setWidth_byte_eq_zero, VG.Proof.Ct.diff_zero, ← Ver.bytesAt_eq_iff, h1, h2]

theorem test_two : RelCT isa (Two (At J8)) (.block [.alu .test .rdx (.reg .rdx)]) (Two (At J9)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, he, hcx, hd, hg⟩ => WP.mono (test_ok t) fun u ⟨hs, hz⟩ => by
      refine ⟨s, S, he.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2, by rw [hs.1]; exact hcx, ?_, hg⟩
      rw [hz]
      by_cases h : emOut s = encVal s
      · rw [decide_eq_true h, show t.gpr .rdx = 0 from hd.2 h]; rfl
      · rw [decide_eq_false h, show (t.gpr .rdx == 0) = false from beq_eq_false_iff_ne.mpr (fun h' => h (hd.1 h'))]

/-! ## The composition -/

theorem release_ct : RelCT isa (Two (At J8)) release fun _ _ => True := by
  unfold release
  refine RelCT.seq test_two (two_ite ?_ (two_and (zeroSlots_ct fun _ _ h => h.1.1))
    (two_and (copyOut_ct fun _ _ h => ⟨h.1.1, h.1.2.1⟩)))
  refine pinEval (fun s => if stackArg s 2 = s.gpr .rcx then some (!decide (emOut s = encVal s)) else none)
    (fun s t h => by simp only [eval, h.2.2.1, h.2.2.2, Option.map_some, ↓reduceIte]) ?_
  intro a s S
  have he : (stackArg s 2 = s.gpr .rcx) = (stackArg a 2 = a.gpr .rcx) := by
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  by_cases hs : stackArg s 2 = s.gpr .rcx
  · have ha : stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte, emOut_sib S hs, encVal_sib S hs]
  · have ha : ¬ stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte]

theorem J6_sig {s t : State} (h : J6 s t) : stackArg s 2 = s.gpr .rcx := by
  obtain ⟨_, ⟨_, j₄, _, _⟩, _, _⟩ := h
  exact j₄.2.2.2.2.2.2.2

theorem tail_ct : RelCT isa (Two (At J5)) tail fun _ _ => True := by
  unfold tail
  refine RelCT.seq test0_two5 (two_ite ?_ (two_and (zeroSlots_ct fun _ _ h => J5n_env h))
    (two_and (RelCT.seq cmpArgs_two (RelCT.seq compare_two release_ct))))
  refine pinEval (fun s => if stackArg s 2 = s.gpr .rcx then some (!(encRes s).isSome) else none)
    (fun s t h => by
      have hg := J6_sig h
      obtain ⟨_, _, _, hz⟩ := h
      simp only [eval, hz, hg, ↓reduceIte]) ?_
  intro a s S
  have he : (stackArg s 2 = s.gpr .rcx) = (stackArg a 2 = a.gpr .rcx) := by
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  by_cases hs : stackArg s 2 = s.gpr .rcx
  · have ha : stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte, encRes_sib S hs]
  · have ha : ¬ stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte]

theorem afterPub_ct : RelCT isa (Two (At J2)) afterPub fun _ _ => True := by
  unfold afterPub
  refine RelCT.seq test0_two (two_ite ?_ (two_and (zeroSlots_ct fun _ _ h => h.1.1.1))
    (RelCT.seq encArgs_two (RelCT.seq encode_two tail_ct)))
  refine pinEval (fun s => if stackArg s 2 = s.gpr .rcx then some (!(pubOut s).isSome) else none)
    (fun s t h => by simp only [eval, h.2, h.1.2.2, ↓reduceIte]) ?_
  intro a s S
  have he : (stackArg s 2 = s.gpr .rcx) = (stackArg a 2 = a.gpr .rcx) := by
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  by_cases hs : stackArg s 2 = s.gpr .rcx
  · have ha : stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte, pubOut_sib S hs]
  · have ha : ¬ stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte]

theorem body_ct (v : PubImpl) : RelCT isa (Two (At JA)) (body v.name v.code) fun _ _ => True :=
  RelCT.seq pubArgs_two (RelCT.seq (call_two v) afterPub_ct)

theorem code_ct (v : PubImpl) : RelCT isa (Two (At J0)) (code v.name v.code) fun _ _ => True := by
  unfold code
  refine RelCT.seq lenCheck_two (two_ite ?_ zeroOut0_ct (relCT_alloc ((body_ct v).mono ?_ fun _ _ h => h)))
  · refine pinEval (fun s => some (!(stackArg s 2 == s.gpr .rcx))) (fun s t h => by
      simp only [eval, h.2.2, Option.map_some]) ?_
    intro a s S
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  · rintro _ _ ⟨t₁, t₂, ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩, rfl, rfl⟩
    have hg : ∀ {s t}, JL s t → isa.eval .ne t = some false → stackArg s 2 = s.gpr .rcx := fun j e => by
      simp only [eval, j.2.2, Option.map_some, Option.some.injEq, Bool.not_eq_false', beq_iff_eq] at e
      exact e
    exact ⟨a, ⟨s₁, S₁, t₁, j₁, hg j₁ e₁, rfl⟩, ⟨s₂, S₂, t₂, j₂, hg j₂ e₂, rfl⟩⟩

theorem code_constantTime (v : PubImpl) :
    ConstantTime isa recContract.pre recContract.pub (code v.name v.code) :=
  RelCT.constantTime ((code_ct v).mono
    (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩) fun _ _ h => h)

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_recover`, calling the implementation `v` of
`vg_rsa_public_checked`, meets the shared contract. -/
theorem code_verified (v : PubImpl) :
    Verified target (code v.name v.code) (Spec.RsaPkcs1Sig.recoverContract abi verStack) :=
  have hct : ConstantTime isa recContract.pre recContract.pub (code v.name v.code) := code_constantTime v
  Verified.of_correct (k := recContract) (code_correct v) hct recover_implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PubImpl) : (code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [code, body, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Sig.X86_64.Rec
