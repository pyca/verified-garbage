module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcCorrect
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivPcCorrect
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: constant time

`vg_rsa_private_checked`'s argument (`PrivCT.lean`), for this function's
frame: two runs from entry states that agree on the public data
(`chkPcContract.pub`, with `n`'s values, the first words of `pre`) leak the
same trace (`bodyP_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivCheckedPc
open VG.Impl.Rsa.X86_64.PrivChecked (sp lea oM cmpLoop masks releaseLoop)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting the precondition with the anchor's public data. -/
def SibP (a s : State) : Prop := chkPcContract.pre s ∧ chkPcContract.pub a s

theorem pubP_refl (s : State) : chkPcContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem SibP.gpr {a s : State} (h : SibP a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem SibP.arg {a s : State} (h : SibP a s) {i : Nat} (hi : i < 16) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.2.1) i (List.mem_range.mpr hi)).symm

theorem SibP.n {a s : State} (h : SibP a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.2.2.1.symm

theorem SibP.e {a s : State} (h : SibP a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.2.2.2.2.1.symm

theorem SibP.leak {a s : State} (h : SibP a s) :
    Spec.Rsa.privatePreLeak s.mem (stackArg s 14) (s.gpr .rcx).toNat =
      Spec.Rsa.privatePreLeak a.mem (stackArg a 14) (a.gpr .rcx).toNat :=
  h.2.2.2.2.2.symm

/-- `n`'s values, the words of `pre` that are public. -/
theorem SibP.pre {a s : State} (h : SibP a s) :
    Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
      Spec.Rsa.wordsAt a.mem (stackArg a 14) (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat) :=
  (List.map_inj_right fun _ _ e => BitVec.eq_of_toNat_eq e).mp h.leak

theorem SibP.fb {a s : State} (h : SibP a s) : fbP s = fbP a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

/-- A point of a run, described by `J` from the run's entry state. -/
def AtP (J : State → State → Prop) (a t : State) : Prop := ∃ s, SibP a s ∧ J s t

/-- A register `J` gives as a function of the public data. -/
theorem pinP {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, SibP a s → f s = f a) {a t₁ t₂ : State} (h₁ : AtP J a t₁) (h₂ : AtP J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

/-- In the frame, `rsp` is public. -/
theorem pinsP_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → EnvP s t) : Pins (AtP J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pinP fbP (fun s t h => (hJ s t h).rsp) (fun _ _ h => h.fb) h₁ h₂

/-- What a callee sees in memory: the caller's, but for its return address. -/
theorem EnvP.entryFrame {s t : State} (he : EnvP s t) : Frame [stkRP s, outR s, scrR s] s.mem t.callEntry.mem :=
  frameP_call he.mem (callEntryP_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (belowP_sub s)

/-- `n`'s values in `pre`, as a callee sees them. -/
theorem EnvP.entryPre {s t : State} (hp : PreFPc s) (he : EnvP s t) (rd wr : List Region) :
    Spec.Rsa.wordsAt (t.callEntry.withRegions rd wr).mem (stackArg s 14)
        (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
      Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
  have sP := preRP_sub hp
  have hprl := hp.hprl
  have wPre := hp.wPre
  unfold Spec.Rsa.privatePrecomputedWords at hprl
  rw [State.withRegions_mem]
  exact wordsP_of_frame he.entryFrame (hp.dKpre.symm.sub_left sP).symm (hp.dOpre.symm.sub_left sP).symm
    (hp.dpres.sub_left sP).symm (by simp only [preRP] at sP ⊢; omega)

/-! ## The points of the code -/

def J0P (s t : State) : Prop := t = allocState frameBytes s

def J1P (s t : State) : Prop :=
  EnvP s t ∧ (∀ i < 14, word t.mem (fbP s) (8 * i) = stackArg s (i + 2)) ∧ t.gpr .rdi = off (fbP s) oM ∧
    t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧
    t.gpr .r9 = s.gpr .rcx

def J2P (s t : State) : Prop := EnvP s t

def J5P (s t : State) : Prop :=
  EnvP s t ∧ word t.mem (fbP s) 0 = off (fbP s) oM ∧ word t.mem (fbP s) 8 = s.gpr .rcx ∧
    word t.mem (fbP s) 16 = stackArg s 12 ∧ word t.mem (fbP s) 24 = stackArg s 13 ∧
    t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = stackArg s 14 ∧
    t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
    t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

def J7P (s t : State) : Prop :=
  t.gpr .rsp = fbP s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = stackArg s 0 ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .r10 = BitVec.ofNat 64 0

/-! ## The calls -/

/-- What the CRT's contract makes public, from the entry state. -/
theorem crtP_view {a s t : State} (S : SibP a s) (h : J1P s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)).gpr =
      [off (fbP a) oM, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, stackArg a 0, a.gpr .rcx, fbP a - 8] ∧
    (∀ i < 14, stackArg (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)) i = stackArg a (i + 2)) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)).mem
      ((t.callEntry.withRegions (crtPcRd s) (crtPcWr s)).gpr .rdx)
      ((t.callEntry.withRegions (crtPcRd s) (crtPcWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat ∧
    Spec.Rsa.privatePreLeak (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)).mem
      (stackArg (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)) 12)
      ((t.callEntry.withRegions (crtPcRd s) (crtPcWr s)).gpr .rcx).toNat =
      Spec.Rsa.privatePreLeak a.mem (stackArg a 14) (a.gpr .rcx).toNat := by
  obtain ⟨he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := preFPc_of S.1
  have hE : ∀ i < 14, stackArg (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)) i = stackArg s (i + 2) :=
    fun i hi => (stackArgP_entry he.rsp _ _ (by omega)).trans (hargs i hi)
  have hcx' : (t.callEntry.withRegions (crtPcRd s) (crtPcWr s)).gpr .rcx = s.gpr .rcx := by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hcx]
  refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rcx) (by decide),
      S.gpr (r := .rdx) (by decide), S.arg (by decide)]
  · rw [hE i hi, S.arg (by omega)]
  · simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [bytesP_of_frame he.entryFrame hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), S.n]
  · rw [hE 12 (by decide), hcx']
    simp only [Spec.Rsa.privatePreLeak]
    rw [he.entryPre hp]
    exact S.leak

theorem crtP_ct (v : CrtImpl) : RelCT isa (Two (AtP J1P)) (.call v.pcrtName v.pcrt) fun _ _ => True := by
  refine RelCT.callEx (k := crtPcContract.clear) v.pcrtOk v.pcrtCt fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, g₁, n₁, l₁⟩ := crtP_view S₁ j₁
  obtain ⟨r₂, g₂, n₂, l₂⟩ := crtP_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := crtPc_covers (preFPc_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := crtPc_covers (preFPc_of S₂.1) j₂.1
  obtain ⟨he₁, hargs₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hargs₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  have p₁ : crtPcContract.clear.pre ((t₁.callEntry).withRegions (crtPcRd s₁) (crtPcWr s₁)) :=
    ⟨crtPc_pre (preFPc_of S₁.1) he₁ hargs₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁, crtPc_clear (preFPc_of S₁.1) he₁⟩
  have p₂ : crtPcContract.clear.pre ((t₂.callEntry).withRegions (crtPcRd s₂) (crtPcWr s₂)) :=
    ⟨crtPc_pre (preFPc_of S₂.1) he₂ hargs₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂, crtPc_clear (preFPc_of S₂.1) he₂⟩
  have ga : ∀ i < 14, stackArg ((t₁.callEntry).withRegions (crtPcRd s₁) (crtPcWr s₁)) i =
      stackArg ((t₂.callEntry).withRegions (crtPcRd s₂) (crtPcWr s₂)) i := fun i hi => (g₁ i hi).trans (g₂ i hi).symm
  have hpub : crtPcContract.pub ((t₁.callEntry).withRegions (crtPcRd s₁) (crtPcWr s₁))
      ((t₂.callEntry).withRegions (crtPcRd s₂) (crtPcWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), ga 0 (by decide), ga 1 (by decide), ga 2 (by decide), ga 3 (by decide),
      ga 4 (by decide), ga 5 (by decide), ga 6 (by decide), ga 7 (by decide), ga 8 (by decide), ga 9 (by decide),
      ga 10 (by decide), ga 11 (by decide), ga 12 (by decide), ga 13 (by decide), n₁.trans n₂.symm,
      l₁.trans l₂.symm⟩
  exact ⟨crtPcRd s₁, crtPcWr s₁, crtPcRd s₂, crtPcWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-- What `vg_rsa_public_precomputed_checked`'s contract makes public. -/
theorem pdP_view {a s t : State} (S : SibP a s) (h : J5P s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (pdRdP s) (pdWrP s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, stackArg a 14, BitVec.ofNat 64 (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat),
        a.gpr .r8, a.gpr .r9, fbP a - 8] ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWrP s)) 0 = off (fbP a) oM ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWrP s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWrP s)) 2 = stackArg a 12 ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWrP s)) 3 = stackArg a 13 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (pdRdP s) (pdWrP s)).mem
      ((t.callEntry.withRegions (pdRdP s) (pdWrP s)).gpr .rdx)
      ((t.callEntry.withRegions (pdRdP s) (pdWrP s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 14) (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pdRdP s) (pdWrP s)).mem
      ((t.callEntry.withRegions (pdRdP s) (pdWrP s)).gpr .r8)
      ((t.callEntry.withRegions (pdRdP s) (pdWrP s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := preFPc_of S.1
  have hk2 := hp.k2
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by
      unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega)
  have rcx := S.gpr (r := .rcx) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, rcx, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide), S.arg (by decide)]
  · rw [stackArgP_entry he.rsp _ _ (by decide), ← S.fb]; exact hw0
  · rw [stackArgP_entry he.rsp _ _ (by decide), ← rcx]; exact hw1
  · rw [stackArgP_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw2
  · rw [stackArgP_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx, hcxN]
    rw [he.entryPre hp, S.pre]
  · simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [bytesP_of_frame he.entryFrame hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega), S.e]

theorem pdP_ct (P : PublicImpl) (name : String) :
    RelCT isa (Two (AtP J5P)) (.call name (P.code)) fun _ _ => True := by
  have hct : ConstantTime isa (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pub (P.code) :=
    P.ct
  refine RelCT.callEx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩)
    P.ok hct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, w₁', e₁⟩ := pdP_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, w₂', e₂⟩ := pdP_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := pdP_covers (preFPc_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := pdP_covers (preFPc_of S₂.1) j₂.1
  obtain ⟨he₁, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  have p₁ : pdContract.pre (t₁.callEntry.withRegions (pdRdP s₁) (pdWrP s₁)) :=
    pdP_pre (preFPc_of S₁.1) he₁ hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ : pdContract.pre (t₂.callEntry.withRegions (pdRdP s₂) (pdWrP s₂)) :=
    pdP_pre (preFPc_of S₂.1) he₂ hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pdContract.pub (t₁.callEntry.withRegions (pdRdP s₁) (pdWrP s₁))
      (t₂.callEntry.withRegions (pdRdP s₂) (pdWrP s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, w₁'.trans w₂'.symm, e₁.trans e₂.symm⟩
  exact ⟨pdRdP s₁, pdWrP s₁, pdRdP s₂, pdWrP s₂, p₁, p₂, hpub, Covers.append_left c₁ w₁.right, w₁,
    Covers.append_left c₂ w₂.right, w₂, by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## The pieces -/

theorem crtArgsP_two : RelCT isa (Two (AtP J0P)) (.block crtArgs) (Two (AtP J1P)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pinP fbP (fun s t h => by rw [h]; rfl) (fun _ _ h => h.fb) h₁ h₂) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      subst ht
      exact WP.mono (crtArgsP_ok (preFPc_of S.1)) fun _ ⟨he, _, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ =>
        ⟨s, S, he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩

theorem crtCallP_two (v : CrtImpl) : RelCT isa (Two (AtP J1P)) (.call v.pcrtName v.pcrt) (Two (AtP J2P)) :=
  two_post (crtP_ct v) fun _ _ ⟨s, S, he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (crtPc_call v (preFPc_of S.1) he hargs hdi hsi hdx hcx h8 h9) fun _ h => ⟨s, S, h.1⟩

theorem pdArgsP_two : RelCT isa (Two (AtP J2P)) (.block pdArgs) (Two (AtP J5P)) :=
  two_piece [.rsp] (pinsP_rsp fun _ _ h => h) (by taint_decide)
    fun _ t ⟨s, S, he⟩ => by
      have hp := preFPc_of S.1
      refine WP.mono (pdArgsP_ok hp he) fun t₃ ⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩ => ?_
      have hw : ∀ {d : Nat}, d < 4 → word t₃.mem (fbP s) (8 * d) =
          [off (fbP s) oM, s.gpr .rcx, stackArg s 12, stackArg s 13].getD d 0 := fun {d} hd => by
        rw [hm₃]
        rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl | rfl
        · simp (disch := decide) only [word_wo, word_self0, Nat.mul_zero]
          rfl
        · simp (disch := decide) only [word_wo, word_writeW_self, Nat.mul_one]; rfl
        · simp (disch := decide) only [word_wo, word_writeW_self]; rfl
        · simp (disch := decide) only [word_writeW_self]; rfl
      exact ⟨s, S, he₃, hw (d := 0) (by decide), hw (d := 1) (by decide),
        hw (d := 2) (by decide), hw (d := 3) (by decide), hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩

theorem pdCallP_two (P : PublicImpl) (name : String) :
    RelCT isa (Two (AtP J5P)) (.call name (P.code)) (Two (AtP J2P)) :=
  two_post (pdP_ct P name) fun _ _ ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (pdP_call P name (preFPc_of S.1) he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) fun _ h => ⟨s, S, h.1⟩

theorem cmpArgsP_two : RelCT isa (Two (AtP J2P)) (.block cmpArgs) (Two (AtP J7P)) :=
  two_piece [.rsp] (pinsP_rsp fun _ _ h => h) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (cmpArgsP_ok (preFPc_of S.1) he) fun _ ⟨_, _, hdi, hsi, hcx, h10, _, k⟩ =>
      ⟨s, S, (k.gpr (by decide)).trans he.rsp, hdi, hsi, hcx, h10⟩

theorem tailP_eq : seqs PrivCheckedPc.tail =
    .seq (.block cmpArgs) (.seq cmpLoop (.seq (.block masks) (.seq releaseLoop (.block [.mov .rax (.reg .r11)])))) :=
  rfl

/-- The comparison and the release, from the registers `cmpArgs` sets. -/
theorem restP_ct : RelCT isa (Two (AtP J7P))
    (.seq cmpLoop (.seq (.block masks) (.seq releaseLoop (.block [.mov .rax (.reg .r11)])))) fun _ _ => True :=
  two_taint [.rdi, .rsi, .rcx, .r10, .rsp] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact pinP (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pinP (fun s => stackArg s 0) (fun _ _ h => h.2.2.1) (fun _ _ S => S.arg (by decide)) h₁ h₂
    · exact pinP (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pinP (fun _ => BitVec.ofNat 64 0) (fun _ _ h => h.2.2.2.2) (fun _ _ _ => rfl) h₁ h₂
    · exact pinP fbP (fun _ _ h => h.1) (fun _ _ S => S.fb) h₁ h₂) (by taint_decide)

theorem bodyP_ct (v : CrtImpl) (pdName : String) :
    RelCT isa (Two (AtP J0P)) (PrivCheckedPc.body v.pcrtName v.pcrt pdName (v.pubOp.code)) fun _ _ => True := by
  rw [bodyP_eq, checkP_eq, tailP_eq]
  exact RelCT.seq crtArgsP_two (RelCT.seq (crtCallP_two v) (RelCT.seq pdArgsP_two
    (RelCT.seq (pdCallP_two v.pubOp pdName) (RelCT.seq cmpArgsP_two restP_ct))))

/-! ## The frame -/

theorem allocP_push {s s₁ : State} (h : isa.push (.alloc frameBytes) s = some s₁) : s₁ = allocState frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame of `frameBytes` bytes leaks what its body does. -/
theorem relCT_allocP {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState frameBytes s₁ ∧ b = allocState frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc frameBytes) body (.free frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := allocP_push p₁
      obtain rfl := allocP_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

theorem codeP_constantTime (v : CrtImpl) (pdName : String) :
    ConstantTime isa chkPcContract.pre chkPcContract.pub
      (PrivCheckedPc.code v.pcrtName v.pcrt pdName (v.pubOp.code)) :=
  RelCT.constantTime (relCT_allocP ((bodyP_ct v pdName).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pubP_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

/-! ## `Verified` -/

/-- `vg_rsa_private_checked_precomputed`, calling the implementation `v` of
the CRT with precomputed values and its independently verified public
operation, meets the shared contract. -/
theorem codeP_verified (v : CrtImpl) (pdName : String) :
    Verified target (PrivCheckedPc.code v.pcrtName v.pcrt pdName (v.pubOp.code))
      (Spec.Rsa.privateCheckedPrecomputedContract abi stackBytesPc) :=
  have hct : ConstantTime isa chkPcContract.pre chkPcContract.pub
      (PrivCheckedPc.code v.pcrtName v.pcrt pdName (v.pubOp.code)) := codeP_constantTime v pdName
  Verified.of_correct (k := chkPcContract) (codeP_correct v pdName) hct private_checked_pc_implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem codeP_spSafe (v : CrtImpl) (pdName : String) :
    (PrivCheckedPc.code v.pcrtName v.pcrt pdName (v.pubOp.code)).all (fun i => !isa.writesSp i) = true := by
  simp only [PrivCheckedPc.code, PrivCheckedPc.body, PrivCheckedPc.tail, List.cons_append, List.nil_append, seqs,
    Code.all, v.pcrtSpSafe, v.pubOp.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.Rsa.X86_64
