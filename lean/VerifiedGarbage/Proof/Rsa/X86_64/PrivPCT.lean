module

public import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCorrect
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivPCorrect
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCorrect
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivCheck
meta import VerifiedGarbage.Proof.Rsa.X86_64.PrivTail
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_rsa_private_checked_precomputed` on x86-64: constant time

As `vg_rsa_private_checked` (`PrivCT.lean`), from entry states that agree on
`chkContractP.pub` (`SibP`): its public data, `pre`'s address and length,
and the modulus' values in `pre`, which the CRT given `pre` and
`vg_rsa_public_precomputed_checked` both take as public (`codeP_constantTime`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## Entry states and the anchor -/

/-- An entry state meeting `chkContractP`'s precondition with the anchor's
public data. -/
def SibP (a s : State) : Prop := chkContractP.pre s ∧ chkContractP.pub a s

theorem pubP_refl (s : State) : chkContractP.pub s s := ⟨pub_refl s, rfl, rfl, rfl⟩

theorem SibP.gpr {a s : State} (h : SibP a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1.1 r hr).symm

theorem SibP.arg {a s : State} (h : SibP a s) {i : Nat} (hi : i < 14) : stackArg s i = stackArg a i :=
  ((List.map_inj_left.mp h.2.1.2.1) i (List.mem_range.mpr hi)).symm

theorem SibP.n {a s : State} (h : SibP a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.1.2.2.1.symm

theorem SibP.e {a s : State} (h : SibP a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.2.1.2.2.2.symm

theorem SibP.fb {a s : State} (h : SibP a s) : fb s = fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

theorem SibP.pre {a s : State} (h : SibP a s) :
    Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
      Spec.Rsa.wordsAt a.mem (stackArg a 14) (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat) := by
  have hl := h.2.2.2.2
  simp only [Spec.Rsa.privatePrecomputedLeak] at hl
  exact ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl).symm

/-- A point of a run, described by `J` from the run's entry state. -/
def AtP (J : State → State → Prop) (a t : State) : Prop := ∃ s, SibP a s ∧ J s t

theorem pinP {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, SibP a s → f s = f a) {a t₁ t₂ : State} (h₁ : AtP J a t₁) (h₂ : AtP J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pinsP_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → Env s t) : Pins (AtP J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact pinP fb (fun s t h => (hJ s t h).rsp) (fun _ _ h => h.fb) h₁ h₂

/-! ## The points of the code -/

def J1P (s t : State) : Prop :=
  J1 s t ∧ word t.mem (fb s) 96 = stackArg s 14 ∧ word t.mem (fb s) 104 = stackArg s 15

def J5P (s t : State) : Prop :=
  Env s t ∧ word t.mem (fb s) 0 = off (fb s) oM ∧ word t.mem (fb s) 8 = s.gpr .rcx ∧
    word t.mem (fb s) 16 = stackArg s 12 ∧ word t.mem (fb s) 24 = stackArg s 13 ∧
    t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = stackArg s 14 ∧
    t.gpr .rcx = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) ∧
    t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

/-! ## The calls -/

/-- `pre`'s words at a callee's entry, from the caller's entry state. -/
theorem Env.entryWordsP {s t : State} (he : Env s t) (hf : PFacts s) (rd wr : List Region) :
    Spec.Rsa.wordsAt (t.callEntry.withRegions rd wr).mem (stackArg s 14)
      (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) =
    Spec.Rsa.wordsAt s.mem (stackArg s 14) (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat) := by
  have sP := preRp_sub hf
  have hl := hf.wPr
  have hpl := hf.hpl
  rw [State.withRegions_mem]
  exact words_of_frame (entry_frame he) (hf.dKp.symm.sub_left sP).symm (hf.dOp.symm.sub_left sP).symm
    (hf.dSp.symm.sub_left sP).symm (by unfold Spec.Rsa.privatePrecomputedWords at hpl; omega_arith)

/-- What the CRT given `pre`'s contract makes public, from the entry state. -/
theorem crtP_view {a s t : State} (S : SibP a s) (h : J1P s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr =
      [off (fb a) oM, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, stackArg a 0, a.gpr .rcx, fb a - 8] ∧
    (∀ i < 12, stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) i = stackArg a (i + 2)) ∧
    stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 12 = stackArg a 14 ∧
    stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 13 = stackArg a 15 ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (crtRdP s) (crtWr s)).mem
      ((t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr .rdx)
      ((t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat ∧
    Spec.Rsa.privatePrecomputedLeak (t.callEntry.withRegions (crtRdP s) (crtWr s)).mem
      (stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 12)
      ((t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr .rcx).toNat =
      Spec.Rsa.privatePrecomputedLeak a.mem (stackArg a 14) (a.gpr .rcx).toNat := by
  obtain ⟨⟨he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩, h96, h104⟩ := h
  obtain ⟨hp, hf⟩ := preFP_of S.1
  have e12 : stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 12 = stackArg s 14 :=
    (stackArg_entry he.rsp _ _ (by omega_using [])).trans h96
  have e13 : stackArg (t.callEntry.withRegions (crtRdP s) (crtWr s)) 13 = stackArg s 15 :=
    (stackArg_entry he.rsp _ _ (by omega_using [])).trans h104
  have rcx : (t.callEntry.withRegions (crtRdP s) (crtWr s)).gpr .rcx = s.gpr .rcx := by
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hcx]
  refine ⟨?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rcx) (by decide),
      S.gpr (r := .rdx) (by decide), S.arg (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by omega_using [hi]), hargs i hi, S.arg (by omega_using [hi])]
  · rw [e12]; exact S.2.2.1.symm
  · rw [e13]; exact S.2.2.2.1.symm
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [he.entryBytes _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega_using []), S.n]
  · simp only [Spec.Rsa.privatePrecomputedLeak, rcx, e12]
    rw [he.entryWordsP hf, S.pre]

theorem crtP_ct (v : CrtImpl) : RelCT isa (Two (AtP J1P)) (.call v.nameP v.codeP) fun _ _ => True := by
  refine RelCT.callEx (k := crtContractP.clear) v.okP v.ctP fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, g₁, a12₁, a13₁, n₁, l₁⟩ := crtP_view S₁ j₁
  obtain ⟨r₂, g₂, a12₂, a13₂, n₂, l₂⟩ := crtP_view S₂ j₂
  obtain ⟨hp₁, hf₁⟩ := preFP_of S₁.1
  obtain ⟨hp₂, hf₂⟩ := preFP_of S₂.1
  obtain ⟨c₁, w₁⟩ := crtP_covers hp₁ j₁.1.1
  obtain ⟨c₂, w₂⟩ := crtP_covers hp₂ j₂.1.1
  obtain ⟨⟨he₁, hargs₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩, h96₁, h104₁⟩ := j₁
  obtain ⟨⟨he₂, hargs₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩, h96₂, h104₂⟩ := j₂
  have p₁ : crtContractP.clear.pre ((t₁.callEntry).withRegions (crtRdP s₁) (crtWr s₁)) :=
    ⟨crtP_pre hp₁ hf₁ he₁ hargs₁ h96₁ h104₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁, crtP_clear hp₁ hf₁ he₁⟩
  have p₂ : crtContractP.clear.pre ((t₂.callEntry).withRegions (crtRdP s₂) (crtWr s₂)) :=
    ⟨crtP_pre hp₂ hf₂ he₂ hargs₂ h96₂ h104₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂, crtP_clear hp₂ hf₂ he₂⟩
  have ga : ∀ i < 12, stackArg ((t₁.callEntry).withRegions (crtRdP s₁) (crtWr s₁)) i =
      stackArg ((t₂.callEntry).withRegions (crtRdP s₂) (crtWr s₂)) i := fun i hi => (g₁ i hi).trans (g₂ i hi).symm
  have hpub : crtContractP.pub ((t₁.callEntry).withRegions (crtRdP s₁) (crtWr s₁))
      ((t₂.callEntry).withRegions (crtRdP s₂) (crtWr s₂)) :=
    ⟨⟨regs_eq (r₁.trans r₂.symm), ga 0 (by decide), ga 1 (by decide), ga 2 (by decide), ga 3 (by decide),
      ga 4 (by decide), ga 5 (by decide), ga 6 (by decide), ga 7 (by decide), ga 8 (by decide), ga 9 (by decide),
      ga 10 (by decide), ga 11 (by decide), n₁.trans n₂.symm⟩, a12₁.trans a12₂.symm, a13₁.trans a13₂.symm,
      l₁.trans l₂.symm⟩
  exact ⟨crtRdP s₁, crtWr s₁, crtRdP s₂, crtWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-- What `vg_rsa_public_precomputed_checked`'s contract makes public, given
`pre`. -/
theorem pdP_view {a s t : State} (S : SibP a s) (h : J5P s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr =
      [a.gpr .rdi, a.gpr .rcx, stackArg a 14, BitVec.ofNat 64 (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat),
        a.gpr .r8, a.gpr .r9, fb a - 8] ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) 0 = off (fb a) oM ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) 2 = stackArg a 12 ∧
    stackArg (t.callEntry.withRegions (pdRdP s) (pdWr s)) 3 = stackArg a 13 ∧
    Spec.Rsa.wordsAt (t.callEntry.withRegions (pdRdP s) (pdWr s)).mem
      ((t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr .rdx)
      ((t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr .rcx).toNat =
      Spec.Rsa.wordsAt a.mem (stackArg a 14) (Spec.Rsa.precomputedWords (a.gpr .rcx).toNat) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (pdRdP s) (pdWr s)).mem
      ((t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr .r8)
      ((t.callEntry.withRegions (pdRdP s) (pdWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  obtain ⟨hp, hf⟩ := preFP_of S.1
  have hk2 := hp.k2
  have hpwl := preWords_le hp
  have hcxN : (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .rcx).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .rcx).toNat := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hpwl])
  have rcx := S.gpr (r := .rcx) (by decide)
  have a14 : stackArg s 14 = stackArg a 14 := S.2.2.1.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, rcx, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide), a14]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.fb]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← rcx]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx, hcxN]
    rw [he.entryWordsP hf, S.pre]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [he.entryBytes _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega_using []), S.e]

theorem pdP_ct (P : PublicImpl) (name : String) :
    RelCT isa (Two (AtP J5P)) (.call name (P.code)) fun _ _ => True := by
  have hct : ConstantTime isa (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pre
      (⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩ : Contract isa).pub (P.code) :=
    P.ct
  refine RelCT.callEx (k := ⟨pdContract.pre, pdChkContract.post, pdContract.pub⟩)
    P.ok hct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, w₁', e₁⟩ := pdP_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, w₂', e₂⟩ := pdP_view S₂ j₂
  obtain ⟨hp₁, hf₁⟩ := preFP_of S₁.1
  obtain ⟨hp₂, hf₂⟩ := preFP_of S₂.1
  obtain ⟨c₁, w₁⟩ := pdP_covers hp₁ hf₁ j₁.1
  obtain ⟨c₂, w₂⟩ := pdP_covers hp₂ hf₂ j₂.1
  obtain ⟨he₁, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  have p₁ : pdContract.pre (t₁.callEntry.withRegions (pdRdP s₁) (pdWr s₁)) :=
    pdP_pre hp₁ hf₁ he₁ hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ : pdContract.pre (t₂.callEntry.withRegions (pdRdP s₂) (pdWr s₂)) :=
    pdP_pre hp₂ hf₂ he₂ hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pdContract.pub (t₁.callEntry.withRegions (pdRdP s₁) (pdWr s₁))
      (t₂.callEntry.withRegions (pdRdP s₂) (pdWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, w₁'.trans w₂'.symm, e₁.trans e₂.symm⟩
  exact ⟨pdRdP s₁, pdWr s₁, pdRdP s₂, pdWr s₂, p₁, p₂, hpub, Covers.append_left c₁ w₁.right, w₁,
    Covers.append_left c₂ w₂.right, w₂, by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## The pieces -/

theorem crtArgsP_two : RelCT isa (Two (AtP J0)) (.block crtArgsP) (Two (AtP J1P)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact pinP fb (fun s t h => by rw [h]; rfl) (fun _ _ h => h.fb) h₁ h₂) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      subst ht
      obtain ⟨hp, hf⟩ := preFP_of S.1
      exact WP.mono (crtArgsP_ok hp hf) fun _ ⟨he, _, hargs, h96, h104, hdi, hsi, hdx, hcx, h8, h9⟩ =>
        ⟨s, S, ⟨he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩, h96, h104⟩

theorem crtCallP_two (v : CrtImpl) : RelCT isa (Two (AtP J1P)) (.call v.nameP v.codeP) (Two (AtP J2)) :=
  two_post (crtP_ct v) fun _ _ ⟨s, S, ⟨he, hargs, hdi, hsi, hdx, hcx, h8, h9⟩, h96, h104⟩ =>
    WP.mono (crtP_call v (preFP_of S.1).1 (preFP_of S.1).2 he hargs h96 h104 hdi hsi hdx hcx h8 h9)
      fun _ h => ⟨s, S, h.1⟩

theorem pdArgsP_two : RelCT isa (Two (AtP J2)) (.block pdArgsP) (Two (AtP J5P)) :=
  two_piece [.rsp] (pinsP_rsp fun _ _ h => h) (by taint_decide)
    fun _ t ⟨s, S, he⟩ => by
      obtain ⟨hp, hf⟩ := preFP_of S.1
      refine WP.mono (pdArgsP_ok hp hf he) fun t₃ ⟨he₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩ => ?_
      have hw : ∀ {d : Nat}, d < 4 → word t₃.mem (fb s) (8 * d) =
          [off (fb s) oM, s.gpr .rcx, stackArg s 12, stackArg s 13].getD d 0 := fun {d} hd => by
        rw [hm₃]
        rcases (show d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 by omega_using [hd]) with rfl | rfl | rfl | rfl
        · simp (disch := decide) only [word_wo, word_self0, Nat.mul_zero]
          rfl
        · simp (disch := decide) only [word_wo, word_writeW_self, Nat.mul_one]; rfl
        · simp (disch := decide) only [word_wo, word_writeW_self]; rfl
        · simp (disch := decide) only [word_writeW_self]; rfl
      exact ⟨s, S, he₃, hw (d := 0) (by decide), hw (d := 1) (by decide),
        hw (d := 2) (by decide), hw (d := 3) (by decide), hdi₃, hsi₃, hdx₃, hcx₃, h8₃, h9₃⟩

theorem pdCallP_two (P : PublicImpl) (name : String) :
    RelCT isa (Two (AtP J5P)) (.call name (P.code)) (Two (AtP J2)) :=
  two_post (pdP_ct P name) fun _ _ ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (pdP_call P name (preFP_of S.1).1 (preFP_of S.1).2 he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9)
      fun _ h => ⟨s, S, h.1⟩

theorem cmpArgsP_two : RelCT isa (Two (AtP J2)) (.block cmpArgs) (Two (AtP J7)) :=
  two_piece [.rsp] (pinsP_rsp fun _ _ h => h) (by taint_decide)
    fun _ _ ⟨s, S, he⟩ => WP.mono (cmpArgs_ok (preFP_of S.1).1 he) fun _ ⟨_, _, hdi, hsi, hcx, h10, _, k⟩ =>
      ⟨s, S, (k.gpr (by decide)).trans he.rsp, hdi, hsi, hcx, h10⟩

theorem restP_ct : RelCT isa (Two (AtP J7))
    (.seq cmpLoop (.seq (.block masks) (.seq releaseLoop (.block [.mov .rax (.reg .r11)])))) fun _ _ => True :=
  two_taint [.rdi, .rsi, .rcx, .r10, .rsp] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact pinP (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pinP (fun s => stackArg s 0) (fun _ _ h => h.2.2.1) (fun _ _ S => S.arg (by decide)) h₁ h₂
    · exact pinP (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact pinP (fun _ => BitVec.ofNat 64 0) (fun _ _ h => h.2.2.2.2) (fun _ _ _ => rfl) h₁ h₂
    · exact pinP fb (fun _ _ h => h.1) (fun _ _ S => S.fb) h₁ h₂) (by taint_decide)

theorem bodyP_ct (v : CrtImpl) (pdName : String) :
    RelCT isa (Two (AtP J0)) (bodyP v.nameP v.codeP pdName (v.pubOp.code)) fun _ _ => True := by
  rw [bodyP_eq, checkP_eq, tail_eq]
  exact RelCT.seq crtArgsP_two (RelCT.seq (crtCallP_two v) (RelCT.seq pdArgsP_two
    (RelCT.seq (pdCallP_two v.pubOp pdName) (RelCT.seq cmpArgsP_two restP_ct))))

/-! ## The function -/

theorem codeP_constantTime (v : CrtImpl) (pdName : String) :
    ConstantTime isa chkContractP.pre chkContractP.pub (codeP v.nameP v.codeP pdName (v.pubOp.code)) :=
  RelCT.constantTime (relCT_alloc ((bodyP_ct v pdName).mono
    (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂, hpub⟩, e₁, e₂⟩ => ⟨s₁, ⟨s₁, ⟨h₁, pubP_refl s₁⟩, e₁⟩, ⟨s₂, ⟨h₂, hpub⟩, e₂⟩⟩)
    fun _ _ h => h))

/-- It writes `rsp` only in its frame's push and pop. -/
theorem codeP_spSafe (v : CrtImpl) (pdName : String) :
    (codeP v.nameP v.codeP pdName (v.pubOp.code)).all (fun i => !isa.writesSp i) = true := by
  simp only [codeP, bodyP_eq, checkP_eq, tail_eq, Code.all, v.spSafeP, v.pubOp.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.Rsa.X86_64
