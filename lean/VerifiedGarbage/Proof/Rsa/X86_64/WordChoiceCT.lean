module

public import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
public import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvCTMain
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Constant-time public selection of CRT remainder algorithms -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The word reducer's extended array window remains inside RSA's workspace. -/
theorem GA.wordFrame {p : CvP} {s t : State} (h : GA p s)
    (ff : Frm p.B (WordDivide.normRanges (wk p.k)) s.mem t.mem) (kk : Keep mmRegs s t) : GA p t := by
  obtain ⟨I, m₀, c, rfl, h, L, O, hm⟩ := h
  have hw : 4 ≤ wk I.k := by have := L.k1; unfold wk; omega_using [this]
  have hZ : slot (wk I.k) 17 ≤ I.Z := by
    have hk := L.k1
    have hz := L.z
    simp only [slot, Impl.Bignum.hdrBytes, wk]; omega_using [hk, hz]
  have hn := h.ws.scr.nowrap
  refine ⟨I, m₀, c, rfl, h.step ff ?_ ?_ kk (by decide), L, O, ?_⟩
  · intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact Mut.ofSlot _ _ _
    · exact WordDivide.all_mut hr
  · intro r hr
    simp only [WordDivide.normRanges, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h.ws.sl (by decide)
    · exact WordDivide.all_bound h.ws hZ hr
  · rw [← hm]
    apply ff.word_eq _ (by change 8 * 22 + 8 ≤ 2 ^ 64; decide)
    intro r hr
    simp only [WordDivide.normRanges, WordDivide.allRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [VG.Impl.Rsa.X86_64.WordDivide.aM, VG.Impl.Rsa.X86_64.WordDivide.aR,
        VG.Impl.Rsa.X86_64.WordDivide.aT, VG.Impl.Rsa.X86_64.WordDivide.aV, slot, Public.sMask, sFn,
        Impl.Bignum.hdrBytes] <;> omega_arith

theorem wordFast_ct : RelCT isa (Two GA) (.seq (.block VG.Impl.Rsa.X86_64.WordDivide.normalize)
    VG.Impl.Rsa.X86_64.WordDivide.code) (Two GA) := by
  refine two_post (two_map (fun p : CvP => (⟨p.B, p.Z, wk p.k, 0⟩ : WordDivide.Pub)) ?_ WordDivide.fast_ct) ?_
  · rintro p s ⟨I, m₀, c, rfl, h, L, O, hm⟩
    have hk := L.k1
    have hz := L.z
    refine ⟨h.ws, ?_, ?_⟩
    · change slot (wk I.k) 17 ≤ I.Z
      simp only [slot, Impl.Bignum.hdrBytes, wk]; omega_using [hk, hz]
    · change 4 ≤ wk I.k
      unfold wk; omega_using [hk]
  · intro p s h
    obtain ⟨I, m₀, c, rfl, hs, L, O, hm⟩ := h
    have hk := L.k1
    have hz := L.z
    have hZ : slot (wk I.k) 17 ≤ I.Z := by
      simp only [slot, Impl.Bignum.hdrBytes, wk]; omega_using [hk, hz]
    exact WP.mono (WordDivide.fast_ok hs.ws hZ (by unfold wk; omega_using [hk])) fun t ⟨_, ff, kk⟩ =>
      (show GA I.pub s from ⟨I, m₀, c, rfl, hs, L, O, hm⟩).wordFrame ff kk

def WordHead (p : CvP) (s : State) : Prop :=
  GA p s ∧ s.gpr .r12 = BitVec.ofNat 64 (wk p.k) ∧ s.gpr .rdx = p.pN

def publicGuard (p : CvP) : BitVec 64 :=
  WordDivide.guardVal (wk p.k) p.k p.pl p.ql ((p.nb[0]?).getD 0)

def WordTest (p : CvP) (s : State) : Prop := GA p s ∧ s.zf = some (publicGuard p == 0)

theorem wordHead_ct : RelCT isa (Two GA) (.block wordGuardHead) (Two WordHead) := by
  unfold wordGuardHead
  refine ws_block_ct CvP.B CvP.Z (fun p => wk p.k) (fun _ _ h => h.ws) (by taint_decide) ?_
  rintro p s ⟨I, m₀, c, rfl, h, L, O, hm⟩
  exact WP.mono (WordDivide.guardHead_ok h) fun t ⟨ht, mt, h12, hdx⟩ =>
    ⟨⟨I, m₀, c, rfl, ht, L, O, by rw [mt]; exact hm⟩, h12, hdx⟩

theorem wordTail_ct : RelCT isa (Two WordHead) (.block wordGuardTail) (Two WordTest) := by
  refine two_piece [.rdi, .rdx] ?_ (by taint_decide) ?_
  · intro p s₁ s₂ h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.ws.rdi, h₂.1.ws.rdi]
    · rw [h₁.2.2, h₂.2.2]
  · rintro p s ⟨⟨I, m₀, c, rfl, h, L, O, hm⟩, h12, hdx⟩
    refine WP.mono (WordDivide.guardTail_ok h L h12 hdx) fun t ⟨ht, mt, hz⟩ => ?_
    refine ⟨⟨I, m₀, c, rfl, ht, L, O, by rw [mt]; exact hm⟩, ?_⟩
    have hnl : 0 < I.nb.length := by rw [L.nl]; have := L.k1; omega_using [this]
    simpa only [publicGuard, CvIn.pub, List.getElem?_eq_getElem hnl, Option.getD_some] using hz

/-- Both branches preserve the same public construction state. -/
theorem wordChoice_ct {j : Nat} (hj : j < 16) (hjC : aC ≠ j) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (base j .rsi ++ base aC .rbx)) copyWords)
      hc).isSome = true) : RelCT isa (Two GA) (wordChoice j) (Two GA) := by
  unfold wordChoice
  refine RelCT.seq wordHead_ct (RelCT.seq wordTail_ct ?_)
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact (RelCT.seq (divisor_ct hj hjC ht) wordFast_ct).mono
      (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)
  · exact (ct_app (by simp [divisor]) (by simp) (divisor_ct hj hjC ht)
      (ct_one (divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by taint_decide)))).mono
      (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)

end VG.Proof.Rsa.X86_64
