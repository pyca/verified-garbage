module

public import VerifiedGarbage.Proof.Rsa.X86_64.WordCrt
public import VerifiedGarbage.Proof.Rsa.X86_64.WordGuard
public import VerifiedGarbage.Proof.Rsa.X86_64.CvMain
import VerifiedGarbage.Proof.Bignum.Octets

-- separate module: CRT dispatch correctness is independent of the inverse and output-store proofs in CvMainOk

/-! # Public selection between word and bit remainder algorithms -/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem mask_true_iff (c : Bool) : mask c = mask true ↔ c = true := by cases c <;> decide

theorem cvWordChoice_ok {I : CvIn} {m₀ : Mem} {s : State} (h : CvS I m₀ s) (L : CvLens I) {j : Nat}
    (hj : j = aP ∨ j = aQ)
    (hP : wv s.mem I.B (slot (wk I.k) aP) (wk I.k) = I.P)
    (hQ : wv s.mem I.B (slot (wk I.k) aQ) (wk I.k) = I.Q)
    (hM : mword s.mem I.B = mask true → I.P * I.Q = I.N)
    (hv : Spec.Rsa.modulusValid I.N I.k = true) :
    WP isa (wordChoice j) s fun t =>
      CvS I m₀ t ∧ mword t.mem I.B = mword s.mem I.B ∧
      (mword s.mem I.B = mask true → wv t.mem I.B (slot (wk I.k) aV) (wk I.k + 1) =
        wv s.mem I.B (slot (wk I.k) aD) (wk I.k) %
          (wv s.mem I.B (slot (wk I.k) j) (wk I.k) - 1)) ∧
      (∀ i, i = aP ∨ i = aQ ∨ i = aD ∨ i = aX₁ ∨ i = aX₂ →
        wv t.mem I.B (slot (wk I.k) i) (wk I.k) = wv s.mem I.B (slot (wk I.k) i) (wk I.k)) := by
  have hk1 := L.k1
  have hk2 := L.k2
  have hW : 4 ≤ wk I.k := by unfold wk; omega_using [hk1]
  have hZ : slot (wk I.k) 17 ≤ I.Z := by
    have hz := L.z
    simp only [slot, Impl.Bignum.hdrBytes, wk]
    omega_using [hk1, hz]
  have pbound : I.P < 256 ^ I.pl := by have := os2ip_lt I.pb; rwa [L.pbl] at this
  have qbound : I.Q < 256 ^ I.ql := by have := os2ip_lt I.qb; rwa [L.qbl] at this
  obtain ⟨hodd, hlo⟩ := valid_lo hv
  have facts := factors_of hodd hlo pbound qbound L.pl2 L.ql2
  have fj : mword s.mem I.B = mask true →
      wv s.mem I.B (slot (wk I.k) j) (wk I.k) % 2 = 1 ∧ 1 < wv s.mem I.B (slot (wk I.k) j) (wk I.k) := by
    intro hc
    have f := facts (hM hc)
    rcases hj with rfl | rfl
    · rw [hP]; exact ⟨f.1, f.2.1⟩
    · rw [hQ]; exact ⟨f.2.2.1, f.2.2.2⟩
  unfold wordChoice
  refine WP.seq (WP.mono (WordDivide.guardHead_ok h) fun s₁ ⟨h₁, m₁, h12, hdx⟩ => ?_)
  refine WP.seq (WP.mono (WordDivide.guardTail_ok h₁ L h12 hdx) fun s₂ ⟨h₂, m₂, hz⟩ => ?_)
  have mm := m₂.trans m₁
  refine WP.ite (WordDivide.guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'(by rw [L.nl]; omega)) == 0) (by simp only [eval, hz]) (fun hb => ?_) (fun _ => ?_)
  · have hg : WordDivide.guardVal (wk I.k) I.k I.pl I.ql (I.nb[0]'(by rw [L.nl]; omega)) = 0 := by
      simpa only [beq_iff_eq] using hb
    refine WP.mono (cvWordFast_ok h₂ L hj hW hZ (fun hc => ?_)) fun t ⟨ht, mt, vt, pt⟩ => ?_
    · rw [mm] at hc ⊢
      obtain ⟨fp, fq⟩ := WordDivide.factors_word L hg (hM hc)
      refine ⟨(fj hc).1, ?_⟩
      rcases hj with rfl | rfl
      · rwa [hP]
      · rwa [hQ]
    · rw [mm] at mt vt pt
      exact ⟨ht, mt, vt, pt⟩
  · exact WP.mono (cvDivPart_ok h₂ L hj) fun t ⟨ht, mt, vt, pt⟩ => by
      rw [mm] at mt vt pt
      exact ⟨ht, mt, fun hc => vt (fj hc).1 (fj hc).2, pt⟩

end VG.Proof.Rsa.X86_64
