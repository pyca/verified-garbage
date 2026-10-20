module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Context
public import VerifiedGarbage.Impl.Ffdh.X86_64.Domain
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtExpL

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Main
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH public-key validation on x86-64: correctness before the ABI epilogue -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPublic

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh VG.Proof.MlKem.X86_64
open VG.Spec.Ffdh

theorem cp_body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (c : CpCtx s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body M.mm E.code (.seq (.block r2Head) R.code)) s fun t =>
      cpPost s t ∧ t.gpr .rdi = s.gpr .r9 ∧ InScr (s.gpr .r9) ((scrLen s).toNat * 8) s.mem t.mem ∧
      (∀ i < 6, word t.mem (s.gpr .r9) (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hk1 := c.k1
  have hk2 := c.k2
  have hZ := c.hZ
  have hn := c.hs.nowrap
  have hw : ∀ i < 20, InRegions s.wr (off (s.gpr .r9) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPublic.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (cpEntry_ok rfl hw) fun s₁ ⟨hdi₁, saved₁, slots₁, ho₁, k₁⟩ => ?_
  have hD₁ := slots₁ (sDom, s.gpr .rdi) (by simp)
  have hL₁ := slots₁ (sDomLen, s.gpr .rsi) (by simp)
  have hK₁ := slots₁ (sK, s.gpr .rdx) (by simp)
  have hY₁ := slots₁ (sY, s.gpr .rcx) (by simp)
  have i₁ : InScr (s.gpr .r9) ((scrLen s).toNat * 8) s.mem s₁.mem := InScr.of_outside ho₁ (by omega)
  have hdom₁ := c.dom.congrK i₁ k₁
  have hpS : Src s₁ (s.gpr .r9) ((scrLen s).toNat * 8) (s.gpr .rdi)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat) := by
    have := src_slice (off := 0) (len := (s.gpr .rdx).toNat) hdom₁
      (by rcases c.dl with h | h <;> rw [h] <;> omega)
    simpa using this
  refine WP.mono (domHead_ok (c.hs.congr k₁.2.2) hdi₁ (by omega) hk1 hk2 hD₁
    (by rw [hK₁, ofNat_toNat64]) hpS (bytesAt_length _ _ _))
    fun s₂ ⟨hz₂, _, hQ₂, f₂, hdi₂, k₂⟩ => ?_
  have hp₂ : ∀ i < 32, i ≠ sG → i ≠ sQ →
      word s₂.mem (s.gpr .r9) (8 * i) = word s₁.mem (s.gpr .r9) (8 * i) := fun i hi h1 h2 =>
    f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> unfold sG sQ sFn at * <;> omega) (by omega)
  have i₂ : InScr (s.gpr .r9) ((scrLen s).toNat * 8) s.mem s₂.mem :=
    i₁.trans (InScr.of_frm f₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only [sG, sQ, sFn] <;> omega))
  have K₂ : Keep (.rdi :: mmRegs) s s₂ := keep_trans (k₁.mono (by decide)) (k₂.mono (by decide))
  have saved₂ : ∀ i < 6, word s₂.mem (s.gpr .r9) (8 * i) = s.gpr (saved.getD i .rax) := fun i hi => by
    rw [hp₂ i (by omega) (by unfold sG sFn; omega) (by unfold sQ sFn; omega)]
    exact saved₁ i hi
  have hpk : (domainOf (s.gpr .rdx).toNat (cpDom s)).p =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat) :=
    domainOf_p _ _ (by rcases c.dl with h | h <;> omega)
  refine WP.ite (!Spec.Rsa.modulusValid
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat)) (s.gpr .rdx).toNat)
    (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · have hv : Spec.Rsa.modulusValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat)) (s.gpr .rdx).toNat = false :=
      by simpa only [Bool.not_eq_true'] using hb
    refine WP.mono (ret_ok s₂ (r := 0) (by decide)) fun t ⟨_, hm, k⟩ =>
      ⟨?_, (k.gpr (by decide)).trans hdi₂, by rw [hm]; exact i₂,
        (fun i hi => by rw [hm]; exact saved₂ i hi), keep_trans K₂ (k.mono (by decide))⟩
    intro hd
    have := domainValid_mod hd
    rw [hpk, hv] at this
    exact absurd this (by decide)
  · have hv : Spec.Rsa.modulusValid
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rdx).toNat)) (s.gpr .rdx).toNat = true :=
      by simpa only [Bool.not_eq_false'] using hb
    refine WP.mono (cpMain_ok M E R c hdi₂ (c.hs.congr (k₂.2.2.trans k₁.2.2))
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hD₁)
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hL₁)
      (by rw [hp₂ _ (by decide) (by decide) (by decide), hK₁, ofNat_toNat64])
      (by rw [hp₂ _ (by decide) (by decide) (by decide)]; exact hY₁)
      hQ₂ i₂ (k₂.2.1.trans k₁.2.1) (k₂.2.2.trans k₁.2.2) hv)
      fun t ⟨hax, hdi, hf, hsaved, k⟩ => ⟨?_, hdi, i₂.trans hf,
        (fun i hi => (hsaved i hi).trans (saved₂ i hi)), keep_trans K₂ k⟩
    intro _
    rw [hax]
    split <;> rfl

end VG.Proof.Ffdh.X86_64.CheckPublic
