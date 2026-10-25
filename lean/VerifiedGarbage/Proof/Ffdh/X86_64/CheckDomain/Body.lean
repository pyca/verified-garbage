module
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Context

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Math
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves

/-! # FFDH domain validation on x86-64: complete body correctness -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem bit_bool (b : Bool) : ((bit (b = true)).setWidth 32).toNat = if b then 1 else 0 := by
  cases b <;> rfl

theorem cd_body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (c : CdCtx s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body M.mm E.code (.seq (.block r2Head) R.code)) s fun t =>
      cdPost s t ∧ t.gpr .rdi = (cdOf s).B ∧ InScr (cdOf s).B (cdOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (cdOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_base c) fun u₁ ⟨hb₁, hd₁, hi₁, hs₁, k₁⟩ => ?_
  refine WP.mono (dom_base hb₁ hd₁) fun u₂ ⟨hb₂, hz₂, hd₂, hG, hQ, hi₂, hs₂, k₂⟩ => ?_
  have hi := hi₁.trans hi₂
  have hs : ∀ i < 6, word u₂.mem (cdOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs₂ i hi).trans (hs₁ i hi)
  have k := keep_trans k₁ k₂
  refine WP.ite (!(cdOf s).mv) (by simp [eval, hz₂]) (fun hn => ?_) (fun hy => ?_)
  · have hn' : (cdOf s).mv = false := by simpa only [Bool.not_eq_true'] using hn
    have hv := invalid_modulus hn'
    refine WP.mono (ret_ok u₂ (r := 0) (by decide)) fun t ⟨ha, hm, kk⟩ => ?_
    refine ⟨?_, (kk.gpr (by decide)).trans hd₂, by rw [hm]; exact hi,
      (fun i hi => by rw [hm]; exact hs i hi), keep_trans k (kk.mono (by decide))⟩
    change ((t.gpr .rax).setWidth 32).toNat = if Spec.Ffdh.domainValid (cdOf s).k (cdOf s).dom then 1 else 0
    rw [ha, hv]; rfl
  · have hy' : (cdOf s).mv = true := by simpa only [Bool.not_eq_false'] using hy
    refine WP.mono (main_ok M E R hb₂ hd₂ hG hQ hy') fun t S₃ => ?_
    refine ⟨?_, S₃.1.1, hi.trans S₃.2.1,
      (fun i hi => (S₃.2.2.1 i hi).trans (hs i hi)), keep_trans k S₃.2.2.2⟩
    change ((t.gpr .rax).setWidth 32).toNat = if Spec.Ffdh.domainValid (cdOf s).k (cdOf s).dom then 1 else 0
    have he := propext (accept_valid hb₂ hy')
    rw [S₃.1.2]
    simpa only [bit, he] using bit_bool (Spec.Ffdh.domainValid (cdOf s).k (cdOf s).dom)

end VG.Proof.Ffdh.X86_64.CheckDomain
