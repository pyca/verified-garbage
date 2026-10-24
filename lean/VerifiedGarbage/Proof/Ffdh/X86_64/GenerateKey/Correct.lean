module

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CorrectMath
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Main
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH key-generation attempts on x86-64: correctness and ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.Ffdh

theorem body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (hpre : gkPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.body M.mm E.code (.seq (.block r2Head) R.code)) s fun t =>
      gkPost s t ∧ t.gpr .rdi = (gkOf s).B ∧ RunFrame (gkOf s) s.mem t.mem ∧
      (∀ i < 6, word t.mem (gkOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  have c := gkCtx_of hpre
  unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_base c) fun u ⟨hb, hd, hi, hs, k⟩ => ?_
  refine WP.mono (dom_base hb hd) fun v ⟨hb', hz, hd', hG, hQ, hi', hs', k'⟩ => ?_
  have H := hi.trans hi'
  have K := keep_trans k k'
  have hS : ∀ i < 6, word v.mem (gkOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs' i hi).trans (hs i hi)
  refine WP.ite (!(gkOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun hf => ?_)
  · have hm : (gkOf s).mv = false := by simpa only [Bool.not_eq_true'] using hf
    refine WP.mono (ret_ok v (r := 0) (by decide)) fun t ⟨_, hmem, kk⟩ =>
      ⟨?_, (kk.gpr (by decide)).trans hd', (fun a ha _ _ => by rw [hmem]; exact H a ha),
        (fun i hi => by rw [hmem]; exact hS i hi), keep_trans K (kk.mono (by decide))⟩
    intro hv
    have hm' := domainValid_mod hv
    change (gkOf s).mv = true at hm'
    rw [hm] at hm'
    contradiction
  · have hm : (gkOf s).mv = true := by simpa only [Bool.not_eq_false'] using hf
    refine WP.mono (main_ok M E R hb' hd' hG hQ hm) fun t hh => ?_
    have hmain := hh
    obtain ⟨_, hdt, _, _, hsave, hframe, kk⟩ := hh
    refine ⟨?_, hdt, (RunFrame.of_scr H).trans hframe,
      (fun i hi => (hsave i hi).trans (hS i hi)), keep_trans K kk⟩
    intro hv
    have hp : parametersValid (gkOf s).params = true := by
      unfold domainValid at hv
      exact ((Bool.and_eq_true _ _).mp hv).1
    exact attempt_spec (p := gkOf s) (rb := gkRand s) (s := v) (u := v) (t := t) hb' hm hp hmain

theorem gk_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : gkContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ gkContract.post s t := by
  have hpre := h
  have c := gkCtx_of h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hRetX, hRetY, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ gkContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.code
  refine WP.seq (WP.mono (body_ok M E R hpre) fun u ⟨hp, hd, hf, hs, k⟩ => ?_)
  have hZ := c.hZ
  have hk := c.k1
  refine WP.mono (exit_ok (c.hs.congr k.2.2) hd (by omega) hs)
    fun t ⟨hRestore, hm, kk⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact (kk.gpr (by decide)).trans (k.gpr (by decide))
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
    · exact hRestore _ (by decide)
  · rw [hm]
    apply Mem.readW_congr
    intro i hi
    have hbyte := contains_byte (s.gpr .rsp) hi (by decide)
    refine hf _ (out_scr hRetScr hbyte) ?_ ?_
    · intro j hj he
      exact hRetX _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.xl]; exact hj) (by have := c.k2; omega))
    · intro j hj he
      exact hRetY _ hbyte (by rw [he]; exact contains_byte _ (by rw [c.yl]; exact hj) (by have := c.k2; omega))
  · change gkPost s t
    unfold gkPost
    rw [kk.gpr (show .rax ∉ saved by decide), hm]
    exact hp

end VG.Proof.Ffdh.X86_64.GenerateKey
