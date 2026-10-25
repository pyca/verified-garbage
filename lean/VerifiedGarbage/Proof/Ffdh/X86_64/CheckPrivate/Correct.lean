module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Main
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
public import Mathlib.Tactic.TermCongr
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH private-key validation on x86-64: correctness and ABI -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Spec.Ffdh

theorem body_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {s : State} (hpre : kpPre s) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body M.mm E.code (.seq (.block r2Head) R.code)) s fun t =>
      kpPost s t ∧ t.gpr .rdi = (kpOf s).B ∧ InScr (kpOf s).B (kpOf s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (kpOf s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t := by
  have c := kpCtx_of hpre
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (entry_base c) fun u ⟨hb, hd, hi, hs, k⟩ => ?_
  refine WP.mono (dom_base hb hd) fun v ⟨hb', hz, hd', hG, hQ, hi', hs', k'⟩ => ?_
  have H := hi.trans hi'
  have K := keep_trans k k'
  have hS : ∀ i < 6, word v.mem (kpOf s).B (8 * i) = s.gpr (saved.getD i .rax) :=
    fun i hi => (hs' i hi).trans (hs i hi)
  refine WP.ite (!(kpOf s).mv) (by simp [eval, hz]) (fun hf => ?_) (fun hf => ?_)
  · have hm : (kpOf s).mv = false := by simpa only [Bool.not_eq_true'] using hf
    refine WP.mono (ret_ok v (r := 0) (by decide)) fun t ⟨_, hmem, kk⟩ =>
      ⟨?_, (kk.gpr (by decide)).trans hd', by rw [hmem]; exact H,
        (fun i hi => by rw [hmem]; exact hS i hi), keep_trans K (kk.mono (by decide))⟩
    intro hv
    have hm' := domainValid_mod hv
    change (kpOf s).mv = true at hm'
    rw [hm] at hm'
    contradiction
  · have hm : (kpOf s).mv = true := by simpa only [Bool.not_eq_false'] using hf
    refine WP.mono (main_ok M E R hb' hd' hG hQ hm) fun t ⟨⟨hd'', ha⟩, hi'', hs'', kk⟩ =>
      ⟨?_, hd'', H.trans hi'', (fun i hi => (hs'' i hi).trans (hS i hi)), keep_trans K kk⟩
    intro hv
    have hp : parametersValid (kpOf s).params = true := by
      unfold domainValid at hv
      exact ((Bool.and_eq_true _ _).mp hv).1
    have hst : mainStatus (kpOf s) (kpX s) < 2 ^ 32 := (mainStatus_lt _ _).trans (by decide)
    change ((t.gpr .rax).setWidth 32).toNat = privateStatus (kpOf s).params (Spec.Rsa.os2ip (kpOf s).yb) (Spec.Rsa.os2ip (kpX s))
    rw [ha]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (hst.trans (by decide)), Nat.mod_eq_of_lt hst]
    exact mainStatus_eq hb' hm hp

theorem kp_correct (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    (hmx : (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code)).allInstrs
      (fun i => !loadsMxcsr i) = true) (s : State) (h : kpContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code)) s tr t ∧
      abiPreserved s t ∧ kpContract.post s t := by
  have hpre := h
  have c := kpCtx_of h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hRetScr, _⟩ := h
  suffices hw : WP isa (VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code M.mm E.code (.seq (.block r2Head) R.code)) s
      fun t => gprPreserved s t ∧ kpContract.post s t by
    obtain ⟨tr, t, he, hg, hp⟩ := hw
    exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.code
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
    exact hf _ (out_scr hRetScr (contains_byte (s.gpr .rsp) hi (by decide)))
  · change kpPost s t
    unfold kpPost
    rw [kk.gpr (show .rax ∉ saved by decide)]
    exact hp

end VG.Proof.Ffdh.X86_64.CheckPrivate
