module

public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl

import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Core
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Sample
import Mathlib.Tactic.TermCongr
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Finish
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.CutInputs
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Zero
/-! # FFDH key-generation attempts on x86-64: correctness and ABI -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/CorrectMath.lean`, which only this module imported.
section

/-! # FFDH on x86-64: the attempt's outputs satisfy the shared key-generation specification -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Spec.Ffdh VG.Proof.Bignum

theorem resultStatus_lt (p : GkP) (rb : List Byte) : resultStatus p rb < 2 ^ 32 := by
  unfold resultStatus
  split
  · decide
  · split <;> decide

theorem attempt_spec {p : GkP} {rb : List Byte} {s u t : State} (hb : Base p rb u)
    (hm : p.mv = true) (ha : parametersValid p.params = true) (h : AttemptPost p rb s t) :
    ((t.gpr .rax).setWidth 32).toNat = keyStatus p.params (p.scalar rb) ∧
      if keyStatus p.params (p.scalar rb) = 1 then
        Spec.Rsa.bytesAt t.mem p.xp p.k = Spec.Rsa.i2osp (p.scalar rb) p.k ∧
          Spec.Rsa.bytesAt t.mem p.yp p.k = Spec.Rsa.i2osp (Spec.Rsa.powMod p.params.g (p.scalar rb) p.params.p) p.k
      else Spec.Rsa.bytesAt t.mem p.xp p.k = List.replicate p.k 0 ∧
        Spec.Rsa.bytesAt t.mem p.yp p.k = List.replicate p.k 0 := by
  obtain ⟨hr, _, hx, hy, _⟩ := h
  have hst := hb.resultStatus_eq hm ha
  have hlt := resultStatus_lt p rb
  refine ⟨?_, ?_⟩
  · rw [hr]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (hlt.trans (by decide)), Nat.mod_eq_of_lt hlt]
    exact hst
  · rw [← hst]
    by_cases hs : resultStatus p rb = 1
    · simp only [ite_eq_left hs] at hx hy ⊢
      refine ⟨hx.trans (hb.cut_i2osp hm), ?_⟩
      rw [hb.power_value hm] at hy
      rw [VG.Proof.Bignum.powMod_eq]
      exact hy
    · simp only [ite_eq_right hs] at hx hy ⊢
      exact ⟨hx, by rw [hy, i2osp_zero']⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Scalar.lean`, which only this module imported.
section

/-! # FFDH on x86-64: the complete scalar-sampling stage -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem saved_scan {p : GkP} {s t : State} (hf : Frm p.B scanRanges s.mem t.mem) :
    ∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := by
  intro i hi
  exact hf.word_eq (by
    simp only [scanRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [sEp, sEl, sMsk, sFn] <;> omega) (by omega)

/-- The sampled scalar is ready for the existing private-key arithmetic proofs. -/
def ScalarPost (p : GkP) (rb : List Byte) (s t : State) : Prop :=
  CheckPrivate.Base p.kp (p.xb rb) t ∧ Src t p.B p.Z p.xp (p.cut rb) ∧ t.gpr .rdi = p.B ∧
    word t.mem p.B (8 * sG) = off p.dp p.k ∧ word t.mem p.B (8 * sQ) = off p.dp (2 * p.k) ∧
    (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ RunFrame p s.mem t.mem ∧ Keep mmRegs s t

theorem scalar_ok {p : GkP} {rb : List Byte} {s : State} (h : Inputs p rb s) (hm : p.mv = true) :
    WP isa (seqs scalar) s (ScalarPost p rb s) := by
  unfold scalar
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.bound) (by simp [bound]) (by simp)
    (WP.mono (scan_inputs h) fun u ⟨hu, hn, ha, hf, k₁⟩ => ?_)
  change WP isa (.seq (.block smear) (.seq (.block cutSetup)
    (.seq (.loop (.block cutBody) .ne) (.block cutFinish)))) u _
  refine WP.seq (WP.mono (smear_inputs hu hn ha) fun v ⟨hv, hnv, hmask, hfv, k₂⟩ => ?_)
  refine WP.seq (WP.mono (cutSetup_ok hv hnv hmask) fun z ⟨⟨hr, hmz⟩, k₃⟩ => ?_)
  have hz : Inputs p rb z := hv.keep (by intro a _; rw [hmz]) k₃ (by decide)
  refine WP.seq (WP.mono (cut_inputs hz hr) fun a ⟨ha, hx, hh, h8, hf₄, k₄⟩ => ?_)
  have hna : word a.mem p.B (8 * sEl) = BitVec.ofNat 64 p.n := by
    rw [hh _ (by have := ha.base.hZ; change 200 ≤ p.Z; omega), hmz]
    exact hnv
  refine WP.mono (finish_base ha hx hm hna h8) fun t ⟨hb, hd, hG, hQ, hs, hi, k₅⟩ => ?_
  refine ⟨hb, hx.congrK hi k₅, hd, hG, hQ, ?_, ?_, (((k₁.trans k₂).trans k₃).trans (k₄.trans k₅)).mono (by decide)⟩
  · intro i hi'
    rw [hs i hi', hh _ (by have := h.base.hZ; omega), hmz, saved_scan hfv i hi', saved_scan hf i hi']
  · have hZ : 256 ≤ p.Z := by have := h.base.hZ; omega
    have f₁ : RunFrame p s.mem u.mem := .of_frm hf (fun r hr => (scanRanges_end r hr).trans hZ)
    have f₂ : RunFrame p u.mem v.mem := .of_frm hfv (fun r hr => (scanRanges_end r hr).trans hZ)
    have f₃ : RunFrame p v.mem z.mem := by rw [hmz]; exact .refl _ _
    exact ((f₁.trans f₂).trans f₃).trans (hf₄.trans (.of_scr hi))

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Main.lean`, which only this module imported.
section

/-! # FFDH on x86-64: a complete key-generation attempt -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.MlKem.X86_64

theorem main_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M)
    {p : GkP} {rb : List Byte} {s : State} (h : Base p rb s) (hd : s.gpr .rdi = p.B)
    (hG : word s.mem p.B (8 * sG) = off p.dp p.k) (hQ : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k))
    (hm : p.mv = true) :
    WP isa (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.main M.mm E.code (.seq (.block r2Head) R.code)) s
      (AttemptPost p rb s) := by
  have hk := h.k1
  have hZ := h.hZ
  unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.main
  change WP isa (.seq (VG.Impl.Rsa.X86_64.Keys.zeroOut sY sK)
    (seqs (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.scalar ++
      VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core M.mm E.code (.seq (.block r2Head) R.code)))) s _
  refine WP.seq (WP.mono (zero_ok h hd) fun u ⟨hu, hy, hf₁, hh, k₁⟩ => ?_)
  have hdi : u.gpr .rdi = p.B := (k₁.gpr (by decide)).trans hd
  have hg : word u.mem p.B (8 * sG) = off p.dp p.k := by
    rw [hh _ (by change 224 ≤ p.Z; omega)]; exact hG
  have hq : word u.mem p.B (8 * sQ) = off p.dp (2 * p.k) := by
    rw [hh _ (by change 232 ≤ p.Z; omega)]; exact hQ
  refine wp_seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.scalar)
    (b := VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core M.mm E.code (.seq (.block r2Head) R.code))
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.scalar])
    (by simp [VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core, pSetup])
    (WP.mono (scalar_ok ⟨hu, hdi, hy, hg, hq⟩ hm) fun v ⟨hb, hx, hdv, hgv, hqv, hs₂, hf₂, k₂⟩ => ?_)
  have hox : OutOk v p.B p.Z p.xp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact h.x.wr i hi, h.x.sep⟩
  have hoy : OutOk v p.B p.Z p.yp p.k :=
    ⟨fun i hi => by rw [k₂.2.2, k₁.2.2]; exact h.y.wr i hi, h.y.sep⟩
  refine WP.mono (core_ok M E R hb hdv hgv hqv hm hx hox hoy h.xy (h.cut_length) h.ld_lt)
    fun t ⟨hr, hdt, hX, hY, hs₃, hf₃, k₃⟩ => ?_
  refine ⟨hr, hdt, hX, hY, ?_, (RunFrame.of_y hf₁).trans (hf₂.trans hf₃), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  intro i hi
  rw [hs₃ i hi, hs₂ i hi, hh _ (by omega)]

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

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
