module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessState

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawPrefix
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessRange
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TapeHead

/-! # FFDH parameter generation on x86-64: one rejection-sampling iteration -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem drawSample_ok {p : WitnessParams} {rp : Addr} {used : Nat} {bs : List Byte} {s : State}
    (h : DrawState p rp used bs s) (havail : p.len ≤ bs.length) :
    WP isa drawSample s fun t =>
      let a := Spec.Rsa.os2ip (bs.take p.len) % 2 ^ p.bits
      DrawState p (off rp p.len) (used + p.len) (bs.drop p.len) t ∧
      wv t.mem p.I (slot p.w aXm) p.w = a ∧ t.zf = some (!decide (2 ≤ a ∧ a < p.N - 1)) ∧
      word t.mem p.O (8 * oStatus) = 1 ∧
      (∀ j < 32, j ≠ oStatus → word t.mem p.O (8 * j) =
        word (advanceMem s.mem p.O rp p.len bs.length used) p.O (8 * j)) ∧
      DrawFrame p s.mem t.mem ∧ Keep mmRegs s t := by
  have hz64 : p.Z ≤ 2 ^ 64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
  unfold drawSample
  simp only [VG.Impl.Bignum.X86_64.seqs]
  refine WP.seq (WP.mono (drawPrefix_ok h havail) fun u ⟨hu, hx, hh, hf, k⟩ => ?_)
  refine WP.seq (WP.mono (witnessRange_ok hu.ready p.dims p.odd hx)
    fun v ⟨_, hz, hrv, hxv, hfr, kr⟩ => ?_)
  have hfit : ∀ r ∈ [(slot p.w aTmp, 8 * p.w), (8 * VG.Impl.Ffdh.X86_64.Domain.sF, 8)],
      r.1 + r.2 ≤ p.IZ := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hb := slot_le (w := p.w) (show aTmp < 8 by decide)
      omega_using [hb, p.dims.z]
    · change 248 ≤ p.IZ
      have hb := p.dims.z
      unfold slot VG.Impl.Bignum.hdrBytes at hb
      omega_using [hb]
  have hhlo : ∀ r ∈ [(slot p.w aTmp, 8 * p.w), (8 * VG.Impl.Ffdh.X86_64.Domain.sF, 8)], 136 ≤ r.1 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · unfold slot VG.Impl.Bignum.hdrBytes aTmp; omega
    · decide
  have hhv := inner_header hfr hfit hz64
  have hfv := DrawFrame.of_inner hfr hfit hz64
  have hlv := (inner_link hfr hhlo).trans hu.link
  have hv := hu.transport hrv hlv (fun j hj _ => hhv j hj) hfv kr
  have houter : Scr v p.O 256 := by
    simpa [off] using hv.scr.sub (o := 0) (n := 256) p.space_bounds.1 (by decide)
  refine WP.mono (drawFinish_ok hv.ready.good.scr p.space_bounds.2.1 houter hv.ready.good.rdi hv.link)
    fun t ⟨hm, hzf, kt⟩ => ?_
  obtain ⟨ht, hxt, hht, hft⟩ := hv.status_write (1#64) hm kt ((kt.gpr (by decide)).trans hv.ready.good.rdi)
  refine ⟨ht, hxt.trans hxv, hzf.trans hz, ?_, ?_, (hf.trans hfv).trans hft,
    ((k.trans kr).trans kt).mono (by decide)⟩
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro j hj hne
    exact ((hht j hj hne).trans (hhv j hj)).trans (hh j hj)

end VG.Proof.Ffdh.X86_64.ParameterCandidate
