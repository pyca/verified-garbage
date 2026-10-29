module
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Arguments
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateStores
import VerifiedGarbage.Proof.Framework.Omega

/-! # Candidate arithmetic and output storage from retained frame arguments -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Impl.Dsa.AArch64.Generation
open VG.Impl.Dsa.Generation.Layout

theorem candidateFromFrame_ok {s : State} {B F : Addr} {Z w pLen qLen : Nat}
    {W : Nat → BitVec 64} {xb qb : List Byte}
    (h : Ws s B Z w) (hpLen : pLen = 8 * w) (hqLen : qLen ≤ pLen) (hpMax : pLen ≤ 1024)
    (hsp : s.sp = F)
    (hr : ∀ k < 34, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 34, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8)
    (sx : Src s B Z (off (W 5) shaped) xb) (sq : Src s B Z (off (W 5) q) qb)
    (hx : xb.length = pLen) (hq : qb.length = qLen) (hqposlen : 1 ≤ qLen)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w))
    (hpw : ∀ i < pLen, InRegions s.wr (off (off (W 5) p) i) 1)
    (hew : ∀ i < pLen, InRegions s.wr (off (off (W 5) exponent) i) 1)
    (hpo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) p) i))
    (heo : ∀ i < pLen, Z ≤ ofs B (off (off (W 5) exponent) i))
    (hpe : ∀ i < pLen, ∀ j < pLen, off (off (W 5) p) i ≠ off (off (W 5) exponent) j) :
    WP isa (candidateFromFrame pLen qLen) s fun t =>
      let value := Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb)
      Spec.Rsa.bytesAt t.mem (off (W 5) p) pLen = Spec.Dsa.encodeBE pLen value ∧
      Spec.Rsa.bytesAt t.mem (off (W 5) exponent) pLen =
        Spec.Dsa.encodeBE pLen ((value - 1) / Spec.Rsa.os2ip qb) ∧
      Ws t B Z w ∧ word t.mem B 160 = off (W 5) p ∧ Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem t.mem ∧
      Keep mmRegs s t := by
  have hpl : pLen < 2 ^ 16 := by omega
  have hql : qLen < 2 ^ 16 := by omega
  unfold candidateFromFrame
  refine WP.seq (WP.mono (candidateArguments_ok h hpl hql hsp hr hwords hsep)
    fun u ⟨hu, hxp, hxl, hqp, hqlen, hpp, hep, hm, hf, hk⟩ => ?_)
  have frame : Frm B [(128, 128)] s.mem u.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(128, 128)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_singleton, forall_eq]
    exact h.h256
  have sxu := sx.congrK (InScr.of_frm frame bound) hk
  have squ := sq.congrK (InScr.of_frm frame bound) hk
  refine WP.mono (candidateBuild_ok hu hxp (by rw [hx]; exact hxl) hqp (by rw [hq]; exact hqlen)
    hpp hep hm sxu squ (hx.trans hpLen) (by omega) (by omega) hqpos hqfit
    (fun i hi => by rw [hk.wr]; exact hpw i (hpLen ▸ hi))
    (fun i hi => by rw [hk.wr]; exact hew i (hpLen ▸ hi))
    (fun i hi => hpo i (hpLen ▸ hi)) (fun i hi => heo i (hpLen ▸ hi))
    (fun i hi j hj => hpe i (hpLen ▸ hi) j (hpLen ▸ hj))) fun t ⟨tp, te, ht, hp, ft, kt⟩ => ?_
  rw [← hpLen] at tp te ft
  refine ⟨tp, te, ht, hp, ?_, (hk.trans kt).mono (by decide)⟩
  have ff : Frame [⟨B, Z⟩, ⟨off (W 5) p, pLen⟩, ⟨off (W 5) exponent, pLen⟩] s.mem u.mem := by
    intro a ha
    apply hf a
    right
    have hn := ha ⟨B, Z⟩ (by simp)
    change ¬ ofs B a < Z at hn
    have := h.h256
    omega
  exact ff.trans ft

end VG.Proof.Dsa.AArch64.Generation
