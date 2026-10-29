module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
/-! # Preserve p and the generator exponent across primality testing -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/WorkspaceWords.lean`, which only this module imported.
section

/-! Workspace headers survive writes to disjoint output byte buffers. -/
section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64

theorem workspace_of_words {s t : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    (hm : ∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d)
    (hwr : t.wr = s.wr) (h0 : t.gpr .x0 = B) : Ws t B Z w := by
  have hz := h.h256
  exact ⟨h.scr.congr hwr, h0,
    (hm _ (by simp only [sW]; omega)).trans h.hw,
    (hm _ (by simp only [sStride, sFn]; omega)).trans h.hS,
    fun j hj => (hm _ (by simp only [sArr]; omega)).trans (h.harr j hj), h.hZ, h.w1, h.w2⟩

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64

/-- A full-width native store preserves the entire arithmetic workspace. -/
theorem storeCandidateArray_ok {s : State} {B out : Addr} {Z w a ptr : Nat}
    (h : Ws s B Z w) (ha : a < 16) (hptr : ptr < 32)
    (hp : word s.mem B (8 * ptr) = out) (hl : word s.mem B 136 = BitVec.ofNat 64 (8 * w))
    (hm : word s.mem B (8 * Public.sMask) = mask true)
    (hout : ∀ i < 8 * w, InRegions s.wr (off out i) 1)
    (hsep : ∀ i < 8 * w, Z ≤ ofs B (off out i)) :
    WP isa (seqs (Impl.Rsa.AArch64.Keys.storeA a ptr 17 Public.sMask)) s fun t =>
      Spec.Rsa.bytesAt t.mem out (8 * w) = Spec.Dsa.encodeBE (8 * w) (wv s.mem B (slot w a) w) ∧
      (∀ x, (∀ i < 8 * w, x ≠ off out i) → t.mem x = s.mem x) ∧
      Ws t B Z w ∧ Frm B [(Z, 2 ^ 64)] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (storeA_ok h ha hptr (by decide : 17 < 32) (by decide : Public.sMask < 32)
    hp hl hm (by have := h.w1; omega) (Nat.le_refl _) hout hsep)
    fun t ⟨hb, hf, hwr, _, hk⟩ => ?_
  have hw := words_outside_bytes (by have := h.scr.nowrap; omega : Z ≤ 2 ^ 64) hf hsep
  have ht := workspace_of_words h hw hwr ((hk.gpr .x0 (by decide)).trans h.x0)
  have fr : Frm B [(Z, 2 ^ 64)] s.mem t.mem := by
    intro x hx
    apply hf
    intro i hi he
    subst x
    have ho := hsep i hi
    have hc := hx (Z, 2 ^ 64) (by simp)
    have hl : ofs B (off out i) < 2 ^ 64 := (off out i - B).isLt
    simp only [off] at ho hl
    omega
  refine ⟨?_, hf, ht, fr, hk.mono (by decide)⟩
  simpa only [Spec.Rsa.bytesAt, off, VG.Proof.Dsa.encodeBE_i2osp, ite_true,
    show (8 * w + 7) / 8 = w by omega] using hb

theorem candidateStores_ok {s : State} {B pp ep : Addr} {Z w : Nat}
    (h : Ws s B Z w)
    (hp : word s.mem B 160 = pp) (he : word s.mem B 168 = ep)
    (hl : word s.mem B 136 = BitVec.ofNat 64 (8 * w))
    (hm : word s.mem B (8 * Public.sMask) = mask true)
    (hpw : ∀ i < 8 * w, InRegions s.wr (off pp i) 1)
    (hew : ∀ i < 8 * w, InRegions s.wr (off ep i) 1)
    (hpo : ∀ i < 8 * w, Z ≤ ofs B (off pp i))
    (heo : ∀ i < 8 * w, Z ≤ ofs B (off ep i))
    (hpe : ∀ i < 8 * w, ∀ j < 8 * w, off pp i ≠ off ep j) :
    WP isa Impl.Dsa.AArch64.Generation.candidateStores s fun t =>
      Spec.Rsa.bytesAt t.mem pp (8 * w) = Spec.Dsa.encodeBE (8 * w) (wv s.mem B (slot w 5) w) ∧
      Spec.Rsa.bytesAt t.mem ep (8 * w) = Spec.Dsa.encodeBE (8 * w) (wv s.mem B (slot w 0) w) ∧
      Ws t B Z w ∧ Frame [⟨pp, 8 * w⟩, ⟨ep, 8 * w⟩] s.mem t.mem ∧
      Frm B [(Z, 2 ^ 64)] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.candidateStores
  refine WP.seq (WP.mono (storeCandidateArray_ok h (by decide : 5 < 16) (by decide : 20 < 32)
    hp hl hm hpw hpo) fun u ⟨up, fu, hu, wu, ku⟩ => ?_)
  have uh : ∀ d, d + 8 ≤ Z → word u.mem B d = word s.mem B d := by
    intro d hd
    exact wu.word_eq (by simp only [List.mem_singleton]; rintro r rfl; exact Or.inl hd)
      (by have := h.scr.nowrap; omega)
  have hh := h.h256
  refine WP.mono (storeCandidateArray_ok hu (by decide : 0 < 16) (by decide : 21 < 32)
    (by rw [uh 168 (by omega)]; exact he) (by rw [uh 136 (by omega)]; exact hl)
    (by rw [uh (8 * Public.sMask) (by unfold Public.sMask sFn; omega)]; exact hm)
    (fun i hi => by rw [ku.wr]; exact hew i hi) heo) fun t ⟨te, ft, ht, wt, kt⟩ => ?_
  refine ⟨?_, ?_, ht, ?_, wu.trans wt, (ku.trans kt).mono (by decide)⟩
  · rw [← up]
    apply List.ext_getElem
    · simp only [bytesAt_length]
    · intro i hi _
      simp only [bytesAt_length] at hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      exact ft _ (fun j hj => hpe i hi j hj)
  · rw [te, wu.wv_eq (by
      simp only [List.mem_singleton]; rintro r rfl; left
      have := h.sl (by decide : 0 < 16); omega)
      (by have := h.sl (by decide : 0 < 16); have := h.scr.nowrap; omega)]
  · intro a ha
    rw [ft a (fun i hi heq => ha ⟨ep, 8 * w⟩ (by simp) (heq ▸
      Offset.contains_base ep hi (by have := h.w2; omega))),
      fu a (fun i hi heq => ha ⟨pp, 8 * w⟩ (by simp) (heq ▸
      Offset.contains_base pp hi (by have := h.w2; omega)))]

/-- Complete candidate arithmetic from input byte buffers to saved p and
exponent byte buffers. The only other writes are to the arithmetic arrays. -/
theorem candidateBuild_ok {s : State} {B xp qp pp ep : Addr} {Z w : Nat} {xb qb : List Byte}
    (h : Ws s B Z w)
    (hxp : word s.mem B 128 = xp) (hxl : word s.mem B 136 = BitVec.ofNat 64 xb.length)
    (hqp : word s.mem B 144 = qp) (hql : word s.mem B 152 = BitVec.ofNat 64 qb.length)
    (hp : word s.mem B 160 = pp) (he : word s.mem B 168 = ep)
    (hm : word s.mem B (8 * Public.sMask) = mask true)
    (sx : Src s B Z xp xb) (sq : Src s B Z qp qb) (hwidth : xb.length = 8 * w)
    (hqposlen : 1 ≤ qb.length) (hqf : qb.length ≤ 8 * w)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w))
    (hpw : ∀ i < 8 * w, InRegions s.wr (off pp i) 1)
    (hew : ∀ i < 8 * w, InRegions s.wr (off ep i) 1)
    (hpo : ∀ i < 8 * w, Z ≤ ofs B (off pp i))
    (heo : ∀ i < 8 * w, Z ≤ ofs B (off ep i))
    (hpe : ∀ i < 8 * w, ∀ j < 8 * w, off pp i ≠ off ep j) :
    WP isa Impl.Dsa.AArch64.Generation.candidateBuild s fun t =>
      let p := Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb)
      Spec.Rsa.bytesAt t.mem pp (8 * w) = Spec.Dsa.encodeBE (8 * w) p ∧
      Spec.Rsa.bytesAt t.mem ep (8 * w) = Spec.Dsa.encodeBE (8 * w) ((p - 1) / Spec.Rsa.os2ip qb) ∧
      Ws t B Z w ∧ word t.mem B 160 = pp ∧
      Frame [⟨B, Z⟩, ⟨pp, 8 * w⟩, ⟨ep, 8 * w⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.AArch64.Generation.candidateBuild
  refine WP.seq (WP.mono (candidateArithmetic_ok h hxp hxl hqp hql sx sq
    (by rw [hwidth]; have := h.w1; omega) (by omega) hqposlen hqf hqpos hqfit)
    fun u ⟨hu, up, ue, fu, ku⟩ => ?_)
  have uh : ∀ d, d + 8 ≤ 256 → word u.mem B d = word s.mem B d := by
    intro d hd
    exact fu.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        left <;> simp only [slot, hdrBytes] <;> omega)
      (by have := h.scr.nowrap; have := h.h256; omega)
  refine WP.mono (candidateStores_ok hu (by rw [uh 160 (by decide)]; exact hp)
    (by rw [uh 168 (by decide)]; exact he) (by rw [uh 136 (by decide), hxl, hwidth])
    (by rw [uh (8 * Public.sMask) (by decide)]; exact hm)
    (fun i hi => by rw [ku.wr]; exact hpw i hi)
    (fun i hi => by rw [ku.wr]; exact hew i hi) hpo heo hpe)
    fun t ⟨tp, te, ht, ft, wt, kt⟩ => ?_
  refine ⟨by rw [tp, up], by rw [te, ue], ht, ?_, ?_, (ku.trans kt).mono (by decide)⟩
  · rw [wt.word_eq (d := 160) (by
      simp only [List.mem_singleton]; rintro r rfl; left; have := h.h256; omega)
      (by decide : 160 + 8 ≤ 2 ^ 64), uh 160 (by decide)]
    exact hp
  have fs : Frame [⟨B, Z⟩, ⟨pp, 8 * w⟩, ⟨ep, 8 * w⟩] s.mem u.mem := by
    intro a ha
    apply fu a
    intro r hr
    have hrz : r.1 + r.2 ≤ Z := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact h.sl (by decide)
    have hz := ha ⟨B, Z⟩ (by simp)
    change ¬ (a - B).toNat < Z at hz
    dsimp only [ofs]
    omega
  exact fs.trans (ft.mono (by simp))

end VG.Proof.Dsa.AArch64.Generation
