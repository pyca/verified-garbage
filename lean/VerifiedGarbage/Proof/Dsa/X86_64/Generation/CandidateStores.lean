module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateArithmetic
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Arguments
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Arguments
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! ### `Dsa.X86_64.Generation.CandidateArguments`, which the modules that import this one used -/

section

/-! # Native setup for candidate reduction and the saved generator exponent -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

private theorem candidate_arguments_fit {pLen qLen : Nat} (hp : pLen < 2 ^ 31) (hq : qLen < 2 ^ 31) :
    ∀ a ∈ candidateArguments pLen qLen, argumentFits a := by
  intro a ha
  simp only [candidateArguments, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only [argumentFits]
  · decide
  · exact ⟨by decide, by decide, hp⟩
  · decide
  · exact ⟨by decide, by decide, hq⟩
  · decide
  · decide
  · decide

theorem candidateArguments_ok {s : State} {B F : Addr} {Z w pLen qLen : Nat} {W : Nat → BitVec 64}
    (h : Ws s B Z w) (hp : pLen < 2 ^ 31) (hq : qLen < 2 ^ 31) (hsp : s.gpr .rsp = F)
    (hr : ∀ k < 37, InRegions (s.rd ++ s.wr) (off F (8 * k)) 8)
    (hwords : ∀ k < 37, word s.mem F (8 * k) = W k)
    (hsep : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8) :
    WP isa (.block (headerArguments (candidateArguments pLen qLen))) s fun t =>
      Ws t B Z w ∧
      word t.mem B 128 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.shaped ∧
      word t.mem B 136 = BitVec.ofNat 64 pLen ∧
      word t.mem B 144 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q ∧
      word t.mem B 152 = BitVec.ofNat 64 qLen ∧
      word t.mem B 160 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.p ∧
      word t.mem B 168 = W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.exponent ∧
      word t.mem B (8 * Public.sMask) = mask true ∧
      Outside B 128 128 s.mem t.mem ∧ Keep [.rax] s t := by
  have hB : Scr s B 256 := by
    simpa only [off, BitVec.add_zero] using h.scr.sub (o := 0) (n := 256) h.h256 (by decide)
  have fits := candidate_arguments_fit hp hq
  refine WP.mono (headerArguments_ok _ fits hB h.rdi hsp hr hwords hsep) fun t ⟨hm, hk⟩ => ?_
  have hf : Outside B 128 128 s.mem t.mem := by
    rw [hm]; exact argumentWrites_outside _ _ _ _ fits
  have wh (k : Nat) (hk32 : k < 32) : word t.mem B (8 * k) =
      argumentWords W (fun j => word s.mem B (8 * j)) (candidateArguments pLen qLen) k := by
    rw [hm]; exact argumentWrites_word _ _ _ _ fits hk32
  have hh (d : Nat) (hd : d + 8 ≤ 128) : word t.mem B d = word s.mem B d :=
    hf.word (Or.inl hd) (by omega_using [hd])
  have stride : word t.mem B 224 = word s.mem B 224 := by
    exact wh 28 (by decide)
  have ht : Ws t B Z w := ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.rdi,
    (hh 48 (by decide)).trans h.hw, stride.trans h.hS, fun j hj => (hh (8 * sArr j) (by unfold sArr; omega_using [hj])).trans (h.harr j hj),
    h.hZ, h.w1, h.w2⟩
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hf, hk⟩
  · exact wh 16 (by decide)
  · exact wh 17 (by decide)
  · exact wh 18 (by decide)
  · exact wh 19 (by decide)
  · exact wh 20 (by decide)
  · exact wh 21 (by decide)
  · exact wh 22 (by decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Preserve p and the generator exponent across primality testing -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Impl.Bignum.X86_64

/-- A full-width native store preserves the entire arithmetic workspace. -/
theorem storeCandidateArray_ok {s : State} {B out : Addr} {Z w a ptr : Nat}
    (h : Ws s B Z w) (ha : a < 16) (hptr : ptr < 32)
    (hp : word s.mem B (8 * ptr) = out) (hl : word s.mem B 136 = BitVec.ofNat 64 (8 * w))
    (hm : word s.mem B (8 * Public.sMask) = mask true)
    (hout : ∀ i < 8 * w, InRegions s.wr (off out i) 1)
    (hsep : ∀ i < 8 * w, Z ≤ ofs B (off out i)) :
    WP isa (seqs (Impl.Rsa.X86_64.Keys.storeA a ptr 17 Public.sMask)) s fun t =>
      Spec.Rsa.bytesAt t.mem out (8 * w) = Spec.Dsa.encodeBE (8 * w) (wv s.mem B (slot w a) w) ∧
      (∀ x, (∀ i < 8 * w, x ≠ off out i) → t.mem x = s.mem x) ∧
      Ws t B Z w ∧ Frm B [(Z, 2 ^ 64)] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (storeA_ws h ha hptr (by decide : 17 < 32) hp hl hm
    (by have := h.w1; omega_using [this]) (Nat.le_refl _) hout hsep) fun t ⟨hb, hf, ht, fr, hk⟩ => ?_
  refine ⟨?_, hf, ht, fr, hk.mono (by decide)⟩
  simpa only [Spec.Rsa.bytesAt, off, VG.Proof.Dsa.encodeBE_i2osp, ite_true,
    show (8 * w + 7) / 8 = w by omega_using []] using hb

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
    WP isa Impl.Dsa.X86_64.Generation.candidateStores s fun t =>
      Spec.Rsa.bytesAt t.mem pp (8 * w) = Spec.Dsa.encodeBE (8 * w) (wv s.mem B (slot w 5) w) ∧
      Spec.Rsa.bytesAt t.mem ep (8 * w) = Spec.Dsa.encodeBE (8 * w) (wv s.mem B (slot w 0) w) ∧
      Ws t B Z w ∧ Frame [⟨pp, 8 * w⟩, ⟨ep, 8 * w⟩] s.mem t.mem ∧
      Frm B [(Z, 2 ^ 64)] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.candidateStores
  refine WP.seq (WP.mono (storeCandidateArray_ok h (by decide : 5 < 16) (by decide : 20 < 32)
    hp hl hm hpw hpo) fun u ⟨up, fu, hu, wu, ku⟩ => ?_)
  have uh : ∀ d, d + 8 ≤ Z → word u.mem B d = word s.mem B d := by
    intro d hd
    exact wu.word_eq (by simp only [List.mem_singleton]; rintro r rfl; exact Or.inl hd)
      (by have := h.scr.nowrap; omega_using [hd, this])
  have hh := h.h256
  refine WP.mono (storeCandidateArray_ok hu (by decide : 0 < 16) (by decide : 21 < 32)
    (by rw [uh 168 (by omega_using [hh])]; exact he) (by rw [uh 136 (by omega_using [hh])]; exact hl)
    (by rw [uh (8 * Public.sMask) (by unfold Public.sMask sFn; omega_using [hh])]; exact hm)
    (fun i hi => by rw [ku.2.2]; exact hew i hi) heo) fun t ⟨te, ft, ht, wt, kt⟩ => ?_
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
      have := h.sl (by decide : 0 < 16); omega_using [this])
      (by have := h.sl (by decide : 0 < 16); have := h.scr.nowrap; omega_arith)]
  · intro a ha
    rw [ft a (fun i hi heq => ha ⟨ep, 8 * w⟩ (by simp) (heq ▸
      Offset.contains_base ep hi (by have := h.w2; omega_using [hi, this]))),
      fu a (fun i hi heq => ha ⟨pp, 8 * w⟩ (by simp) (heq ▸
      Offset.contains_base pp hi (by have := h.w2; omega_using [hi, this])))]

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
    WP isa Impl.Dsa.X86_64.Generation.candidateBuild s fun t =>
      let p := Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb)
      Spec.Rsa.bytesAt t.mem pp (8 * w) = Spec.Dsa.encodeBE (8 * w) p ∧
      Spec.Rsa.bytesAt t.mem ep (8 * w) = Spec.Dsa.encodeBE (8 * w) ((p - 1) / Spec.Rsa.os2ip qb) ∧
      Ws t B Z w ∧ word t.mem B 160 = pp ∧
      Frame [⟨B, Z⟩, ⟨pp, 8 * w⟩, ⟨ep, 8 * w⟩] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Impl.Dsa.X86_64.Generation.candidateBuild
  refine WP.seq (WP.mono (candidateArithmetic_ok h hxp hxl hqp hql sx sq
    (by rw [hwidth]; have := h.w1; omega_using [this]) (by omega_using [hwidth]) hqposlen hqf hqpos hqfit)
    fun u ⟨hu, up, ue, fu, ku⟩ => ?_)
  have uh : ∀ d, d + 8 ≤ 256 → word u.mem B d = word s.mem B d := by
    intro d hd
    exact fu.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        left <;> simp only [slot, hdrBytes] <;> omega_using [hd])
      (by have := h.scr.nowrap; have := h.h256; omega_using [hd])
  refine WP.mono (candidateStores_ok hu (by rw [uh 160 (by decide)]; exact hp)
    (by rw [uh 168 (by decide)]; exact he) (by rw [uh 136 (by decide), hxl, hwidth])
    (by rw [uh (8 * Public.sMask) (by decide)]; exact hm)
    (fun i hi => by rw [ku.2.2]; exact hpw i hi)
    (fun i hi => by rw [ku.2.2]; exact hew i hi) hpo heo hpe)
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
    omega_using [hrz, hz]
  exact fs.trans (ft.mono (by simp))

end VG.Proof.Dsa.X86_64.Generation
