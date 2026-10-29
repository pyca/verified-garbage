module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateArithmetic
public import VerifiedGarbage.Proof.Rsa.Ranges
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Double
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateReduction
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import Mathlib.Tactic.Widget.Calc
/-! # The byte-to-integer bridge for p-candidate arithmetic -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/ReductionExponent.lean`, which only this module imported.
section

/-! # Candidate reduction also produces the generator exponent -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Proof.Rsa VG.Proof.Dsa.Generation

theorem reduceExponent_ok {s : State} {B : Addr} {Z w x q : Nat}
    (h : Ws s B Z w) (hx : wv s.mem B (slot w 0) w = x)
    (hq : wv s.mem B (slot w 2) w = 2 * q) (hqpos : 0 < q) :
    WP isa (.seq Impl.Dsa.X86_64.Generation.reduceCandidate
      (Impl.Dsa.X86_64.Generation.doubleArray 0)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w 5) w = x + 1 - x % (2 * q) ∧
      wv t.mem B (slot w 0) w = (x + 1 - x % (2 * q) - 1) / q ∧
      Frm B [ar w 4, ar w 0, ar w 1, ar w 3, ar w 5] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hxlt : x < 2 ^ (64 * w) := hx ▸ wv_lt s.mem B (slot w 0) w
  have he : 2 * (x / (2 * q)) ≤ x := by
    calc
      2 * (x / (2 * q)) ≤ q * (2 * (x / (2 * q))) := Nat.le_mul_of_pos_left _ hqpos
      _ = 2 * q * (x / (2 * q)) := by ac_rfl
      _ ≤ x := Nat.mul_div_le x (2 * q)
  refine WP.seq (WP.mono (reduceCandidate_ok h hx hq hqpos) fun u ⟨hu, hp, hquot, hf, hk⟩ => ?_)
  refine WP.mono (doubleArray_ok hu (by decide : 0 < 16) (by rw [hquot]; omega))
    fun t ⟨ht, ho, kt⟩ => ?_
  have ft : Frm B [ar w 0] u.mem t.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  have wt := hu.congr ft (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kt (by decide)
  refine ⟨wt, ?_, ?_, ?_, (hk.trans kt).mono (by decide)⟩
  · rw [ft.wv_eq (by
      simp only [List.mem_singleton]; rintro r rfl
      simp only [slot, hdrBytes]; omega) (by have := h.sl (by decide : 5 < 16); have := h.scr.nowrap; omega), hp]
  · rw [ht, hquot, pReduction_generatorExponent x hqpos]
  · exact hf.trans (ft.mono (by simp))

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Rsa.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 VG.Impl.Bignum.X86_64 VG.Proof.Rsa

/-- Padded loads preserve the arithmetic header and every other array. -/
theorem loadCandidateArray_ok {s : State} {B p : Addr} {Z w a ptr len : Nat} {bs : List Byte}
    (h : Ws s B Z w) (ha : a < 16) (hptr : ptr < 32) (hlen : len < 32)
    (hp : word s.mem B (8 * ptr) = p) (hl : word s.mem B (8 * len) = BitVec.ofNat 64 bs.length)
    (src : Src s B Z p bs) (hpos : 1 ≤ bs.length) (hfit : bs.length ≤ 8 * w) :
    WP isa (seqs (Impl.Rsa.X86_64.Keys.loadA a ptr len)) s fun t =>
      Ws t B Z w ∧ wv t.mem B (slot w a) w = Spec.Rsa.os2ip bs ∧
      Frm B [ar w a] s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (loadA_ok h ha hptr hlen hp hl src rfl hpos hfit) fun t ⟨hv, ho, hk⟩ => ?_
  have hf : Frm B [ar w a] s.mem t.mem := Frm.of_outside ho (by simp [ar])
  exact ⟨h.congr hf (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) hk (by decide),
    hv, hf, hk.mono (by decide)⟩

theorem candidateArithmetic_ok {s : State} {B xp qp : Addr} {Z w : Nat} {xb qb : List Byte}
    (h : Ws s B Z w)
    (hxp : word s.mem B 128 = xp) (hxl : word s.mem B 136 = BitVec.ofNat 64 xb.length)
    (hqp : word s.mem B 144 = qp) (hql : word s.mem B 152 = BitVec.ofNat 64 qb.length)
    (sx : Src s B Z xp xb) (sq : Src s B Z qp qb)
    (hxpos : 1 ≤ xb.length) (hxf : xb.length ≤ 8 * w)
    (hqposlen : 1 ≤ qb.length) (hqf : qb.length ≤ 8 * w)
    (hqpos : 0 < Spec.Rsa.os2ip qb) (hqfit : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * w)) :
    WP isa Impl.Dsa.X86_64.Generation.candidateArithmetic s fun t =>
      Ws t B Z w ∧
      wv t.mem B (slot w 5) w = Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb) ∧
      wv t.mem B (slot w 0) w =
        (Spec.Rsa.os2ip xb + 1 - Spec.Rsa.os2ip xb % (2 * Spec.Rsa.os2ip qb) - 1) / Spec.Rsa.os2ip qb ∧
      Frm B [ar w 0, ar w 1, ar w 2, ar w 3, ar w 4, ar w 5] s.mem t.mem ∧ Keep mmRegs s t := by
  change WP isa (.seq (seqs (Impl.Rsa.X86_64.Keys.loadA 0 16 17))
    (.seq (seqs (Impl.Rsa.X86_64.Keys.loadA 2 18 19))
      (.seq (Impl.Dsa.X86_64.Generation.doubleArray 2)
        (.seq Impl.Dsa.X86_64.Generation.reduceCandidate (Impl.Dsa.X86_64.Generation.doubleArray 0))))) s _
  refine WP.seq (WP.mono (loadCandidateArray_ok h (by decide : 0 < 16) (by decide : 16 < 32)
    (by decide : 17 < 32) hxp hxl sx hxpos hxf) fun u ⟨hu, ux, fu, ku⟩ => ?_)
  have uh : ∀ d, d + 8 ≤ 256 → word u.mem B d = word s.mem B d := by
    intro d hd
    exact fu.word_eq (by simp only [List.mem_singleton]; rintro r rfl; simp [slot, hdrBytes]; omega)
      (by have := h.scr.nowrap; have := h.h256; omega)
  have squ : Src u B Z qp qb := sq.congrK (fun a ha => fu a (by
    simp only [List.mem_singleton]; rintro r rfl
    have := h.sl (by decide : 0 < 16)
    dsimp only at *
    omega)) ku
  refine WP.seq (WP.mono (loadCandidateArray_ok hu (by decide : 2 < 16) (by decide : 18 < 32)
    (by decide : 19 < 32) (by rw [uh 144 (by decide)]; exact hqp)
    (by rw [uh 152 (by decide)]; exact hql) squ hqposlen hqf) fun v ⟨hv, vq, fv, kv⟩ => ?_)
  refine WP.seq (WP.mono (doubleArray_ok hv (by decide : 2 < 16) (by rw [vq]; exact hqfit))
    fun z ⟨zq, ho, kz⟩ => ?_)
  have fz : Frm B [ar w 2] v.mem z.mem :=
    Frm.of_outside (ho.mono (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [ar])
  have hz := hv.congr fz (fun r hr => by
    rcases List.mem_singleton.mp hr with rfl; exact Mut.ofSlot _ _ _) kz (by decide)
  have zx : wv z.mem B (slot w 0) w = Spec.Rsa.os2ip xb := by
    have sep : ∀ r ∈ [ar w 2], slot w 0 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w 0 := by
      simp only [List.mem_singleton]; rintro r rfl; left; simp only [slot, hdrBytes]; omega
    have room : slot w 0 + 8 * w ≤ 2 ^ 64 := by
      have := h.sl (by decide : 0 < 16); have := h.scr.nowrap; omega
    rw [fz.wv_eq sep room, fv.wv_eq sep room, ux]
  change WP isa (.seq Impl.Dsa.X86_64.Generation.reduceCandidate
    (Impl.Dsa.X86_64.Generation.doubleArray 0)) z _
  refine WP.mono (reduceExponent_ok hz zx (by rw [zq, vq]) hqpos) fun t ⟨ht, tp, te, ft, kt⟩ => ?_
  exact ⟨ht, tp, te, (fu.append (fv.append (fz.append ft))).mono (by simp),
    (((ku.trans kv).trans kz).trans kt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64.Generation
