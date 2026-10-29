module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Arithmetic
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey

import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFrame
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Attr.Core
import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
/-! # FFDH key generation on x86-64: a generator power uses exchange's output proof -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/GenerateKey/Bridge.lean`, which only this module imported.
section

/-! # FFDH key generation on x86-64: reuse the exchange output workspace -/

section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Only the outer header's public-value and output pointers change. -/
theorem bridge_ok {s : State} {B yp gp : Addr} {Z o w : Nat} {mi : BitVec 64}
    (hc : SubCtx s B Z o w w mi)
    (hY : word s.mem B (8 * sY) = yp) (hG : word s.mem B (8 * sG) = gp) :
    WP isa (.block bridge) s fun t =>
      word t.mem B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut) = yp ∧
      word t.mem B (8 * sY) = gp ∧
      Frm B [(8 * VG.Impl.Ffdh.X86_64.Domain.sOut, 8), (8 * sY, 8)] s.mem t.mem ∧
      Keep [.rax, .rdx] s t := by
  have hZ : 256 ≤ Z := by have := hc.lo; have := hc.hi; unfold slot hdrBytes at *; omega
  have hs := hc.scr
  have hldY := hs.ld (d := 8 * sY) (by change 160 ≤ Z; omega)
  have hstO := hs.st (d := 8 * VG.Impl.Ffdh.X86_64.Domain.sOut) (by change 184 ≤ Z; omega)
  have hstY := hs.st (d := 8 * sY) (by change 160 ≤ Z; omega)
  have hldG := hs.ld (d := 8 * sG) (by change 224 ≤ Z; omega)
  let m₁ := s.mem.writeW (off B (8 * VG.Impl.Ffdh.X86_64.Domain.sOut)) yp
  let m := m₁.writeW (off B (8 * sY)) gp
  have ho := writeW_outside (d := 8 * VG.Impl.Ffdh.X86_64.Domain.sOut) s.mem B yp (by decide)
  have hy := writeW_outside (d := 8 * sY) m₁ B gp (by decide)
  have hG' : word m₁ B (8 * sG) = gp := by
    rw [ho.word (by decide) (by decide)]
    exact hG
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.mem = m) (by
    unfold bridge
    xrun [State.ea, hdr, VG.Impl.Rsa.X86_64.Crt.ws, hc.rdi, hdrOff, hc.good.scr.ld (hdr_lt_slot w 8 (show VG.Impl.Rsa.X86_64.Crt.sLink < 32 by decide)),
      hc.link, hldY, hY, hstO, hldG, hG', hstY, m, m₁]) rfl) fun t ⟨hm, k⟩ => ?_
  refine ⟨?_, ?_, ?_, k⟩
  · rw [hm, hy.word (by decide) (by decide)]
    exact word_writeW_self _ _ _ _
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro a ha
    rw [hm]
    exact (hy a (ha (8 * sY, 8) (by simp))).trans
      (ho a (ha (8 * VG.Impl.Ffdh.X86_64.Domain.sOut, 8) (by simp)))

end VG.Proof.Ffdh.X86_64.GenerateKey
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The private core's output buffer becomes exchange's output, and its
public generator becomes exchange's peer input. -/
def outputP (p : CheckPrivate.KpP) : Exchange.ExP :=
  ⟨p.B, p.Z, p.k, p.dl, p.dp, p.dom, p.yp, p.xp, p.xl, off p.dp p.k, p.gb, p.sp⟩

/-- Move only public pointers; preserve all arithmetic and the computed power. -/
theorem value_bridge {p : CheckPrivate.KpP} {xb : List Byte} {s : State}
    (h : CheckPrivate.Value p xb s) (ho : VG.Proof.Rsa.X86_64.OutOk s p.B p.Z p.yp p.k) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.bridge) s fun t =>
      Exchange.Value (outputP p) xb t ∧ InScr p.B p.Z s.mem t.mem ∧
      (∀ i < 6, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧ Keep [.rax, .rdx] s t := by
  obtain ⟨⟨mi, hb, hc, hg⟩, hy⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have hZ := hb.hZ
  refine WP.mono (bridge_ok hc.sub
    (hb.hdr (sY, p.yp) (by simp [CheckPrivate.KpP.headers])) hg)
    fun t ⟨hOut, hY, hf, k⟩ => ?_
  have hr : ∀ r ∈ [(8 * VG.Impl.Ffdh.X86_64.Domain.sOut, 8), (8 * sY, 8)],
      128 ≤ r.1 ∧ r.1 + r.2 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> decide
  have hi : InScr p.B p.Z s.mem t.mem := InScr.of_frm hf (fun r he => by have := hr r he; omega)
  have hh : ∀ i < 32, i ≠ sY → i ≠ VG.Impl.Ffdh.X86_64.Domain.sOut →
      word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi hy ho =>
    hf.word_eq (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> simp only <;> omega) (by omega)
  have hv : ∀ j < 8, wv t.mem (off p.B (inner p.w)) (slot p.w j) p.w =
      wv s.mem (off p.B (inner p.w)) (slot p.w j) p.w := by
    intro j hj
    have hs := slot_le (w := p.w) hj
    have hlo := hc.sub.lo
    have hhi := hc.sub.hi
    have hn := hb.scr.nowrap
    have h256 : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega
    refine wv_congr fun i hi => ?_
    rw [word_off, word_off]
    exact hf.word_eq (fun r he => Or.inr (by have := hr r he; omega)) (by omega)
  have hc' : ModCtx t p.B p.Z (inner p.w) p.w mi p.P :=
    ⟨hc.sub.of_parent hf hr k.2.2 (k.gpr (by decide)),
      hc.xv.of_parent hc.sub.toMem hf (fun r he => (hr r he).2),
      by rw [hv _ (by decide)]; exact hc.r2l,
      by rw [hv _ (by decide)]; exact hc.r2,
      hc.odd, hc.x1, hc.wide, hc.w2, hc.w28⟩
  have hgl : p.gb.length = p.k := by
    simp only [CheckPrivate.KpP.gb, List.length_take, List.length_drop, hb.doml]
    rcases hb.dl with hd | hd <;> rw [hd] <;> omega
  have hySrc := ((hb.dom.drop p.k).take p.k).congrK hi k
  have hb' : Exchange.Base (outputP p) xb t := by
    refine ⟨hb.k1, hb.k2, hb.dl, hb.doml, hgl, hb.xlen, hb.xl1, hb.xl2,
      hb.hZ, hb.scr.congr k.2.2, hb.dom.congrK hi k, hb.x.congrK hi k, hySrc, ?_,
      fun i hi => by rw [k.2.2]; exact ho.wr i hi, ho.sep⟩
    intro e he
    simp only [Exchange.ExP.headers, outputP, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hh sDom (by decide) (by decide) (by decide)).trans
        (hb.hdr (sDom, p.dp) (by simp [CheckPrivate.KpP.headers]))
    · exact (hh sDomLen (by decide) (by decide) (by decide)).trans
        (hb.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [CheckPrivate.KpP.headers]))
    · exact (hh sK (by decide) (by decide) (by decide)).trans
        (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers]))
    · exact hY
    · exact (hh sX (by decide) (by decide) (by decide)).trans
        (hb.hdr (sX, p.xp) (by simp [CheckPrivate.KpP.headers]))
    · exact (hh sXl (by decide) (by decide) (by decide)).trans
        (hb.hdr (sXl, BitVec.ofNat 64 p.xl) (by simp [CheckPrivate.KpP.headers]))
    · exact hOut
  exact ⟨⟨⟨mi, hb', hc'⟩, (hv aY (by decide)).trans hy⟩, hi,
    fun i hi => hh i (by omega) (by unfold sY sFn; omega)
      (by unfold VG.Impl.Ffdh.X86_64.Domain.sOut sFn; omega), k⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
