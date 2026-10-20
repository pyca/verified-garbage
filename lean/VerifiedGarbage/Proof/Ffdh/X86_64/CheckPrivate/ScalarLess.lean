module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Flags
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH private-key validation on x86-64: scalar upper bounds -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem ltP_work {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} (h : Work p xb mi s)
    (hd : s.gpr .rdi = off p.B (inner p.w)) (ho : p.P % 2 = 1) :
    WP isa (seqs (ltP aXm)) s (StepPost p s fun t => Work p xb mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ t.gpr .rax = bit (Spec.Rsa.os2ip xb < p.P - 1) ∧
      word t.mem (off p.B (inner p.w)) (8 * sF) = word s.mem (off p.B (inner p.w)) (8 * sF)) := by
  have hc := h.mem.ctx hd
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  have hn := hc.good.scr.nowrap
  have hT := slot_le (w := p.w) (show aTmp < 8 by decide)
  have hT0 := hdr_lt_slot p.w aTmp (show 31 < 32 by decide)
  refine WP.mono (ltP_ok hc.good (Nat.le_refl _) (by omega) (by omega)
    (show aXm < 8 by decide) (by decide)) fun t ⟨ha, hfo, k⟩ => ?_
  have hf : Frm (off p.B (inner p.w)) [(slot p.w aTmp, 8 * p.w)] s.mem t.mem := Frm.of_outside hfo (by simp)
  rw [h.x, h.xv.n] at ha
  have ha' : t.gpr .rax = bit (Spec.Rsa.os2ip xb < p.P - 1) := by
    simpa only [bit, lt_pm1 ho (Spec.Rsa.os2ip xb)] using ha
  have hr : ∀ r ∈ [(slot p.w aTmp, 8 * p.w)], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot p.w 8 := by
    simp only [List.mem_singleton]
    rintro r rfl
    exact ⟨by omega, by omega⟩
  have hsep : ∀ {j}, j < 8 → aTmp ≠ j → ∀ r ∈ [(slot p.w aTmp, 8 * p.w)],
      r.1 + r.2 ≤ slot p.w j ∨ slot p.w j + 8 * (p.w + 2) ≤ r.1 := fun hj hne r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_sep (w := p.w) hne
    omega
  obtain ⟨hw, hi, hs⟩ := h.child hd hf hr (hsep (by decide) (by decide))
    (hsep (by decide) (by decide)) (hsep (by decide) (by decide)) k
  refine ⟨⟨hw, (k.gpr (by decide)).trans hd, ha', ?_⟩, hi, hs, k.mono (by decide)⟩
  apply hf.word_eq
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact Or.inl (hdr_lt_slot p.w aTmp (show sF < 32 by decide))
  · have := hdr_lt_slot p.w 8 (show sF < 32 by decide); omega

theorem loadQ_work {p : KpP} {xb : List Byte} {mi : BitVec 64} {s : State} (h : Work p xb mi s)
    (hd : s.gpr .rdi = off p.B (inner p.w)) (hdl : p.dl = 3 * p.k) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.loadArr aY sQ sK)) s
      (StepPost p s fun t => Work p xb mi t ∧ t.gpr .rdi = off p.B (inner p.w) ∧
        wv t.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.Q ∧
        word t.mem (off p.B (inner p.w)) (8 * sF) = word s.mem (off p.B (inner p.w)) (8 * sF)) := by
  have hc := h.mem.ctx hd
  have hb := h.base
  have hk := hb.k1
  have hk' := hb.k2
  have hlen : p.qb.length = p.k := by simp only [KpP.qb, List.length_take, List.length_drop, hb.doml, hdl]; omega
  have hsQ : Src s p.B p.Z (off p.dp (2 * p.k)) p.qb := (hb.dom.drop (2 * p.k)).take p.k
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  refine WP.mono (primeLoad_ok hc (by omega) (Nat.le_refl _) (by omega) (show aY < 8 by decide)
    (show sQ < 32 by decide) (show sK < 32 by decide) h.hQ
    (by rw [hlen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])) hsQ
    (by rw [hlen]; omega) (by rw [hlen]; omega) (by rw [hlen])) fun t ⟨_, hy, hf, k⟩ => ?_
  have ff : Frm (off p.B (inner p.w)) [(slot p.w aY, 8 * (p.w + 2))] s.mem t.mem := Frm.of_outside hf (by simp)
  have hY := slot_le (w := p.w) (show aY < 8 by decide)
  have hY0 := hdr_lt_slot p.w aY (show 31 < 32 by decide)
  have hr : ∀ r ∈ [(slot p.w aY, 8 * (p.w + 2))], 8 * 17 ≤ r.1 ∧ r.1 + r.2 ≤ slot p.w 8 := by
    simp only [List.mem_singleton]
    rintro r rfl
    exact ⟨by omega, hY⟩
  have hsep : ∀ {j}, j < 8 → aY ≠ j → ∀ r ∈ [(slot p.w aY, 8 * (p.w + 2))],
      r.1 + r.2 ≤ slot p.w j ∨ slot p.w j + 8 * (p.w + 2) ≤ r.1 := fun _ hne r hr => by
    rw [List.mem_singleton.mp hr]
    exact slot_sep hne
  obtain ⟨hw, hi, hs⟩ := h.child hd ff hr (hsep (by decide) (by decide))
    (hsep (by decide) (by decide)) (hsep (by decide) (by decide)) k
  refine ⟨⟨hw, (k.gpr (by decide)).trans hd, hy, ?_⟩, hi, hs, k.mono (by decide)⟩
  apply ff.word_eq
  · intro r hr
    rw [List.mem_singleton.mp hr]
    exact Or.inl (hdr_lt_slot p.w aY (show sF < 32 by decide))
  · have := hc.good.scr.nowrap
    have := hdr_lt_slot p.w 8 (show sF < 32 by decide)
    omega

end VG.Proof.Ffdh.X86_64.CheckPrivate
