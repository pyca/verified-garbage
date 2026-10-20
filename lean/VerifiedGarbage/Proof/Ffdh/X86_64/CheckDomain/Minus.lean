module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Parent
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
import VerifiedGarbage.Proof.Ffdh.WordPred
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH domain validation on x86-64: p minus one -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (zeroArr)

theorem minus_one {p : CdP} {s : State} (h : Parent p s) (ho : p.P % 2 = 1) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1) s
      (StepPost p s fun t => Parent p t ∧ wv t.mem p.B (slot p.w aX) p.w = p.P - 1 ∧
        (∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i))) := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have hX := slot_le (w := p.w) (show aX < 8 by decide)
  have hX0 := hdr_lt_slot p.w aX (show 31 < 32 by decide)
  have hZ := h.good.2
  have hn := h.outer.scr.nowrap
  have arrFrame : ∀ {u v : State} (hu : Parent p u),
      Outside p.B (slot p.w aX) (8 * (p.w + 2)) u.mem v.mem → Keep mmRegs u v →
      Parent p v ∧ InScr p.B p.Z u.mem v.mem ∧
        (∀ i < 32, word v.mem p.B (8 * i) = word u.mem p.B (8 * i)) := by
    intro u v hu hf k
    have ff : Frm p.B [(slot p.w aX, 8 * (p.w + 2))] u.mem v.mem := Frm.of_outside hf (by simp)
    exact hu.array ff (fun r he => by
      rw [List.mem_singleton.mp he]; exact ⟨by omega, by omega⟩) k (k.gpr (by decide))
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1
  simp only [seqs]
  refine WP.seq (WP.mono (zeroArr_ok h.good.1 hZ (by omega) (by omega) (show aX < 8 by decide))
    fun u₁ ⟨_, ho₁, k₁⟩ => ?_)
  obtain ⟨h₁, hi₁, hh₁⟩ := arrFrame h ho₁ k₁
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx]
    (Q := fun u => u.gpr .rsi = p.dp ∧ u.gpr .rcx = BitVec.ofNat 64 p.k ∧
      u.gpr .rbx = off p.B (slot p.w aX) ∧ u.mem = u₁.mem)
    (by xrun [State.ea, hdr, h₁.outer.rdi, hdrOff, h₁.outer.ld (show sDom < 32 by decide),
      h₁.outer.ld (show sK < 32 by decide), h₁.outer.ld (show sArr aX < 32 by decide),
      h₁.base.hdr (sDom, p.dp) (by simp [CdP.headers]),
      h₁.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]), h₁.outer.harr aX (by decide)]) rfl)
    fun u₂ ⟨⟨hsi₂, hcx₂, hbx₂, hm₂⟩, k₂⟩ => ?_)
  have h₂ := h₁.keep hm₂ k₂ (k₂.gpr (by decide))
  have hsrc := h₂.base.dom.take p.k
  refine WP.seq (WP.mono (loadBE_ok h₂.outer.scr hsi₂ hcx₂ hbx₂ h.base.plen
    (by omega) (by omega) rfl (by omega)
    (fun i hi => hsrc.rd i (by rw [h.base.plen]; exact hi))
    (fun i hi => hsrc.val i _)
    (fun i hi => Or.inr (by have := hsrc.out i (by rw [h.base.plen]; exact hi); omega)))
    fun u₃ ⟨hP₃, ho₃, k₃⟩ => ?_)
  have k₃' : Keep mmRegs u₂ u₃ := k₃.mono (by decide)
  obtain ⟨h₃, hi₃, hh₃⟩ := arrFrame h₂ (ho₃.mono (Nat.le_refl _) (by omega)) k₃'
  have hbx₃ : u₃.gpr .rbx = off p.B (slot p.w aX) := (k₃.gpr (by decide)).trans hbx₂
  refine WP.mono (WP.keep [.rax]
    (Q := fun t => t.mem = u₃.mem.writeW (off p.B (slot p.w aX)) (word u₃.mem p.B (slot p.w aX) - 1))
    (by xrun [State.ea, at0, hbx₃,
      show off p.B (slot p.w aX) + BitVec.ofInt 64 0 = off p.B (slot p.w aX) from by simp,
      h₃.outer.scr.ld (show slot p.w aX + 8 ≤ p.Z by omega),
      h₃.outer.scr.st (show slot p.w aX + 8 ≤ p.Z by omega)]) rfl)
    fun t ⟨hm, k⟩ => ?_
  have hw := writeW_outside u₃.mem p.B (d := slot p.w aX) (word u₃.mem p.B (slot p.w aX) - 1) (by omega)
  rw [← hm] at hw
  have kk : Keep mmRegs u₃ t := k.mono (by decide)
  obtain ⟨ht, hit, hht⟩ := arrFrame h₃ (hw.mono (Nat.le_refl _) (by omega)) kk
  have hi : InScr p.B p.Z s.mem t.mem := hi₁.trans (by rw [hm₂] at hi₃; exact hi₃.trans hit)
  have hh : ∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i) := fun i hi => by
    rw [hht i hi, hh₃ i hi, hm₂, hh₁ i hi]
  refine ⟨⟨ht, ?_, hh⟩, hi, fun i hi => hh i (by omega),
    keep_trans (keep_trans (keep_trans (k₁.mono (by decide)) (k₂.mono (by decide)))
      (k₃'.mono (by decide))) (kk.mono (by decide))⟩
  rw [hm, wv_dec _ _ (by omega) (by rw [hP₃]; exact ho) (by omega), hP₃]

end VG.Proof.Ffdh.X86_64.CheckDomain
