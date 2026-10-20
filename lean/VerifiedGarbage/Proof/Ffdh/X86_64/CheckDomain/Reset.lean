module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Parent

import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: restore the p workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem reset_p {p : CdP} {s : State} (h : Parent p s) (hm : p.mv = true) :
    WP isa (seqs pSetup) s fun t => ∃ mi, Work p mi t ∧ t.gpr .rdi = off p.B (inner p.w) ∧
      InScr p.B p.Z s.mem t.mem ∧ (∀ i < 32, i ≠ sWs → word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) ∧
      Keep (.rdi :: mmRegs) s t := by
  have hb := h.base
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have hn := h.outer.scr.nowrap
  have hroom := h.outer.room
  have hZ := hb.hZ
  have h256 : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega
  have h136 : 136 ≤ slot p.w 8 := by unfold slot hdrBytes; omega
  have eW : wsWords p.k = p.w := wsWords_k (by omega)
  unfold pSetup
  refine wp_seqs_append (a := wsSetup sK ++ ([.block [enter]] : List (Prog isa))) (b := modSetup sDom sK)
    (by simp [wsSetup]) (by simp [modSetup, VG.Impl.Rsa.X86_64.Crt.loadArr])
    (WP.mono (wsSetup_ok (sl := sK) (len := p.k) h.outer (by decide) (by decide)
      (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) (by omega) (by omega))
      fun u ⟨hc, _, hWs, hf, k⟩ => ?_)
  rw [eW] at hc
  have hh : ∀ i < 32, i ≠ sWs → word u.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hne => hf.word_eq (fun r he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp only <;> unfold sWs sFn at * <;> omega) (by omega)
  have hi : InScr p.B p.Z s.mem u.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sWs sFn at * <;> omega)
  have hbu : Base p u := hb.keep hi k (by
    intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact hh _ (by dsimp only; decide) (by dsimp only; decide))
  refine WP.mono (modSetup_ok hc (by omega) (Nat.le_refl _) (by omega)
    (show sDom < 32 by decide) (show sK < 32 by decide)
    (hbu.hdr (sDom, p.dp) (by simp [CdP.headers]))
    (by rw [hbu.plen]; exact hbu.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]))
    (hbu.dom.take p.k) (by rw [hbu.plen]; omega) (by rw [hbu.plen])
    (valid_facts hm hk).1) fun t ⟨mi, hc', hv, ff, kk⟩ => ?_
  have hr : ∀ r ∈ [(slot p.w aN, 8 * (p.w + 2)), (slot p.w aOne, 8 * (p.w + 2)), (8 * sMinv, 8)],
      r.1 + r.2 ≤ slot p.w 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact slot_le (by decide)
    · exact slot_le (by decide)
    · exact hdr_lt_slot p.w 8 (by decide)
  obtain ⟨hbt, hit, hht⟩ := hbu.child hc (L := slot p.w 8) (by omega) ff hr kk
  refine ⟨mi, ⟨hbt, hc'.toMem, hv, ?_, ?_, ?_⟩, hc'.rdi, hi.trans hit, ?_, keep_trans k (kk.mono (by decide))⟩
  · rw [hht _ (by decide)]; exact hWs
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.g
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.q
  · intro i hi hne
    rw [hht i hi, hh i hi hne]

end VG.Proof.Ffdh.X86_64.CheckDomain
