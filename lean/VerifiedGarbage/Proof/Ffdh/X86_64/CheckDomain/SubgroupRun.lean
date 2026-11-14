module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Subgroup
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Parent
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves

/-! ### `Ffdh.X86_64.CheckDomain.Reset`, which only this module used -/

section

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
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  have hn := h.outer.scr.nowrap
  have hroom := h.outer.room
  have hZ := hb.hZ
  have h256 : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega_using []
  have h136 : 136 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_using []
  have eW : wsWords p.k = p.w := wsWords_k (by omega_using [hk])
  unfold pSetup
  refine wp_seqs_append (a := wsSetup sK ++ ([.block [enter]] : List (Prog isa))) (b := modSetup sDom sK)
    (by simp [wsSetup]) (by simp [modSetup, VG.Impl.Rsa.X86_64.Crt.loadArr])
    (WP.mono (wsSetup_ok (sl := sK) (len := p.k) h.outer (by decide) (by decide)
      (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])) (by omega_using [hk]) (by omega_using [ew]))
      fun u ⟨hc, _, hWs, hf, k⟩ => ?_)
  rw [eW] at hc
  have hh : ∀ i < 32, i ≠ sWs → word u.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hne => hf.word_eq (fun r he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp only <;> unfold sWs sFn at * <;> omega_arith) (by omega_using [hi])
  have hi : InScr p.B p.Z s.mem u.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> unfold sWs sFn at * <;> omega_arith)
  have hbu : Base p u := hb.keep hi k (by
    intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact hh _ (by dsimp only; decide) (by dsimp only; decide))
  refine WP.mono (modSetup_ok hc (by omega_using [hk, ew]) (Nat.le_refl _) (by omega_using [hk', ew])
    (show sDom < 32 by decide) (show sK < 32 by decide)
    (hbu.hdr (sDom, p.dp) (by simp [CdP.headers]))
    (by rw [hbu.plen]; exact hbu.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]))
    (hbu.dom.take p.k) (by rw [hbu.plen]; omega_using [hk]) (by rw [hbu.plen])
    (valid_facts hm hk).1) fun t ⟨mi, hc', hv, ff, kk⟩ => ?_
  have hr : ∀ r ∈ [(slot p.w aN, 8 * (p.w + 2)), (slot p.w aOne, 8 * (p.w + 2)), (8 * sMinv, 8)],
      r.1 + r.2 ≤ slot p.w 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact slot_le (by decide)
    · exact slot_le (by decide)
    · exact hdr_lt_slot p.w 8 (by decide)
  obtain ⟨hbt, hit, hht⟩ := hbu.child hc (L := slot p.w 8) (by omega_using [hroom]) ff hr kk
  refine ⟨mi, ⟨hbt, hc'.toMem, hv, ?_, ?_, ?_⟩, hc'.rdi, hi.trans hit, ?_, keep_trans k (kk.mono (by decide))⟩
  · rw [hht _ (by decide)]; exact hWs
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.g
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.q
  · intro i hi hne
    rw [hht i hi, hh i hi hne]

end VG.Proof.Ffdh.X86_64.CheckDomain

end

end


/-! # FFDH domain validation on x86-64: the complete subgroup check -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

theorem order_leave {p : CdP} {mi : BitVec 64} {s : State} (h : QWork p mi s) :
    WP isa (.block [leave]) s (StepPost p s (Scanned p)) := by
  have hk := h.base.k1
  have hk' := h.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_using []
  refine WP.mono (leave_ok h.ctx) fun t ⟨hd, hm, k⟩ => ?_
  have hb := h.base.keep (by rw [hm]; exact InScr.refl _ _ _) k (fun _ _ => by rw [hm])
  have hc := h.ctx.toMem.congr hm k.2.2
  have ho := Outer.of_mem hc hd (room_k hk h.base.hZ) (by omega_using [hk, ew]) (by omega_using [hk', ew])
  exact ⟨⟨⟨hb, ho, by rw [hm]; exact h.g, by rw [hm]; exact h.q⟩,
      by rw [hm]; exact h.ep, by rw [hm]; exact h.el⟩,
    by rw [hm]; exact InScr.refl _ _ _, (fun _ _ => by rw [hm]), k.mono (by decide)⟩

theorem scanned_reset {p : CdP} {s : State} (h : Scanned p s) (hm : p.mv = true) :
    WP isa (seqs pSetup) s (StepPost p s fun t => ∃ mi, Work p mi t ∧
      t.gpr .rdi = off p.B (inner p.w) ∧ word t.mem p.B (8 * sEp) = p.eqp ∧
      word t.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq) :=
  WP.mono (reset_p h.parent hm) fun t ⟨mi, hw, hd, hi, hh, k⟩ =>
    ⟨⟨mi, hw, hd, (hh _ (by decide) (by decide)).trans h.ep,
      (hh _ (by decide) (by decide)).trans h.el⟩, hi,
      (fun i hi => hh i (by omega_using [hi]) (by unfold sWs sFn; omega_using [hi])), k⟩

private theorem subgroup_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code) =
      .block [leave] :: (pSetup ++ (.seq (.block r2Head) R.code ::
        (pow M.mm E.code sG sK sEp sEl ++ (isOne aY ++ ([.block [leave]] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup, List.append_assoc, List.cons_append, List.nil_append]

theorem subgroup_ok (M : Mont) (E : CrtExpL M) (R : R2Impl M) {p : CdP} {mi : BitVec 64} {s : State}
    (h : QWork p mi s) (hm : p.mv = true) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code))) s
      (StepPost p s fun t => t.gpr .rdi = p.B ∧ t.gpr .rax = bit (p.G ^ p.Q % p.P = 1)) := by
  rw [subgroup_eq]
  refine wp_seqs_cons (by simp [pSetup]) (WP.mono (order_leave h) fun u₁ S₁ => ?_)
  refine wp_seqs_append (a := pSetup) (by simp [pSetup]) (by simp)
    (WP.mono (scanned_reset S₁.1 hm) fun u₂ S₂ => ?_)
  obtain ⟨mi', hw₂, hd₂, hep₂, hel₂⟩ := S₂.1
  refine wp_seqs_cons (by simp [pow])
    (WP.mono (subgroup_r2 M R hw₂ hd₂ hm hep₂ hel₂) fun u₃ S₃ => ?_)
  refine wp_seqs_append (a := pow M.mm E.code sG sK sEp sEl) (by simp [pow]) (by simp [isOne, eqArr])
    (WP.mono (subgroup_power M E S₃.1 hq) fun u₄ S₄ => ?_)
  exact WP.mono (subgroup_finish S₄.1.1 S₄.1.2) fun _ S₅ => (((S₁.trans S₂).trans S₃).trans S₄).trans S₅

end VG.Proof.Ffdh.X86_64.CheckDomain
