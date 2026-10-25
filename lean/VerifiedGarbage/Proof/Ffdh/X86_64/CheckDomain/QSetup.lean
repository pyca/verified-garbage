module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Scan
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup

/-! # FFDH domain validation on x86-64: q's reduction workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure QWork (p : CdP) (mi : BitVec 64) (s : State) : Prop where
  base : Base p s
  ctx : SubCtx s p.B p.Z (inner p.w) p.w p.wq mi
  xv : XVals s p.B (inner p.w) p.wq mi p.Q
  ep : word s.mem p.B (8 * sEp) = p.eqp
  el : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq
  g : word s.mem p.B (8 * sG) = off p.dp p.k
  q : word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)
  x : wv s.mem p.B (slot p.w aX) p.w = p.P - 1

theorem setup_order {p : CdP} {s : State} (h : Scanned p s) (hq : p.dl = 3 * p.k)
    (ho : p.Q % 2 = 1) (hx : wv s.mem p.B (slot p.w aX) p.w = p.P - 1) :
    WP isa (seqs (wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl)) s
      (StepPost p s fun t => ∃ mi, QWork p mi t) := by
  have hb := h.parent.base
  have hO := h.parent.outer
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega_arith
  have hl := hb.qlen hq
  have hne : p.qb ≠ [] := by intro he; simp [he] at hl; omega_arith
  have hld : p.ld < p.k := by have := lead_lt hne; change lead p.qb < p.k; omega_arith
  have hnl : p.eqb.length = p.nq := by simp only [CdP.eqb, List.length_drop, hl]
  have heq : Spec.Rsa.os2ip p.eqb = p.Q := os2ip_drop_lead p.qb
  have h2 : 2 ≤ p.wq := Nat.le_max_left _ _
  have hwq : p.wq ≤ p.w := by unfold CdP.wq CdP.nq wsWords; have := hO.w2; omega_arith
  have hZ := hb.hZ
  have hInner : slot p.w 8 ≤ inner p.w := Nat.le_refl _
  have h256 : 256 ≤ slot p.wq 8 := by unfold slot hdrBytes; omega_arith
  have hn := hO.scr.nowrap
  have hroom := hO.room
  have hX := slot_le (w := p.w) (show aX < 8 by decide)
  refine wp_seqs_append (a := wsSetup sEl ++ ([.block [enter]] : List (Prog isa))) (b := modSetup sEp sEl)
    (by simp [wsSetup]) (by simp [modSetup, VG.Impl.Rsa.X86_64.Crt.loadArr])
    (WP.mono (wsSetup_ok (sl := sEl) (len := p.nq) hO (by decide) (by decide) h.el
      (by unfold CdP.nq; omega_arith) (by unfold CdP.nq; omega_arith)) fun u ⟨hc, _, _, hf, k⟩ => ?_)
  change SubCtx u p.B p.Z (inner p.w) p.w p.wq _ at hc
  have hh : ∀ i < 32, i ≠ sWs → word u.mem p.B (8 * i) = word s.mem p.B (8 * i) :=
    fun i hi hne => hf.word_eq (fun r he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp only; unfold sWs sFn at *; omega_arith
      · simp only; have : 256 ≤ inner p.w := by simp only [inner, slot, hdrBytes]; omega_arith
        omega_arith) (by omega_arith)
  have hi : InScr p.B p.Z s.mem u.mem := InScr.of_frm hf (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · simp only; unfold sWs sFn; omega_arith
    · simp only; have : 136 ≤ slot p.w 8 := by unfold slot hdrBytes; omega_arith
      omega_arith)
  have hbu : Base p u := hb.keep hi k (by
    intro e he
    simp only [CdP.headers, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact hh _ (by dsimp only; decide) (by dsimp only; decide))
  have hxu : wv u.mem p.B (slot p.w aX) p.w = p.P - 1 := by
    rw [hf.wv_eq (fun r he => ?_) (by omega_arith), hx]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Or.inr (hdr_lt_slot p.w aX (show sWs < 32 by decide))
    · exact Or.inl (by omega_arith)
  have hsrc : Src u p.B p.Z p.eqp p.eqb := ((hbu.dom.drop (2 * p.k)).take p.k).drop p.ld
  refine WP.mono (modSetup_ok hc h2 hwq hO.w28 (show sEp < 32 by decide) (show sEl < 32 by decide)
    ((hh _ (by decide) (by decide)).trans h.ep)
    (by rw [hnl]; exact (hh _ (by decide) (by decide)).trans h.el) hsrc
    (by rw [hnl]; unfold CdP.nq; omega_arith)
    (by rw [hnl]; exact Nat.le_max_right _ _) (by rw [heq]; exact ho)) fun t ⟨mi, hc', hv, ff, kk⟩ => ?_
  rw [heq] at hv
  have hr : ∀ r ∈ [(slot p.wq aN, 8 * (p.wq + 2)), (slot p.wq aOne, 8 * (p.wq + 2)), (8 * sMinv, 8)],
      r.1 + r.2 ≤ slot p.wq 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact slot_le (by decide)
    · exact slot_le (by decide)
    · exact hdr_lt_slot p.wq 8 (by decide)
  have hL : inner p.w + slot p.wq 8 ≤ p.Z := by have := hc.hi; omega_arith
  obtain ⟨hbt, hit, hht⟩ := hbu.child hc hL ff hr kk
  have hx' : wv t.mem p.B (slot p.w aX) p.w = p.P - 1 := by
    rw [ff.wv_below hr (by omega_arith) (by have := hc.hi; omega_arith)
      (by omega_arith), hxu]
  refine ⟨⟨mi, ⟨hbt, hc', hv, ?_, ?_, ?_, ?_, hx'⟩⟩, hi.trans hit, ?_, keep_trans k (kk.mono (by decide))⟩
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.ep
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.el
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.parent.g
  · rw [hht _ (by decide), hh _ (by decide) (by decide)]; exact h.parent.q
  · intro i hi
    rw [hht i (by omega_arith), hh i (by omega_arith) (by unfold sWs sFn; omega_arith)]

end VG.Proof.Ffdh.X86_64.CheckDomain
