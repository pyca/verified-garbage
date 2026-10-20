module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup

import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import VerifiedGarbage.Proof.Framework.Contract

/-! # FFDH domain validation on x86-64: generator subgroup relation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

structure PReady (p : CdP) (mi : BitVec 64) (s : State) : Prop where
  base : Base p s
  ctx : ModCtx s p.B p.Z (inner p.w) p.w mi p.P
  ep : word s.mem p.B (8 * sEp) = p.eqp
  el : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq
  g : word s.mem p.B (8 * sG) = off p.dp p.k

theorem subgroup_r2 (M : Mont) (R : R2Impl M) {p : CdP} {mi : BitVec 64} {s : State}
    (h : Work p mi s) (hd : s.gpr .rdi = off p.B (inner p.w)) (hm : p.mv = true)
    (hep : word s.mem p.B (8 * sEp) = p.eqp) (hel : word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq) :
    WP isa (.seq (.block r2Head) R.code) s (StepPost p s (PReady p mi)) := by
  have hc := h.mem.ctx hd
  refine WP.mono (r2_ctx M R hc h.xv hm h.base.k1 h.base.k2 h.base.hZ) fun t ⟨hc', hf, k⟩ => ?_
  change Frm (off p.B (inner p.w)) (r2Ranges p.w) s.mem t.mem at hf
  have hr : ∀ r ∈ r2Ranges p.w, r.1 + r.2 ≤ slot p.w 8 + tabBytes p.w 32 :=
    fun r he => by have := r2Ranges_le p.w r he; omega
  have hwide : inner p.w + (slot p.w 8 + tabBytes p.w 32) ≤ p.Z := by
    have hw : inner p.w + slot p.w 8 + tabBytes p.w 32 ≤ p.Z := hc'.wide
    omega
  obtain ⟨hb, hi, hh⟩ := h.base.child (wx := p.w) (mi := mi) (rs := r2Ranges p.w) (L := slot p.w 8 + tabBytes p.w 32) hc hwide hf hr k
  exact ⟨⟨hb, hc', (hh _ (by decide)).trans hep, (hh _ (by decide)).trans hel,
    (hh _ (by decide)).trans h.g⟩, hi, fun i hi => hh i (by omega), k.mono (by decide)⟩

theorem subgroup_power (M : Mont) (E : CrtExpL M) {p : CdP} {mi : BitVec 64} {s : State}
    (h : PReady p mi s) (hq : p.dl = 3 * p.k) :
    WP isa (seqs (pow M.mm E.code sG sK sEp sEl)) s (StepPost p s fun t =>
      PReady p mi t ∧ wv t.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.G ^ p.Q % p.P) := by
  have hb := h.base
  have hk := hb.k1
  have hk' := hb.k2
  have hl := hb.qlen hq
  have hne : p.qb ≠ [] := by intro he; simp [he] at hl; omega
  have hld : p.ld < p.k := by have := lead_lt hne; change lead p.qb < p.k; omega
  have hnl : p.eqb.length = p.nq := by simp only [CdP.eqb, List.length_drop, hl]
  have heq : Spec.Rsa.os2ip p.eqb = p.Q := os2ip_drop_lead p.qb
  refine WP.mono (pow_ok M E h.ctx (bp := sG) (bl := sK) (ep := sEp) (el := sEl)
    (pb := off p.dp p.k) (pe := p.eqp) (bb := p.gb) (eb := p.eqb)
    (by decide) (by decide) (by decide) (by decide) h.g
    (by rw [hb.glen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]))
    ((hb.dom.drop p.k).take p.k) (by rw [hb.glen]; omega) (by rw [hb.glen]) h.ep
    (by rw [hnl]; exact h.el) (((hb.dom.drop (2 * p.k)).take p.k).drop p.ld)
    (by rw [hnl]; unfold CdP.nq; omega) (by rw [hnl]; unfold CdP.nq; omega))
    fun t ⟨hc, hy, hf, k⟩ => ?_
  change Frm (off p.B (inner p.w)) (powRanges p.w) s.mem t.mem at hf
  have hr := fun r he => (powRanges_ok p.w r he).2
  have hwide : inner p.w + (slot p.w 8 + tabBytes p.w 32) ≤ p.Z := by
    have hw := h.ctx.wide
    omega
  obtain ⟨hb', hi, hh⟩ := hb.child (wx := p.w) (mi := mi) (rs := powRanges p.w) (L := slot p.w 8 + tabBytes p.w 32) h.ctx.sub hwide hf hr k
  rw [heq] at hy
  exact ⟨⟨⟨hb', hc, (hh _ (by decide)).trans h.ep, (hh _ (by decide)).trans h.el,
    (hh _ (by decide)).trans h.g⟩, hy⟩, hi, fun i hi => hh i (by omega), k.mono (by decide)⟩

theorem subgroup_finish {p : CdP} {mi : BitVec 64} {s : State}
    (h : PReady p mi s) (hy : wv s.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.G ^ p.Q % p.P) :
    WP isa (seqs (isOne aY ++ ([.block [leave]] : List (Prog isa)))) s (StepPost p s fun t =>
      t.gpr .rdi = p.B ∧ t.gpr .rax = bit (p.G ^ p.Q % p.P = 1)) := by
  refine wp_seqs_append (a := isOne aY) (by simp [isOne, eqArr]) (by simp)
    (WP.mono (eqArr_ok h.ctx.sub.good (Nat.le_refl _) (by have := h.ctx.w2; omega) (by have := h.ctx.w28; omega)
      (show aY < 8 by decide) (show aOne < 8 by decide)) fun u ⟨ha, hm, k⟩ => ?_)
  rw [hy, h.ctx.xv.one] at ha
  have hc := (h.ctx.sub.toMem.congr hm k.2.2).ctx ((k.gpr (by decide)).trans h.ctx.sub.rdi)
  simp only [seqs]
  refine WP.mono (leave_ok hc) fun t ⟨hd, hm', kk⟩ => ?_
  exact ⟨⟨hd, (kk.gpr (by decide)).trans ha⟩, by rw [hm', hm]; exact InScr.refl _ _ _,
    (fun _ _ => by rw [hm', hm]), keep_trans (k.mono (by decide)) (kk.mono (by decide))⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
