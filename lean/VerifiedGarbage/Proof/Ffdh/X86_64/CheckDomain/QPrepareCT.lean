module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reduce
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reduce
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: public reduction workspace -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev CdP.qx (p : CdP) : XPub := ⟨p.B, p.Z, inner p.w, p.w, p.wq⟩
abbrev CdP.qm (p : CdP) : MPub := ⟨p.B, p.Z, p.w, p.nq, p.eqp⟩

def ScanReady (p : CdP) (s : State) : Prop := Scanned p s ∧ p.mv = true ∧ p.dl = 3 * p.k ∧ p.qr

def BeforeQ (p : CdP) (s : State) : Prop := ScanReady p s ∧ wv s.mem p.B (slot p.w aX) p.w = p.P - 1

def QData (p : CdP) (s : State) : Prop := ∃ mi, QWork p mi s ∧ p.mv = true ∧ p.dl = 3 * p.k ∧ p.qr

def QResidue (p : CdP) (s : State) : Prop := QData p s ∧ Residue p s

def QDivided (p : CdP) (s : State) : Prop := QData p s ∧ s.zf = some (!decide ((p.P - 1) % p.Q = 0))

theorem beforeQ_m1 (p : CdP) (s : State) (h : BeforeQ p s) : M1 sEp sEl p.qm s := by
  have hb := h.1.1.parent.base
  have hk := hb.k1
  have hk' := hb.k2
  have hl := hb.qlen h.1.2.2.1
  have hne : p.qb ≠ [] := by intro he; simp [he] at hl; omega
  have hld : p.ld < p.k := by have := lead_lt hne; change lead p.qb < p.k; omega
  have hew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have hnl : p.eqb.length = p.nq := by simp only [CdP.eqb, List.length_drop, hl]
  exact ⟨p.eqb, h.1.1.parent.outer, h.1.1.el, h.1.1.ep, ((hb.dom.drop (2 * p.k)).take p.k).drop p.ld,
    hnl, show 1 ≤ p.nq by unfold CdP.nq; omega, show p.nq ≤ 8 * p.w by unfold CdP.nq; omega,
    by rw [os2ip_drop_lead p.qb]; exact h.1.2.2.2.1⟩

theorem beforeQ_data (p : CdP) (s : State) (h : BeforeQ p s) :
    WP isa (seqs (wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl)) s (QData p) :=
  WP.mono (setup_order h.1.1 h.1.2.2.1 h.1.2.2.2.1 h.2) fun _ ⟨⟨mi, hw⟩, _⟩ =>
    ⟨mi, hw, h.1.2.1, h.1.2.2⟩

theorem qdata_rpre (p : CdP) (s : State) (h : QData p s) : RPre aX p.qx s := by
  obtain ⟨mi, hw, _, _, hq⟩ := h
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have h2 : 2 ≤ p.wq := Nat.le_max_left _ _
  have hwq : p.wq ≤ p.w := by unfold CdP.wq CdP.nq wsWords; omega
  exact ⟨mi, p.Q, hw.ctx, hw.xv, h2, hwq, show p.w < 2 ^ 30 by omega, hq.2.1, by decide⟩

theorem qdata_residue (M : Mont) (p : CdP) (s : State) (h : QData p s) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.redc M.mm aX)) s (QResidue p) := by
  obtain ⟨mi, hw, hm, hdl, hq⟩ := h
  exact WP.mono (reduce_order M hw hq.1 hq.2.1) fun _ ⟨hr, _⟩ => by
    obtain ⟨mi', hw', hz⟩ := hr
    exact ⟨⟨mi', hw', hm, hdl, hq⟩, mi', hw', hz⟩

theorem prepare_q_ct : RelCT isa (Two BeforeQ)
    (seqs (wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl)) (Two QData) :=
  two_post (two_map CdP.qm beforeQ_m1
    (wsMod_ct (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) beforeQ_data

theorem reduce_q_ct (M : Mont) : RelCT isa (Two QData)
    (seqs (VG.Impl.Rsa.X86_64.Crt.redc M.mm aX)) (Two QResidue) :=
  two_post (two_map CdP.qx qdata_rpre (redc_ct_X M)) (qdata_residue M)

end VG.Proof.Ffdh.X86_64.CheckDomain
