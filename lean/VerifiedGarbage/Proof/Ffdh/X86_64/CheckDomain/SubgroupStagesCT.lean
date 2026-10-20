module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Subgroup
public import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT

meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QTestCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupRun
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain

/-! # FFDH domain validation on x86-64: public subgroup exponentiation stages -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev CdP.pm (p : CdP) : MPub := ⟨p.B, p.Z, p.w, p.k, p.dp⟩
abbrev CdP.pw (p : CdP) : PowPub := ⟨p.x, off p.dp p.k, p.k, p.eqp, p.nq⟩

def PStart (p : CdP) (s : State) : Prop := Inner p s ∧ p.dl = 3 * p.k ∧
  word s.mem p.B (8 * sEp) = p.eqp ∧ word s.mem p.B (8 * sEl) = BitVec.ofNat 64 p.nq

def Ready (p : CdP) (s : State) : Prop := ∃ mi, PReady p mi s ∧ p.dl = 3 * p.k

def Powered (p : CdP) (s : State) : Prop := Ready p s ∧
  wv s.mem (off p.B (inner p.w)) (slot p.w aY) p.w = p.G ^ p.Q % p.P

theorem qdata_leave (p : CdP) (s : State) (h : QData p s) :
    WP isa (.block [VG.Impl.Rsa.X86_64.Crt.leave]) s (ScanReady p) := by
  obtain ⟨mi, hw, hm, hdl, hq⟩ := h
  exact WP.mono (order_leave hw) fun _ ⟨hs, _⟩ => ⟨hs, hm, hdl, hq⟩

theorem scanready_pm (p : CdP) (s : State) (h : ScanReady p s) : M1 sDom sK p.pm s := by
  have hb := h.1.parent.base
  have hk := hb.k1
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  exact ⟨p.pb, h.1.parent.outer, hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hb.hdr (sDom, p.dp) (by simp [CdP.headers]), hb.dom.take p.k, hb.plen,
    show 1 ≤ p.k by omega, show p.k ≤ 8 * p.w by omega, (valid_facts h.2.1 hk).1⟩

theorem scanready_start (p : CdP) (s : State) (h : ScanReady p s) : WP isa (seqs pSetup) s (PStart p) :=
  WP.mono (scanned_reset h.1 h.2.1) fun _ ⟨⟨mi, hw, hd, hep, hel⟩, _⟩ =>
    ⟨⟨mi, hw, hd, h.2.1⟩, h.2.2.1, hep, hel⟩

theorem start_ready (M : Mont) (R : R2Impl M) (p : CdP) (s : State) (h : PStart p s) :
    WP isa (.seq (.block r2Head) R.code) s (Ready p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hdl, hep, hel⟩ := h
  exact WP.mono (subgroup_r2 M R hw hd hm hep hel) fun _ ⟨hr, _⟩ => ⟨mi, hr, hdl⟩

theorem ready_ps0 (p : CdP) (s : State) (h : Ready p s) : PS0 sG sK sEp sEl p.pw s := by
  obtain ⟨mi, hr, hq⟩ := h
  have hb := hr.base
  have hk := hb.k1
  have hk' := hb.k2
  have hl := hb.qlen hq
  have hne : p.qb ≠ [] := by intro he; simp [he] at hl; omega
  have hld : p.ld < p.k := by have := lead_lt hne; change lead p.qb < p.k; omega
  have hnl : p.eqb.length = p.nq := by simp only [CdP.eqb, List.length_drop, hl]
  have hp := ps0_of hr.ctx (bp := sG) (bl := sK) (ep := sEp) (el := sEl)
    (pb := off p.dp p.k) (pe := p.eqp) (bb := p.gb) (eb := p.eqb)
    (by decide) (by decide) (by decide) (by decide) hr.g
    (by rw [hb.glen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]))
    ((hb.dom.drop p.k).take p.k) (by rw [hb.glen]; omega) (by rw [hb.glen]) hr.ep
    (by rw [hnl]; exact hr.el) (((hb.dom.drop (2 * p.k)).take p.k).drop p.ld)
    (by rw [hnl]; unfold CdP.nq; omega) (by rw [hnl]; unfold CdP.nq; omega)

  simpa only [hb.glen, hnl] using hp

theorem ready_powered (M : Mont) (E : CrtExpL M) (p : CdP) (s : State) (h : Ready p s) :
    WP isa (seqs (pow M.mm E.code sG sK sEp sEl)) s (Powered p) := by
  obtain ⟨mi, hr, hq⟩ := h
  exact WP.mono (subgroup_power M E hr hq) fun _ ⟨⟨hr', hy⟩, _⟩ => ⟨⟨mi, hr', hq⟩, hy⟩

theorem powered_good (p : CdP) (s : State) (h : Powered p s) : GoodW p.ws s := by
  obtain ⟨⟨mi, hr, _⟩, _⟩ := h
  exact ⟨mi, hr.ctx.sub.good, Nat.le_refl _⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
