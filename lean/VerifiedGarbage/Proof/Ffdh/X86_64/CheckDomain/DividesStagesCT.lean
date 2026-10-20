module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QRangeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ScanCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH domain validation on x86-64: public stages before reduction -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev CdP.qs (p : CdP) : ScanPub := ⟨p.B, p.Z, p.w, off p.dp (2 * p.k), p.qb⟩

def DivStart (p : CdP) (s : State) : Prop := QInner p s ∧ p.qr

def DivOuter (p : CdP) (s : State) : Prop := Parent p s ∧ p.mv = true ∧ p.dl = 3 * p.k ∧ p.qr

theorem qchecked_start (p : CdP) (s : State) (h : QChecked p s ∧ isa.eval .e s = some false) : DivStart p s := by
  refine ⟨h.1.1, ?_⟩
  have he : (!decide p.qr) = false := by simpa only [eval, h.1.2, Option.some.injEq] using h.2
  exact of_decide_eq_true (by simpa only [Bool.not_eq_false'] using he)

theorem divstart_leave (p : CdP) (s : State) (h : DivStart p s) :
    WP isa (.block [VG.Impl.Rsa.X86_64.Crt.leave]) s (DivOuter p) := by
  obtain ⟨⟨⟨mi, hw, hd, hm⟩, hdl⟩, hq⟩ := h
  exact WP.mono (prime_leave hw hd) fun _ ⟨hp, _⟩ => ⟨hp, hm, hdl, hq⟩

theorem divouter_scan (p : CdP) (s : State) (h : DivOuter p s) : ScanPre sQ p.qs s := by
  have hl := h.1.base.qlen h.2.2.1
  have hk := h.1.base.k1
  have hk' := h.1.base.k2
  have hne : p.qb ≠ [] := by intro he; simp [he] at hl; omega
  exact ⟨h.1.outer, h.1.q,
    by rw [hl]; exact h.1.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hne, show p.qb.length < 2 ^ 32 by rw [hl]; omega,
    (h.1.base.dom.drop (2 * p.k)).take p.k, by decide⟩

theorem divouter_scanned (p : CdP) (s : State) (h : DivOuter p s) :
    WP isa (seqs (scan sQ)) s (ScanReady p) :=
  WP.mono (scan_order h.1 h.2.2.1) fun _ ⟨hs, _⟩ => ⟨hs, h.2⟩

theorem scanready_minus (p : CdP) (s : State) (h : ScanReady p s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1) s (BeforeQ p) :=
  WP.mono (scanned_minus h.1 (valid_facts h.2.1 h.1.parent.base.k1).1)
    fun _ ⟨⟨hs, hx⟩, _⟩ => ⟨⟨hs, h.2⟩, hx⟩

end VG.Proof.Ffdh.X86_64.CheckDomain
