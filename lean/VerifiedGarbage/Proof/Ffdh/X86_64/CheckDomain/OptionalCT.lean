module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QRangeCT

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.DividesCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QRangeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.DividesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: optional-order control flow -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

def Optional (p : CdP) (s : State) : Prop := ∃ mi,
  Work p mi s ∧ s.gpr .rdi = p.B ∧ p.mv = true ∧ s.zf = some (decide (p.dl = 2 * p.k))

theorem checked_optional (p : CdP) (s : State) (h : GeneratorChecked p s ∧ isa.eval .e s = some false) :
    WP isa (.block (leave :: qTest)) s (Optional p) := by
  obtain ⟨⟨⟨mi, hw, hd, hm⟩, _⟩, _⟩ := h
  have hb := hw.base
  have hk := hb.k1
  have hk' := hb.k2
  have hdl := hb.dl
  exact WP.mono (leaveQ_ok (hw.mem.ctx hd)
    (hb.hdr (sDomLen, BitVec.ofNat 64 p.dl) (by simp [CdP.headers]))
    (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]))
    (by rcases hdl with h | h <;> omega) (by rcases hdl with h | h <;> omega))
    fun _ ⟨hd', _, hz, hmem, k⟩ => ⟨mi, hw.keep hmem k, hd', hm, hz⟩

theorem optional_inner (p : CdP) (s : State) (h : Optional p s ∧ isa.eval .e s = some false) :
    WP isa (.block [enter]) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm, hz⟩, he⟩ := h
  have hn : ¬p.dl = 2 * p.k := by
    have hb : decide (p.dl = 2 * p.k) = false := by simpa only [eval, hz, Option.some.injEq] using he
    exact of_decide_eq_false hb
  have hq : p.dl = 3 * p.k := by rcases hw.base.dl with h | h <;> omega
  exact WP.mono (hw.enter hd) fun _ ⟨hw', hd', _⟩ => ⟨⟨mi, hw', hd', hm⟩, hq⟩

private theorem withQ_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code) =
      .block [enter] :: (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange ++
        ([.ite .e (retInner 0) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code)))] : List (Prog isa))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ, List.cons_append, List.nil_append]

theorem optional_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two fun p s => Optional p s ∧ isa.eval .e s = some false)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.withQ M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  rw [withQ_eq]
  refine seqs_cons_ct (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange, VG.Impl.Rsa.X86_64.Crt.loadArr])
    (RelCT.seq (R := Two QInner)
      (two_piece [.rdi] (pins_rdiB CdP.B fun _ _ h => h.1.choose_spec.2.1)
        (by taint_decide) optional_inner) ?_)
  refine RelCT.seqs_append
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange, VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp)
    (RelCT.seq (R := Two QChecked) qrange_ct ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2])
    (two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ h => h.1.1.1.choose_spec.2.1) (by taint_decide)) ?_
  exact two_map id qchecked_start (divides_ct M E R hE)

end VG.Proof.Ffdh.X86_64.CheckDomain
