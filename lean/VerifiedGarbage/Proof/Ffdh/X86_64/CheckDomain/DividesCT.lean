module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.DividesStagesCT
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QTestCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.MinusCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.DividesStagesCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QTestCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.MinusCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: divisibility in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave redc aXc)

private theorem divides_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code) =
      .block [leave] :: (scan sQ ++ (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1 ++
        ((wsSetup sEl ++ ([.block [enter]] : List (Prog isa)) ++ modSetup sEp sEl) ++
          (redc M.mm aX ++ ((isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa))) ++
            ([.ite .e (retInner 0) (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code)))] : List (Prog isa))))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides, List.append_assoc, List.cons_append, List.nil_append]

theorem divides_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two DivStart)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.divides M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  rw [divides_eq]
  refine seqs_cons_ct (by simp [scan]) (RelCT.seq (R := Two DivOuter)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ ⟨⟨⟨_, _, hd, _⟩, _⟩, _⟩ => hd) (by taint_decide) divstart_leave) ?_)
  refine RelCT.seqs_append (by simp [scan]) (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1])
    (RelCT.seq (R := Two ScanReady)
      (two_post (two_map CdP.qs divouter_scan (scan_ct (by taint_decide) (by taint_decide))) divouter_scanned) ?_)
  refine RelCT.seqs_append (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.pMinus1]) (by simp [wsSetup])
    (RelCT.seq (R := Two BeforeQ)
      (two_post (two_map id (fun _ _ h => h.1.parent) minus_ct) scanready_minus) ?_)
  refine RelCT.seqs_append
    (by simp [wsSetup]) (by simp [redc])
    (RelCT.seq (R := Two QData) prepare_q_ct ?_)
  refine RelCT.seqs_append (by simp [redc]) (by simp [isZero, ltArr, cmpArr])
    (RelCT.seq (R := Two QResidue) (reduce_q_ct M) ?_)
  refine RelCT.seqs_append (by simp [isZero, ltArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two QDivided) test_q_ct ?_)
  simp only [seqs]
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2])
    (two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ h => h.1.1.choose_spec.1.ctx.rdi) (by taint_decide)) ?_
  exact two_map id (fun _ _ h => h.1.1) (subgroup_ct M E R hE)

end VG.Proof.Ffdh.X86_64.CheckDomain
