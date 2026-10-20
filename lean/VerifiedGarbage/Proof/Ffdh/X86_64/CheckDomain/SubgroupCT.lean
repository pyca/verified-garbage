module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupStagesCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.R2CT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupStagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.R2CT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH domain validation on x86-64: subgroup exponentiation in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (leave)

private theorem subgroup_eq (M : Mont) (E : CrtExpL M) (R : R2Impl M) :
    VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code) =
      .block [leave] :: (pSetup ++ (.seq (.block r2Head) R.code ::
        (pow M.mm E.code sG sK sEp sEl ++ (isOne aY ++ ([.block [leave]] : List (Prog isa)))))) := by
  simp only [VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup, List.append_assoc, List.cons_append, List.nil_append]

private theorem finish_ct : RelCT isa (Two Powered) (seqs (isOne aY ++ ([.block [leave]] : List (Prog isa))))
    fun _ _ => True := by
  refine RelCT.seqs_append (by simp [isOne, eqArr]) (by simp)
    (RelCT.seq (R := Two fun (p : CdP) s => GoodW p.ws s) ?_ ?_)
  · simpa only [isOne] using two_post
      (two_map CdP.ws powered_good (eqArr_ct (a := aY) (b := aOne) (by decide) (by decide) (by taint_decide)))
      (fun p s h => by
        obtain ⟨⟨mi, hr, _⟩, _⟩ := h
        exact WP.mono (eqArr_ok hr.ctx.sub.good (Nat.le_refl _)
          (by have := hr.ctx.w2; omega) (by have := hr.ctx.w28; omega)
          (show aY < 8 by decide) (show aOne < 8 by decide)) fun _ ⟨_, hm, k⟩ =>
            GoodW.keep ⟨mi, hr.ctx.sub.good, Nat.le_refl _⟩ hm (k.gpr (by decide)) k.2.2)
  · exact two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ ⟨_, hg, _⟩ => hg.rdi) (by taint_decide)

private theorem reset_ct : RelCT isa (Two ScanReady) (seqs pSetup) (Two PStart) := by
  simpa only [pSetup] using two_post (two_map CdP.pm scanready_pm
    (wsMod_ct (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))) scanready_start

theorem subgroup_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sEp sEl) :
    RelCT isa (Two QData)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.CheckDomain.subgroup M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  rw [subgroup_eq]
  refine seqs_cons_ct (by simp [pSetup]) (RelCT.seq (R := Two ScanReady)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
      fun _ _ ⟨_, hw, _⟩ => hw.ctx.rdi) (by taint_decide) qdata_leave) ?_)
  refine RelCT.seqs_append (by simp [pSetup]) (by simp)
    (RelCT.seq (R := Two PStart)
      reset_ct ?_)
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (R := Two Ready)
    (two_post (two_map id (fun _ _ h => h.1) (r2_ct M R)) (start_ready M R)) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp [isOne, eqArr])
    (RelCT.seq (R := Two Powered)
      (two_post (two_map CdP.pw ready_ps0
        (pow_ct M E (loadArr_ct (by decide) (by taint_decide) (by taint_decide)) hE
          (by taint_decide) (by taint_decide) (by taint_decide))) (ready_powered M E)) ?_)
  exact finish_ct

end VG.Proof.Ffdh.X86_64.CheckDomain
