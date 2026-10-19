module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT

meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.MinusCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.FrontCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Body
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Flags
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Minus
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.MinusCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OddCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QRangeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.R2CT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reset
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Subgroup
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupRun
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Body
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Divides
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Flags
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Math
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Minus
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OddCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QPrepareCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.QRangeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.R2CT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reset
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Subgroup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupRun
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Scan
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # FFDH domain validation on x86-64: testing the shared reduction -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (aXc)

private theorem zero_keep (p : CdP) (s : State) (h : QResidue p s) :
    WP isa (seqs (isZero aXc)) s (QResidue p) := by
  obtain ⟨⟨mi, hw, hm, hdl, hq⟩, hr⟩ := h
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  have h2 : 2 ≤ p.wq := Nat.le_max_left _ _
  have hwq : p.wq ≤ p.w := by unfold CdP.wq CdP.nq wsWords; omega
  refine WP.mono (ltArr_ok hw.ctx.good (Nat.le_refl _) (by omega) (by omega)
    (show aXc < 8 by decide) (show aOne < 8 by decide)) fun t ⟨_, hmem, k⟩ => ?_
  refine ⟨⟨mi, hw.keep hmem k (k.gpr (by decide)), hm, hdl, hq⟩, ?_⟩
  obtain ⟨mi', hw', hz⟩ := hr
  exact ⟨mi', hw'.keep hmem k (k.gpr (by decide)), by rw [hmem]; exact hz⟩

private theorem tested (p : CdP) (s : State) (h : QResidue p s) :
    WP isa (seqs (isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa)))) s (QDivided p) :=
  WP.mono (residue_test h.2) fun _ ⟨⟨⟨mi, hw, _⟩, hz⟩, _⟩ =>
    ⟨⟨mi, hw, h.1.choose_spec.2⟩, hz⟩

theorem test_q_ct : RelCT isa (Two QResidue)
    (seqs (isZero aXc ++ ([.block [.alu .test .rax (.reg .rax)]] : List (Prog isa)))) (Two QDivided) := by
  refine two_post ?_ tested
  refine RelCT.seqs_append (by simp [isZero, ltArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two QResidue) ?_ ?_)
  · simpa only [isZero] using
      (two_post (two_map (fun p : CdP => p.qx.ws) (fun _ _ h => by
        obtain ⟨mi, hw, _⟩ := h.1
        exact ⟨mi, hw.ctx.good, Nat.le_refl _⟩)
        (ltArr_ct (a := aXc) (b := aOne) (by decide) (by decide) (by taint_decide))) zero_keep)
  · exact two_taint [] (pins_nil _) (by taint_decide)

end VG.Proof.Ffdh.X86_64.CheckDomain
