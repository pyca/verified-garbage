module
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.StagesCT

import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OddCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.OddCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Work
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
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
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
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
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Minus
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reduce
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reset
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Subgroup
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.SubgroupRun
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
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
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Reduce
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

/-! # FFDH domain validation on x86-64: subgroup range in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def QInner (p : CdP) (s : State) : Prop := Inner p s ∧ p.dl = 3 * p.k

def QChecked (p : CdP) (s : State) : Prop := QInner p s ∧ s.zf = some (!decide p.qr)

theorem qinner_load (p : CdP) (s : State) (h : QInner p s) : LPre aXm sQ sK p.ql s := by
  obtain ⟨⟨mi, hw, hd, _⟩, hq⟩ := h
  have hb := hw.base
  have hk := hb.k1
  have hk' := hb.k2
  have hl := hb.qlen hq
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  exact ⟨mi, p.qb, hw.mem.ctx hd, show 2 ≤ p.w by omega, Nat.le_refl _, show p.w < 2 ^ 30 by omega,
    by decide, by decide, by decide, hw.q,
    by rw [hl]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hl, (hb.dom.drop (2 * p.k)).take p.k, by rw [hl]; omega,
    by rw [hl]; omega, by rw [hl]⟩

private theorem qinner_loaded (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.loadArr aXm sQ sK)) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  exact WP.mono (load_order hw hd hq) fun _ ⟨⟨hw', hd', _⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hq⟩

private theorem qinner_ranged (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs (range aXm)) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  exact WP.mono (component_range hw hd rfl) fun _ ⟨⟨hw', hd', _⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hq⟩

private theorem qinner_odd (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs (isOdd aXm)) s (QInner p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  have hk := hw.base.k1
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  exact WP.mono (isOdd_ok (hw.mem.ctx hd).good (Nat.le_refl _) (by omega) (show aXm < 8 by decide))
    fun _ ⟨_, hmem, k⟩ => ⟨⟨mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm⟩, hq⟩

private theorem qinner_checked (p : CdP) (s : State) (h : QInner p s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange) s (QChecked p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hq⟩ := h
  exact WP.mono (order_range hw hd hq) fun _ ⟨⟨hw', hd', hz⟩, _⟩ => ⟨⟨⟨mi, hw', hd', hm⟩, hq⟩, hz⟩

theorem qrange_ct : RelCT isa (Two QInner)
    (seqs VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange) (Two QChecked) := by
  refine two_post ?_ qinner_checked
  unfold VG.Impl.Ffdh.X86_64.Domain.CheckDomain.qRange
  simp only [List.append_assoc]
  refine RelCT.seqs_append (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr]) (by simp [range, gt1, ltArr, cmpArr])
    (RelCT.seq (R := Two QInner)
      (two_post (two_map CdP.ql qinner_load (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) qinner_loaded) ?_)
  refine RelCT.seqs_append (by simp [range, gt1, ltArr, cmpArr]) (by simp [isOdd])
    (RelCT.seq (R := Two QInner)
      (two_post (two_map CdP.ws (fun p s h => inner_good p s h.1)
        (range_ct (a := aXm) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide))) qinner_ranged) ?_)
  refine RelCT.seqs_append (by simp [isOdd]) (by simp)
    (RelCT.seq (R := Two QInner)
      (two_post (two_map CdP.ws (fun p s h => inner_good p s h.1) odd_ct) qinner_odd) ?_)
  exact two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w))
    fun _ _ ⟨⟨_, _, hd, _⟩, _⟩ => hd) (by taint_decide)

end VG.Proof.Ffdh.X86_64.CheckDomain
