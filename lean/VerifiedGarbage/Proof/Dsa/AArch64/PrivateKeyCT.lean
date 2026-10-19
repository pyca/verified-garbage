module
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Add
import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Dsa.AArch64.Call2
import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.EqualCT
import VerifiedGarbage.Proof.Dsa.AArch64.EqualHead
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Dsa.AArch64.Minus
import VerifiedGarbage.Proof.Dsa.AArch64.MinusCore
import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
import VerifiedGarbage.Proof.Dsa.AArch64.Power
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.Reduce
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.AArch64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroHead
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Spec.RsaPss
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Add
meta import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
meta import VerifiedGarbage.Proof.Dsa.AArch64.Call2
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.AArch64.EqualCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.EqualHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.Masks
meta import VerifiedGarbage.Proof.Dsa.AArch64.Minus
meta import VerifiedGarbage.Proof.Dsa.AArch64.MinusCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Power
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Reduce
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceReadCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceStepCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MdStream.Spec
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Spec.RsaPss

/-! # Constant time of private-key consistency and nonce validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem privateKey_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p)
    (hx : ∀ p, (Core.privateScalar, p.layout.qLen) ∈ inputs p)
    (hk : ∀ p, (Core.nonce, p.layout.qLen) ∈ inputs p) :
    RelCT isa (Two (ScheduleState inputs)) (Checks.privateKey M.mm)
      (Two (ScheduleState inputs)) := by
  have pp (p : SchedulePublic) : 1 ≤ p.layout.pLen := by have := p.layout.widths; omega
  have qp (p : SchedulePublic) : 1 ≤ p.layout.qLen := p.layout.widths.1
  have qb (p : SchedulePublic) : p.layout.qLen ≤ 1024 := by have := p.layout.widths; omega
  have pf (p : SchedulePublic) : (p.layout.pLen + 7) / 8 ≤ ModulusSide.p.words p.layout := Nat.le_refl _
  have qf (p : SchedulePublic) : (p.layout.qLen + 7) / 8 ≤ ModulusSide.q.words p.layout := Nat.le_refl _
  have h1 := scheduleRange_ct inputs stable .q Core.privateScalar (fun p => p.layout.qLen) false
    (by simp [pointerFits, Core.privateScalar]) (by simp [stablePointer, Core.privateScalar]) qp qf (by taint_decide)
  have h2 := scheduleRange_ct inputs stable .q Core.nonce (fun p => p.layout.qLen) false
    (by simp [pointerFits, Core.nonce]) (by simp [stablePointer, Core.nonce]) qp qf (by taint_decide)
  have h3 := schedulePow_ct M inputs stable .p t Core.generator Core.privateScalar
    (fun p => p.layout.pLen) (fun p => p.layout.qLen)
    (by simp [pointerFits, Core.generator]) (by simp [pointerFits, Core.privateScalar])
    (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.privateScalar])
    pp pf qp qb (by decide) (by decide) (element_space (by decide)) (by taint_decide)
  have h4 := scheduleEqual_ct inputs stable (Core.element t) Core.publicValue (fun p => p.layout.pLen) false
    (by change t < 2 ^ 16; decide) (by simp [pointerFits, Core.publicValue])
    (by simp [stablePointer, Core.element]) (by simp [stablePointer, Core.publicValue]) (by decide)
    pp (by intro p; have := p.layout.widths; omega) (by taint_decide)
  unfold Checks.privateKey seqs
  refine RelCT.seq (two_map (Φ := ScheduleState inputs) (fun p => p)
    (fun p st h => ⟨h, (h.2.1 _ (hx p)).active⟩) h1) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h => ⟨h, (h.2.1 _ (hk p)).active⟩) h2) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h, (h.2.1 _ (hg p)).active, (h.2.1 _ (hx p)).active⟩) h3) ?_
  exact two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p),
      (h.1.2.1 _ (hy p)).active⟩) h4

end VG.Proof.Dsa.AArch64
