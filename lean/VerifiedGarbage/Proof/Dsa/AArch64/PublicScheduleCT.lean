module
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.AArch64.PublicFinishCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicFinishCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicCalls
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Encoding
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
import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPower
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
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
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroHead
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Dsa.Digest
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicPower
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroHead
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.Digest
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

/-! # Constant time of DSA domain and public-key validation -/

/-! # Preserving the public subgroup order through DSA validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The input q is the public subgroup order, including its allocated width. -/
def PublicKeyPre (inputs : SchedulePublic → List (Operand × Nat)) (p : SchedulePublic) (s : State) : Prop :=
  ScheduleState inputs p s ∧ ∃ qb : List Byte,
    OperandBytes s p.layout.base usedBytes ⟨.input .q, .qLen⟩ qb ∧
    qb.length = p.layout.qLen ∧ Spec.Dsa.decodeBE qb = p.layout.subgroup

theorem publicPrefix_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p) :
    RelCT isa (Two (ScheduleState inputs)) (seqs (Checks.publicPrefix M.mm)) (Two (ScheduleState inputs)) := by
  have pp (p : SchedulePublic) : 1 ≤ p.layout.pLen := by have := p.layout.widths; omega
  have qp (p : SchedulePublic) : 1 ≤ p.layout.qLen := p.layout.widths.1
  have pf (p : SchedulePublic) : (p.layout.pLen + 7) / 8 ≤ ModulusSide.p.words p.layout := Nat.le_refl _
  have h1 := scheduleRange_ct inputs stable .p Core.generator (fun p => p.layout.pLen) true
    (by simp [pointerFits, Core.generator]) (by simp [stablePointer, Core.generator]) pp pf (by taint_decide)
  have h2 := scheduleRange_ct inputs stable .p Core.publicValue (fun p => p.layout.pLen) true
    (by simp [pointerFits, Core.publicValue]) (by simp [stablePointer, Core.publicValue]) pp pf (by taint_decide)
  have h3 := scheduleMinus_ct inputs stable .p 1 t (by decide)
    (fun p => Nat.le_of_lt p.pGreater) (by decide) (by decide) (element_space (by decide))
    (by taint_decide) (by taint_decide)
  have h4 := scheduleReduce_ct M inputs stable u (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 16; decide) (by simp [stablePointer, Core.element])
    (by intro p; have := p.layout.widths; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide)
  have h5 := scheduleZero_ct inputs stable (Core.scalar u) (fun p => p.layout.qLen) false
    (by change u < 2 ^ 16; decide) (by simp [stablePointer, Core.scalar]) (by decide)
    qp (by intro p; have := p.layout.widths; omega) (by taint_decide)
  have h6 := scheduleMinus_ct inputs stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega)
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  unfold Checks.publicPrefix seqs
  refine RelCT.seq (two_map (Φ := ScheduleState inputs) (fun p => p)
    (fun p st h => ⟨h, (h.2.1 _ (hg p)).active⟩) h1) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h => ⟨h, (h.2.1 _ (hy p)).active⟩) h2) ?_
  refine RelCT.seq h3 ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h, h.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) h4) ?_
  refine RelCT.seq (two_map (fun p => p) (fun p st h =>
    ⟨h.1, h.1.1.availableLocal .q u (by decide) (scalar_space (by decide) p)⟩) h5) ?_
  exact h6

theorem publicPrefix_known_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (hg : ∀ p, (Core.generator, p.layout.pLen) ∈ inputs p)
    (hy : ∀ p, (Core.publicValue, p.layout.pLen) ∈ inputs p) :
    RelCT isa (Two (PublicKeyPre inputs)) (seqs (Checks.publicPrefix M.mm)) (Two (PublicKeyPre inputs)) := by
  refine two_post (two_map (fun p => p) (fun _ _ h => h.1) ((publicPrefix_ct M inputs stable hg hy).mono (fun _ _ h => h) (fun _ _ _ => trivial))) ?_
  intro p s ⟨hs, qb, hqb, hql, hqv⟩
  obtain ⟨gb, hgb, hgl⟩ := hs.2.1 _ (hg p)
  obtain ⟨yb, hyb, hyl⟩ := hs.2.1 _ (hy p)
  obtain ⟨valid, hm⟩ := hs.2.2
  refine WP.mono (publicPrefix_ok M hs.1 p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits
    hgb hyb hqb hgl hyl hm) fun t ⟨hr, hmask, hq, hf, hk⟩ => ?_
  refine ⟨⟨hr, ?_, hmask⟩, qb, hq, hql, hqv⟩
  intro a ha
  obtain ⟨bs, hbs, hlen⟩ := hs.2.1 a ha
  exact ⟨bs, hs.1.preserveExternal hr hf hk (stable p a ha).1 (stable p a ha).2 hbs, hlen⟩

/-- The subgroup exponent's bytes are fixed by its public value and width. -/
theorem publicSubgroup_ct (M : Mont) (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer)
    (a : Operand) (ha : pointerFits a.pointer) (hpa : stablePointer a.pointer)
    (hin : ∀ p, (a, p.layout.pLen) ∈ inputs p)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0])
      (.block (callHead a ⟨.input .q, .qLen⟩ (Core.element t) pWorkspace)) hc).isSome = true) :
    RelCT isa (Two (PublicKeyPre inputs))
      (Core.publicPow M.mm pWorkspace a ⟨.input .q, .qLen⟩ (Core.element t))
      (Two (PublicKeyPre inputs)) := by
  let pub (p : SchedulePublic) : ReadyCallPublic .p t :=
    scheduleCallPublic .p t (fun p => p.layout.pLen) (fun p => p.layout.qLen)
      (by intro p; have := p.layout.widths; omega) (fun _ => Nat.le_refl _)
      (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega)
      (by decide) (element_space (by decide)) p
  refine two_post (two_map (fun p => (pub p, Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup)) ?_
    (PublicPower.readyPublicPow_ct M .p t a ⟨.input .q, .qLen⟩ ha (by trivial) hpa (by change Field.q ≠ .mask; decide) (by decide) hT)) ?_
  · intro p s ⟨hs, qb, hqb, hql, hqv⟩
    obtain ⟨ab, hab, hal⟩ := hs.2.1 _ (hin p)
    have he : Spec.Dsa.encodeBE p.layout.qLen p.layout.subgroup = qb := by
      rw [← hql, ← hqv, VG.Proof.Dsa.encodeBE_decodeBE]
    rw [he]
    exact ⟨⟨hs.1, ab, qb, hab.active, hqb.active, hal, hql⟩, hqb.active, hql⟩
  · intro p s ⟨hs, qb, hqb, hql, hqv⟩
    obtain ⟨ab, hab, hal⟩ := hs.2.1 _ (hin p)
    refine WP.mono (readyPublicPow_ok M hs.1 .p p.pGreater p.pOdd a ⟨.input .q, .qLen⟩ ha (by trivial)
      hab.active hqb.active (by rw [hal]; have := p.layout.widths; omega)
      (by rw [hal]; exact Nat.le_refl _) (by rw [hql]; exact p.layout.widths.1)
      (by rw [hql]; have := p.layout.widths; omega) t (by decide) (element_space (by decide) p))
      fun s' h => ⟨h.schedule hs (by decide) (element_space (by decide) p) (stable p),
        qb, h.external (by decide) (element_space (by decide) p) hqb, hql, hqv⟩

theorem publicIsOne_ct (inputs : SchedulePublic → List (Operand × Nat))
    (stable : ∀ p a, a ∈ inputs p → a.1.length ≠ .mask ∧ stablePointer a.1.pointer) :
    RelCT isa (Two (PublicKeyPre inputs)) (Checks.isOne pWorkspace (Core.element t))
      (Two (PublicKeyPre inputs)) := by
  have ct := scheduleIsOne_ct inputs stable .p (Core.element t) (fun p => p.layout.pLen)
    (by change t < 2 ^ 16; decide) (by trivial) (by intro p; have := p.layout.widths; omega)
    (fun _ => Nat.le_refl _) (by taint_decide)
  refine two_post (two_map (fun p => p) (fun p s h =>
    ⟨h.1, h.1.1.availableLocal .p t (by decide) (element_space (by decide) p)⟩) (ct.mono (fun _ _ h => h) (fun _ _ _ => trivial))) ?_
  intro p s ⟨hs, qb, hqb, hql, hqv⟩
  obtain ⟨valid, hm⟩ := hs.2.2
  have hb := hs.1.readLocal .p t (by decide) (element_space (by decide) p)
  have hl : (Spec.Rsa.bytesAt s.mem (off p.layout.base t) p.layout.pLen).length = p.layout.pLen := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  refine WP.mono (readyIsOne_ok hs.1 .p (Core.element t) (by change t < 2 ^ 16; decide) hb
    (by simp only [ModulusSide.length]; rw [hl]; have := p.layout.widths; omega) (by simp only [ModulusSide.length]; rw [hl]; exact Nat.le_refl _) hm)
    fun s' h => ⟨h.schedule hs (stable p), qb,
      h.preserve hs.1 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb, hql, hqv⟩

end VG.Proof.Dsa.AArch64
