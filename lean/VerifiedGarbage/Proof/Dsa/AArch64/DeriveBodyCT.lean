module
public import VerifiedGarbage.Proof.Dsa.AArch64.Derive
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState

import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCopy
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.Octets
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
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
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
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.Add
import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.BodyCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Dsa.AArch64.Call2
import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.Child
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCT
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveFailure
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveWrite
import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Dsa.AArch64.Minus
import VerifiedGarbage.Proof.Dsa.AArch64.MinusCore
import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
import VerifiedGarbage.Proof.Dsa.AArch64.ParametersCT
import VerifiedGarbage.Proof.Dsa.AArch64.Parent
import VerifiedGarbage.Proof.Dsa.AArch64.Parity
import VerifiedGarbage.Proof.Dsa.AArch64.Power
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint
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
import VerifiedGarbage.Proof.Dsa.AArch64.ReleaseBytes
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
import VerifiedGarbage.Proof.Dsa.AArch64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Zero
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
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Sha256.Stream
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
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Add
meta import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.BodyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
meta import VerifiedGarbage.Proof.Dsa.AArch64.Call2
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.Child
meta import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveFailure
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveWrite
meta import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Failure
meta import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.Masks
meta import VerifiedGarbage.Proof.Dsa.AArch64.Minus
meta import VerifiedGarbage.Proof.Dsa.AArch64.MinusCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
meta import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
meta import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ParametersCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parent
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parity
meta import VerifiedGarbage.Proof.Dsa.AArch64.Power
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReleaseBytes
meta import VerifiedGarbage.Proof.Dsa.AArch64.Result
meta import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleAddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.Derive
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.Zero
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
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Sha256.Stream

/-! # Constant time of derivation's computation: x's range, g^x, y's copy and the key checks

The operands' bytes may differ between two calls, x's among them: the
schedule relates two runs by their public layout alone. The subgroup order's
bytes are kept exactly, at derivation's extent, for the key checks. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- Derivation's operands: y's slot, q, g and x. -/
def deriveInputs (p : SchedulePublic) : List (Operand × Nat) :=
  [(Core.publicValue, p.layout.pLen), (⟨.input .q, .qLen⟩, p.layout.qLen), (Core.generator, p.layout.pLen),
    (Core.privateScalar, p.layout.qLen)]

theorem deriveInputs_stable (p : SchedulePublic) (a : Operand × Nat)
    (ha : a ∈ deriveInputs p) : a.1.length ≠ .mask ∧ stablePointer a.1.pointer := by
  simp only [deriveInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · simp [Core.publicValue, stablePointer]
  · change Field.qLen ≠ .mask ∧ Field.q ≠ .mask
    decide
  · simp [Core.generator, stablePointer]
  · simp [Core.privateScalar, stablePointer]

/-- An operand past the signer's layout stays available, with whatever bytes
it then holds, when its pointer and length do. -/
theorem ExternalAvailable.rebuild {L : ExecutionLayout} {a : Operand} {n : Nat} {s t : State}
    (hs : Ready L s) (ht : Ready L t) (hk : Keep coreRegs s t)
    (ha : a.length ≠ .mask) (hp : stablePointer a.pointer)
    (h : ExternalAvailable L a n s) : ExternalAvailable L a n t := by
  obtain ⟨bs, hb, hl⟩ := h
  have hptr := hs.pointer_eq ht a.pointer hp
  refine ⟨Spec.Rsa.bytesAt t.mem (pointerValue t.mem L.base a.pointer) n, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [bytesAt_length]
    exact (ht.fields a.length ha).trans ((hs.fields a.length ha).symm.trans (hl ▸ hb.length))
  · intro i hi
    rw [bytesAt_length] at hi
    rw [hk.rd, hk.wr, hptr]
    exact hb.source.rd i (by omega)
  · intro i hi
    simp [Spec.Rsa.bytesAt]
  · intro i hi
    rw [bytesAt_length] at hi
    rw [hptr]
    exact hb.source.out i (by omega)
  · exact bytesAt_length _ _ _

/-- The schedule's state, with derivation's extent and q's bytes. -/
def DeriveSched (p : SchedulePublic) (s : State) : Prop :=
  ScheduleState deriveInputs p s ∧ Scr s p.layout.base deriveExtent ∧
  ∃ qb : List Byte, OperandBytes s p.layout.base deriveExtent ⟨.input .q, .qLen⟩ qb ∧
    qb.length = p.layout.qLen ∧ Spec.Dsa.decodeBE qb = p.layout.subgroup

theorem deriveRange_ct : RelCT isa (Two DeriveSched) (Checks.range qWorkspace Core.privateScalar)
    (Two DeriveSched) := by
  have ct := scheduleRange_ct deriveInputs (fun p => deriveInputs_stable p) .q Core.privateScalar
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.privateScalar])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  refine two_post ((two_map (fun p => p) (fun p s h => ⟨h.1, (h.1.2.1 (Core.privateScalar, p.layout.qLen)
    (by simp [deriveInputs])).active⟩)
    ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  obtain ⟨bs, hbs, hlen⟩ := hs.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ deriveInputs p by
    simp [deriveInputs])
  obtain ⟨valid, hm⟩ := hs.2.2
  refine WP.mono (readyRange_ok hs.1 .q Core.privateScalar (by trivial) hbs.active
    (by rw [hlen]; exact p.layout.widths.1) (by rw [hlen]; exact Nat.le_refl _) false hm) fun t h => ?_
  exact ⟨h.schedule hs (fun a ha => deriveInputs_stable p a ha), hscr.congr h.keep.wr,
    qb, h.preserve hs.1 (by decide) (by decide) (by change Field.q ≠ .mask; decide) hqb, hql, hqv⟩

theorem derivePow_ct (M : Mont) : RelCT isa (Two DeriveSched)
    (Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2)) (Two DeriveSched) := by
  have hend (p : SchedulePublic) : t2 + ModulusSide.p.length p.layout ≤ usedBytes := element_space (by decide) p
  have ct := schedulePow_ct M deriveInputs (fun p => deriveInputs_stable p) .p t2 Core.generator
    Core.privateScalar (fun p => p.layout.pLen) (fun p => p.layout.qLen) (by trivial) (by trivial)
    (by simp [stablePointer, Core.generator]) (by simp [stablePointer, Core.privateScalar])
    (by intro p; have := p.layout.widths; omega) (fun _ => Nat.le_refl _)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega)
    (by decide) (by decide) hend (by taint_decide)
  refine two_post ((two_map (fun p => p) (fun p s h => ⟨h.1,
    (h.1.2.1 (Core.generator, p.layout.pLen) (by simp [deriveInputs])).active,
    (h.1.2.1 (Core.privateScalar, p.layout.qLen) (by simp [deriveInputs])).active⟩) ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  obtain ⟨ga, hga, hgl⟩ := hs.2.1 _ (show (Core.generator, p.layout.pLen) ∈ deriveInputs p by
    simp [deriveInputs])
  obtain ⟨xa, hxa, hxl⟩ := hs.2.1 _ (show (Core.privateScalar, p.layout.qLen) ∈ deriveInputs p by
    simp [deriveInputs])
  have step := readyPow_ok M hs.1 .p (p.greater .p) (p.odd .p) Core.generator Core.privateScalar
    (by trivial) (by trivial) hga.active hxa.active (by rw [hgl]; have := p.layout.widths; omega)
    (by rw [hgl]; exact Nat.le_refl _) (by rw [hxl]; exact p.layout.widths.1)
    (by rw [hxl]; have := p.layout.widths; omega) t2 (by decide) (hend p)
  refine WP.mono (by simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField] using step)
    fun t h => ?_
  have hf : Outside p.layout.base 128 (deriveExtent - 128) s.mem t.mem :=
    (h.scheduleFrame (by decide) (hend p)).mono (by decide) (by decide)
  exact ⟨h.schedule hs (by decide) (hend p) (fun a ha => deriveInputs_stable p a ha), hscr.congr h.keep.wr,
    qb, hqb.frame hs.1 h.ready hf h.keep (by decide) (by change Field.q ≠ .mask; decide), hql, hqv⟩

def CopyRegs (p : SchedulePublic) (s : State) : Prop :=
  s.gpr .x1 = off p.layout.base t2 ∧ s.gpr .x2 = off p.layout.base derivedY ∧
    s.gpr .x9 = BitVec.ofNat 64 p.layout.pLen

theorem deriveCopy_ct : RelCT isa (Two DeriveSched) Generate.copyY (Two DeriveSched) := by
  have ct : RelCT isa (Two DeriveSched) Generate.copyY (fun _ _ => True) := by
    unfold Generate.copyY seqs
    refine RelCT.seq (two_piece (Ψ := CopyRegs) [.x0]
      (pins_of (fun p _ => p.layout.base) (by
        intro p s h r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact h.1.1.parent.x0)) (by taint_decide) ?_) ?_
    · intro p s h
      exact WP.mono (copyHead_ok h.1.1) fun t ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3⟩
    · exact two_taint [.x1, .x2, .x9]
        (pins_of (fun p r => if r = .x1 then off p.layout.base t2 else if r = .x2 then off p.layout.base derivedY
            else BitVec.ofNat 64 p.layout.pLen)
          (by
            intro p s h r hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact h.1
            · exact h.2.1
            · exact h.2.2)) (by taint_decide)
  refine two_post ct ?_
  intro p s ⟨hs, hscr, qb, hqb, hql, hqv⟩
  refine WP.mono (copyY_ok hs.1 hscr) fun t ⟨ht, _, hf, hk⟩ => ?_
  have hp384 : p.layout.pLen ≤ 384 := p.layout.widths.2.2.2
  have hf' : Outside p.layout.base 128 (deriveExtent - 128) s.mem t.mem :=
    hf.mono (by decide) (by unfold deriveExtent; omega_using [hp384])
  obtain ⟨valid, hm⟩ := hs.2.2
  refine ⟨⟨ht, fun a ha => (hs.2.1 a ha).rebuild hs.1 ht hk (deriveInputs_stable p a ha).1
    (deriveInputs_stable p a ha).2, valid, (hf.word (Or.inl (by decide)) (by decide)).trans hm⟩,
    hscr.congr hk.wr, qb, hqb.frame hs.1 ht hf' hk (by decide) (by change Field.q ≠ .mask; decide), hql, hqv⟩

theorem deriveBodySched_ct (M : Mont) : RelCT isa (Two DeriveSched)
    (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, Checks.signingKey M.mm]) (fun _ _ => True) := by
  have h4 := signingKey_ct M deriveInputs (fun p => deriveInputs_stable p)
    (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs]) (by intro p; simp [deriveInputs])
  unfold seqs
  refine RelCT.seq deriveRange_ct (RelCT.seq (derivePow_ct M) (RelCT.seq deriveCopy_ct ?_))
  refine (two_map (Φ := DeriveSched) (fun p => p) (fun p s h => ⟨h.1, ?_⟩) h4).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  obtain ⟨qb, hqb, hql, hqv⟩ := h.2.2
  exact ⟨qb, hqb.shrink (by decide), hql, hqv⟩

end VG.Proof.Dsa.AArch64
