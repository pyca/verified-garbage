module

public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveBodyCT
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCT
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveWrite
public import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveBodyCT
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
meta import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCopy
meta import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCopy
import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
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
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
import VerifiedGarbage.Proof.Dsa.AArch64.Call2
import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.Child
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveFailure
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
import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
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
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
import VerifiedGarbage.Proof.Dsa.AArch64.Store
import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingMain
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingOperands
import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
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
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
public import VerifiedGarbage.Proof.Dsa.AArch64.CTBlocks
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCopy
public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveFailure
public import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Minus
public import VerifiedGarbage.Proof.Dsa.AArch64.MinusCore
public import VerifiedGarbage.Proof.Dsa.AArch64.OneScanCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ParametersCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyMinusCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ReadyRangeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
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
public import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizesCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SignificantLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingMain
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingReadyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.WidthMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalar
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteScalarCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.WriteSignature
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.Derive
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.PackedBytes
meta import VerifiedGarbage.Proof.Dsa.SignVerify
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.MdStream.Spec
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Sha256.Stream

/-! # Constant time of the complete AArch64 key derivation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-! ## Writing the key at public addresses -/

structure KeyPublic where
  base : Addr
  out : Addr
  params : Addr
  publicValue : Addr
  scalar : Addr
  pLen : Nat
  qLen : Nat

def KeyPre (k : KeyPublic) (s : State) : Prop :=
  s.gpr .x0 = k.base ∧ Scr s k.base pWorkspace ∧
  (∃ valid, KeyFields s k.base k.out k.params k.publicValue k.scalar k.pLen k.qLen valid) ∧
  0 < k.pLen ∧ 0 < k.qLen ∧ 3 * k.pLen + 2 * k.qLen < 2 ^ 64 ∧
  KeySource s k.params k.out (2 * k.pLen + k.qLen) (3 * k.pLen + 2 * k.qLen) ∧
  KeySource s k.publicValue k.out k.pLen (3 * k.pLen + 2 * k.qLen) ∧
  KeySource s k.scalar k.out k.qLen (3 * k.pLen + 2 * k.qLen) ∧
  (∀ i < 3 * k.pLen + 2 * k.qLen, InRegions s.wr (k.out + BitVec.ofNat 64 i) 1)

def KeyHeadRegs (k : KeyPublic) (s : State) : Prop :=
  s.gpr .x0 = k.base ∧ s.gpr .x1 = k.params ∧ s.gpr .x2 = k.out ∧
  s.gpr .x9 = BitVec.ofNat 64 (2 * k.pLen + k.qLen) ∧
  KeyRegs s k.out k.publicValue k.scalar k.pLen k.qLen

theorem writeKey_ct : RelCT isa (Two KeyPre) Generate.writeKey
    (Two (fun (k : KeyPublic) (s : State) => s.gpr .x0 = k.base)) := by
  have ct : RelCT isa (Two KeyPre) Generate.writeKey (fun _ _ => True) := by
    unfold Generate.writeKey seqs
    refine RelCT.seq (two_piece (Ψ := KeyHeadRegs) [.x0]
      (pins_of (fun (k : KeyPublic) _ => k.base) (by
        intro k s h r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact h.1)) (by taint_decide) ?_) ?_
    · intro k s ⟨hdi, hs, ⟨valid, hf⟩, _⟩
      exact WP.mono (keyHead_ok hs hdi (Nat.le_refl _) hf) fun t ⟨h1, h2, h3, _, _, hk, hr⟩ =>
        ⟨(hk.gpr .x0 (by decide)).trans hdi, h1, h2, h3, hr⟩
    · exact two_taint [.x0, .x1, .x2, .x9, .x11, .x12, .x13, .x14, .x10]
        (pins_of (fun k r => match r with
            | .x0 => k.base | .x1 => k.params | .x2 => k.out
            | .x9 => BitVec.ofNat 64 (2 * k.pLen + k.qLen) | .x11 => k.publicValue | .x12 => k.scalar
            | .x13 => BitVec.ofNat 64 k.pLen | .x14 => BitVec.ofNat 64 k.qLen | _ => k.out)
          (by
            intro k s h r hr
            obtain ⟨h1, h2, h3, h4, h5⟩ := h
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · exact h1
            · exact h2
            · exact h3
            · exact h4
            · exact h5.publicValue
            · exact h5.scalar
            · exact h5.pLen
            · exact h5.qLen
            · exact h5.out)) (by taint_decide)
  refine two_post ct ?_
  intro k s ⟨hdi, hs, ⟨valid, hf⟩, hp, hq, hk, hP, hY, hX, hw⟩
  exact WP.mono (writeKey_ok hs hdi (Nat.le_refl _) hf hp hq hk hP hY hX hw)
    fun t ⟨_, _, _, _, hkt⟩ => (hkt.gpr .x0 (by decide)).trans hdi

/-! ## Two calls through the computation -/

def DeriveCall.schedule (c : DeriveCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := 0
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.pb
    rw [c.input.pbLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.qb
    rw [c.input.qbLength] at h
    exact Nat.le_of_lt h
  digestBound := by decide

def DeriveCall.initialization (c : DeriveCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.pb
  qBytes := c.input.qb
  pLength := c.input.pbLength
  qLength := c.input.qbLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem DeriveShaped.initialization {reference : DeriveCall} {s : State}
    (h : DeriveShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hscr : Scr s c.layout.base usedBytes := scratch_prefix (n := usedBytes) hs.scratch (by decide) (by decide)
  obtain ⟨hps, hqs, _, _⟩ := c.pre.sources hs.frame hs.keep
  have hps' : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.pb := source_shrink hps (by decide)
  have hqs' : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.qb := source_shrink hqs (by decide)
  rw [hag.layout] at hf hr hscr hps' hqs'
  rw [hag.pb] at hps'
  rw [hag.qb] at hqs'
  exact ⟨hscr, hr, hf, hps', hqs'⟩

abbrev AcceptedDeriveCall := {c : DeriveCall // c.input.accepted = true}

def DeriveReady (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ DeriveInitialized c.input c.original c.pre.pLength s

theorem deriveWorkspaces_ct : RelCT isa (Two (fun c : AcceptedDeriveCall => DeriveShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedDeriveCall => DeriveReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedDeriveCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (deriveInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

theorem DeriveReady.sched {reference : DeriveCall} {s : State} (ha : reference.input.accepted = true)
    (h : DeriveReady reference s) : ∃ pi qi, DeriveSched (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, hframe, hk⟩ := h
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  have hscr : Scr s c.layout.base deriveExtent := c.pre.scratch.congr hk.wr
  change Ready (c.layout.withInverses pi qi) s at hr
  change DeriveOperands (c.layout.withInverses pi qi) c.input s at ho
  have hy : Ready (c.layout.withInverses pi qi) s := hr
  rw [hag.layout] at hr ho hmask hscr
  have hgl : c.input.gb.length = reference.layout.pLen := c.input.gbLength.trans hag.pLen
  have hql : c.input.qb.length = reference.layout.qLen := c.input.qbLength.trans hag.qLen
  have hxl : c.input.x.length = reference.layout.qLen := c.input.xLength.trans hag.qLen
  have hp384 : reference.layout.pLen ≤ 384 := reference.layout.widths.2.2.2
  refine ⟨pi, qi, ⟨hr, ?_, ⟨true, hmask⟩⟩, hscr, c.input.qb, ho.subgroup, hql, ?_⟩
  · intro a ha
    simp only [deriveInputs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · -- y's slot, past the signer's layout
      have hyw : word s.mem reference.layout.base Field.y.offset = off reference.layout.base derivedY :=
        hr.fields .y (by decide)
      refine ⟨Spec.Rsa.bytesAt s.mem (off reference.layout.base derivedY) reference.layout.pLen,
        ⟨?_, ?_, ?_, ?_⟩, bytesAt_length _ _ _⟩
      · rw [bytesAt_length]
        exact (hr.fields .pLen (by decide)).trans reference.layout.pLength
      · intro i hi
        rw [bytesAt_length] at hi
        show InRegions (s.rd ++ s.wr) (word s.mem reference.layout.base Field.y.offset + BitVec.ofNat 64 i) 1
        rw [hyw, off_add]
        exact scr_byte_rd hscr (by unfold deriveExtent; omega)
      · intro i hi
        show s.mem (word s.mem reference.layout.base Field.y.offset + BitVec.ofNat 64 i) = _
        rw [hyw]
        simp [Spec.Rsa.bytesAt]
      · intro i hi
        rw [bytesAt_length] at hi
        show usedBytes ≤ ofs reference.layout.base (word s.mem reference.layout.base Field.y.offset + BitVec.ofNat 64 i)
        rw [hyw, ofs_off _ (by have := hscr.nowrap; unfold deriveExtent at this; omega)]
        exact Nat.le_add_right _ _
    · exact ⟨_, ho.subgroup.shrink (by decide), hql⟩
    · exact ⟨_, ho.generator.shrink (by decide), hgl⟩
    · exact ⟨_, ho.scalar.shrink (by decide), hxl⟩
  · change Spec.Dsa.decodeBE c.input.qb = Spec.Dsa.decodeBE reference.input.qb
    rw [hag.qb]

theorem deriveReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedDeriveCall => DeriveReady c.val) s₁ s₂) : Two DeriveSched s₁ s₂ := by
  obtain ⟨reference, h₁, h₂, hsp⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.sched reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.sched reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1.1 h₂.1.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂, hsp⟩

/-- After the computation: what writing the key needs. -/
def DeriveComputed (reference : DeriveCall) (s : State) : Prop :=
  ∃ c : DeriveCall, DeriveAgrees reference c ∧ ∃ pi qi valid,
    Ready (c.layout.withInverses pi qi) s ∧ word s.mem c.input.base Field.mask.offset = mask valid ∧
    InScr c.input.base deriveExtent c.original.mem s.mem ∧ Keep coreRegs c.original s

def DeriveCall.key (c : DeriveCall) : KeyPublic where
  base := c.layout.base
  out := c.layout.fields .out
  params := c.layout.fields .p
  publicValue := c.layout.fields .y
  scalar := c.layout.fields .x
  pLen := c.layout.pLen
  qLen := c.layout.qLen

theorem DeriveComputed.key {reference : DeriveCall} {s : State} (h : DeriveComputed reference s) :
    KeyPre reference.key s := by
  obtain ⟨c, hag, pi, qi, valid, hr, hm, hframe, hk⟩ := h
  have hkey : c.key = reference.key := by unfold DeriveCall.key; rw [hag.layout]
  rw [← hkey]
  have hl : Spec.Dsa.lengthsValid c.key.pLen c.key.qLen := c.input.lengths
  unfold Spec.Dsa.lengthsValid at hl
  have hscr : Scr s c.input.base deriveExtent := c.pre.scratch.congr hk.wr
  have hn := hscr.nowrap
  obtain ⟨_, _, _, hxs⟩ := c.pre.sources hframe hk
  have hparams := c.pre.paramsSource.congrK hframe hk
  have hf (f : Field) (hf : f ≠ .mask) : word s.mem c.input.base f.offset = c.layout.fields f := hr.fields f hf
  refine ⟨hr.parent.x0, scratch_prefix (n := pWorkspace) hscr (by decide) (by decide),
    ⟨valid, hf .out (by decide), hf .p (by decide), hf .y (by decide), hf .x (by decide),
      (hf .pLen (by decide)).trans c.pre.pLength, hf .qLen (by decide), hm⟩,
    by omega_using [hl], by omega_using [hl], by omega_using [hl],
    ⟨fun i hi => by rw [hk.rd, hk.wr]; exact c.pre.paramsSource.rd i (by rw [c.input.paramsLength]; exact hi),
      c.pre.paramsOut⟩,
    ⟨fun i hi => by
      change InRegions (s.rd ++ s.wr) (off c.input.base derivedY + BitVec.ofNat 64 i) 1
      rw [off_add]
      exact scr_byte_rd hscr (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hl]),
     fun i hi j hj => scr_ne_out c.pre.outSeparate (d := derivedY) (i := i)
      (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hl]) (by omega_using [hn]) j hj⟩,
    ⟨fun i hi => by rw [hk.rd, hk.wr]; exact c.pre.xSource.rd i (by rw [c.input.xLength]; exact hi),
      c.pre.xOut⟩,
    fun i hi => by rw [hk.wr]; exact c.pre.outWrite i hi⟩

theorem deriveComputed_ok (M : Mont) {reference : AcceptedDeriveCall} {s : State}
    (h : DeriveReady reference.val s) :
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
      Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, Checks.signingKey M.mm]) s (DeriveComputed reference.val) := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, hframe, hk⟩ := h
  have hac : c.input.accepted = true := hag.accepted.trans reference.property
  obtain ⟨hsize, hpo, hqo⟩ := c.input.shapeFacts hac
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : Spec.Dsa.decodeBE c.input.pb ≤ 256 ^ c.input.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.pb; rw [c.input.pbLength] at hh; exact Nat.le_of_lt hh
  have hqf : Spec.Dsa.decodeBE c.input.qb ≤ 256 ^ c.input.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt c.input.qb; rw [c.input.qbLength] at hh; exact Nat.le_of_lt hh
  refine WP.mono (deriveBody_ok (L := c.layout.withInverses pi qi) M hr (c.pre.scratch.congr hk.wr)
    hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar c.input.gbLength c.input.qbLength
    c.input.xLength rfl rfl hm) fun t ⟨ht, hmt, _, hft, hkt⟩ => ?_
  exact ⟨c, hag, pi, qi, _, ht, hmt, hframe.trans (InScr.of_outside hft (by decide)),
    (hk.trans hkt).mono (by decide)⟩

theorem deriveSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedDeriveCall => DeriveShaped c.val))
      (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
        Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, Checks.signingKey M.mm, Generate.writeKey, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq deriveWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, Checks.signingKey M.mm]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine RelCT.seq (R := Two (fun c : AcceptedDeriveCall => DeriveComputed c.val))
    (two_post ((deriveBodySched_ct M).mono (fun _ _ h => deriveReady_related h) (fun _ _ h => h))
      (fun reference s h => deriveComputed_ok M h)) ?_
  unfold seqs
  exact RelCT.seq (two_map (fun c : AcceptedDeriveCall => c.val.key) (fun _ _ h => h.key) writeKey_ct)
    (two_map (fun k : KeyPublic => k.base) (fun _ _ h => h) result_ct)

theorem deriveMain_ct (M : Mont) :
    RelCT isa (Two DeriveStart) (Generate.deriveKey M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq deriveShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map DeriveCall.failure (fun _ _ h => h.failure) deriveFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (deriveSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64
