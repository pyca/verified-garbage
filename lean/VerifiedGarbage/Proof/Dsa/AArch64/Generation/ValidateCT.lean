module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DomainCallCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Validate
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateCore
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateArgs
import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Pack
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
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.Add
import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.BodyCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Call2
import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.Child
import VerifiedGarbage.Proof.Dsa.AArch64.CopyMasked
import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Validate
import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.LoadCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
import VerifiedGarbage.Proof.Dsa.AArch64.Parent
import VerifiedGarbage.Proof.Dsa.AArch64.Parity
import VerifiedGarbage.Proof.Dsa.AArch64.Power
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
import VerifiedGarbage.Proof.Dsa.AArch64.ReadyJoint
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
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleReduceCT
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
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Dsa.Generation.WordFrame
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Spec.RsaOaep
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Pack
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
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Add
meta import VerifiedGarbage.Proof.Dsa.AArch64.AddCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Call2
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallAddCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.Child
meta import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryScratch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashFrame
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.LoadCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.LowerScan
meta import VerifiedGarbage.Proof.Dsa.AArch64.Masks
meta import VerifiedGarbage.Proof.Dsa.AArch64.ModulusMinus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Multiply
meta import VerifiedGarbage.Proof.Dsa.AArch64.NewChild
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parent
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parity
meta import VerifiedGarbage.Proof.Dsa.AArch64.Power
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReadyReduceCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Reduce
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceInit
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceReadCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.AArch64.ReduceStepCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ResultCall
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeTail
meta import VerifiedGarbage.Proof.Dsa.AArch64.Store
meta import VerifiedGarbage.Proof.Dsa.AArch64.StoreSuffix
meta import VerifiedGarbage.Proof.Dsa.AArch64.TopMask
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
meta import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
meta import VerifiedGarbage.Proof.Dsa.Derive
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.Memory
meta import VerifiedGarbage.Proof.Dsa.Generation.WordFrame
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.Zero
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Mgf1.Bytes
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Mgf
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Spec.RsaOaep

/-! # Timing of final parameter validation and its success/retry decision -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Dsa.Generation.Layout VG.Impl.Dsa.AArch64.Generation

structure ValidatePublic where
  input : ParametersInput
  B : Addr
  F : Addr
  S : Addr
  base : input.base = VG.Proof.Bignum.off B domainCheck
  frame : (⟨F, frameBytes⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩
  hash : (⟨S, oRsa⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩

def ValidatePublic.call (p : ValidatePublic) : DomainCallPublic := ⟨p.input, VG.Proof.Bignum.off p.B packed⟩

def ValidateBefore (pLen qLen : Nat) (p : ValidatePublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ (∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.B) ∧
  Scr s p.input.base Impl.Dsa.Layout.usedBytes ∧
  Src s p.input.base Impl.Dsa.Layout.usedBytes (VG.Proof.Bignum.off p.B packed) p.input.params ∧
  p.input.pLen = pLen ∧ p.input.qLen = qLen

theorem validateArgs_ready {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16) (h : ValidateBefore pLen qLen p s) :
    WP isa (.block (validateArgs pLen qLen)) s (DomainCallBefore p.call) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  refine WP.mono (validateArgs_ok L R hp hq) fun t ⟨hd, h8, hdx, hcx, hm, hk⟩ => ?_
  have hd' : t.gpr .x0 = VG.Proof.Bignum.off p.B packed := hb ▸ hd
  refine ⟨⟨hs.congr hk.wr, (hb ▸ h8).trans p.base.symm,
    by change t.gpr .x2 = BitVec.ofNat 64 p.input.pLen; rw [heP]; exact hdx,
    by change t.gpr .x3 = BitVec.ofNat 64 p.input.qLen; rw [heQ]; exact hcx, ?_⟩, hd'⟩
  rw [hd']
  exact src.congrK (fun _ _ => by rw [hm]) hk

def ValidateResult (p : ValidatePublic) (s : State) : Prop :=
  s.sp = p.F ∧ s.gpr .x0 = BitVec.ofNat 64
    (if Spec.Dsa.checkParametersBytes p.input.pLen p.input.qLen p.input.params then 1 else 0)

theorem validateCore_result (M : Mont)  {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16) (h : ValidateBefore pLen qLen p s) :
    WP isa (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.AArch64.Generate.checkParameters M.mm))
      s (ValidateResult p) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  have step := validateCore_ok M p.input L R (by rw [hb]; exact p.base)
    (by rw [heP]; exact hp) (by rw [heQ]; exact hq) hs (hb ▸ src) p.frame p.hash
  rw [heP, heQ] at step
  exact WP.mono step fun t ⟨hr, Lt, _, _, _⟩ =>
    ⟨Lt.sp, by simpa only [heP, heQ] using hr⟩

theorem validate_ct_of (M : Mont)  (pLen qLen : Nat)
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (validateArgs pLen qLen)) hc).isSome = true) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate M.mm pLen qLen) (fun _ _ => True) := by
  have core : RelCT isa (Two (ValidateBefore pLen qLen))
      (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.AArch64.Generate.checkParameters M.mm))
      (Two ValidateResult) := by
    refine two_post (RelCT.seq (two_post
      (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht)
      (fun _ _ h => validateArgs_ready hp hq h))
      (two_map ValidatePublic.call (fun _ _ h => h) (domainCall_ct M)))
      (fun _ _ h => validateCore_result M hp hq h)
  unfold validate
  refine RelCT.seq core (two_ite (fun _ _ _ hs ht => by
    change some (_ == (0#64)) = some (_ == (0#64))
    simp only [State.read, Size.bits, BitVec.setWidth_eq, hs.2, ht.2]) ?_ ?_)
  all_goals exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

theorem validate_ct (M : Mont)  (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate M.mm pLen qLen) (fun _ _ => True) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact validate_ct_of M _ _ (by decide) (by decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
