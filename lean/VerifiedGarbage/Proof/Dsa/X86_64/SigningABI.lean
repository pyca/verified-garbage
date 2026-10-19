module

public import VerifiedGarbage.Proof.Framework.Contract
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInput
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningCT
public import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Bignum.CrtMath
public import VerifiedGarbage.Proof.Bignum.LazyMath
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
public import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
public import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
public import VerifiedGarbage.Proof.Bignum.X86_64.Csub
public import VerifiedGarbage.Proof.Bignum.X86_64.Double
public import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
public import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
public import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
public import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
public import VerifiedGarbage.Proof.Bignum.X86_64.Row
public import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import VerifiedGarbage.Proof.Bignum.X86_64.Store
public import VerifiedGarbage.Proof.Bignum.X86_64.Valid
public import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Proof.Dsa.DomainWidths
public import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.Layout
public import VerifiedGarbage.Proof.Dsa.PackedBytes
public import VerifiedGarbage.Proof.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
public import VerifiedGarbage.Proof.Dsa.X86_64.Add
public import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
public import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.Call2
public import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
public import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
public import VerifiedGarbage.Proof.Dsa.X86_64.Child
public import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
public import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
public import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
public import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
public import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
public import VerifiedGarbage.Proof.Dsa.X86_64.Failure
public import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
public import VerifiedGarbage.Proof.Dsa.X86_64.Load
public import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Masks
public import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
public import VerifiedGarbage.Proof.Dsa.X86_64.Parent
public import VerifiedGarbage.Proof.Dsa.X86_64.Parity
public import VerifiedGarbage.Proof.Dsa.X86_64.Power
public import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
public import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
public import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Result
public import VerifiedGarbage.Proof.Dsa.X86_64.Save
public import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
public import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
public import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
public import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
public import VerifiedGarbage.Proof.Dsa.X86_64.Setup
public import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
public import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningMain
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningReadyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Store
public import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
public import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
public import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
public import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
public import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
public import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
public import VerifiedGarbage.Proof.Dsa.Zero
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Poly1305.Limbs64
public import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
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
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.Add
import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.X86_64.BufferFrame
import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
import VerifiedGarbage.Proof.Dsa.X86_64.Call2
import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.X86_64.Child
import VerifiedGarbage.Proof.Dsa.X86_64.CopyMasked
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.EnterLeave
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.EqualHead
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.Failure
import VerifiedGarbage.Proof.Dsa.X86_64.JointBuild
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointByteHead
import VerifiedGarbage.Proof.Dsa.X86_64.JointEncode
import VerifiedGarbage.Proof.Dsa.X86_64.JointEntries
import VerifiedGarbage.Proof.Dsa.X86_64.JointInit
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.JointPrepareCT
import VerifiedGarbage.Proof.Dsa.X86_64.JointRun
import VerifiedGarbage.Proof.Dsa.X86_64.JointStore
import VerifiedGarbage.Proof.Dsa.X86_64.JointWindowCT
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Minus
import VerifiedGarbage.Proof.Dsa.X86_64.MinusStep
import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
import VerifiedGarbage.Proof.Dsa.X86_64.OneScanCT
import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import VerifiedGarbage.Proof.Dsa.X86_64.Parity
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.PublicPrefix
import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.RangeHead
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyJoint
import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInit
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoop
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleJointCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.SealChild
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Dsa.X86_64.Setup
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.X86_64.SigningCT
import VerifiedGarbage.Proof.Dsa.X86_64.SigningMain
import VerifiedGarbage.Proof.Dsa.X86_64.SigningOperands
import VerifiedGarbage.Proof.Dsa.X86_64.SigningReadyCT
import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Dsa.X86_64.StoreSuffix
import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroHead
import VerifiedGarbage.Proof.Dsa.X86_64.ZeroMask
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Sha256.Stream

/-! # The signing ABI and its shared-contract precondition -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem stackArgs_five (s : State) : List.map (stackArg s) (List.range 5) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

structure SigningABI (s : State) : Prop where
  stackBound : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  rd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
  wr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  outScratch : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  keyScratch : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  nonceScratch : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  digestScratch : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  scratchArgs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  retScratch : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  keyBound : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  nonceBound : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  digestBound : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  scratchBound : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  lengths : Spec.Dsa.lengthsValid (s.gpr .r8).toNat (stackArg s 0).toNat
  outLength : (s.gpr .rsi).toNat = 2 * (stackArg s 0).toNat
  keyLength : (s.gpr .rcx).toNat = 3 * (s.gpr .r8).toNat + 2 * (stackArg s 0).toNat
  scratchLength : Spec.Dsa.scratchWords (s.gpr .r8).toNat ≤ (stackArg s 4).toNat

theorem signingABI_of {s : State} (h : (Spec.Dsa.signContract abi).pre s) : SigningABI s := by
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at h
  sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at h
  sig_split h
  constructor <;> with_reducible assumption

def SigningABI.input {s : State} (h : SigningABI s) : SigningInput where
  base := stackArg s 3
  digestPointer := stackArg s 1
  pLen := (s.gpr .r8).toNat
  qLen := (stackArg s 0).toNat
  key := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat
  nonce := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
  digest := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
  lengths := h.lengths
  keyLength := (bytesAt_length _ _ _).trans h.keyLength
  nonceLength := bytesAt_length _ _ _
  digestBound := by rw [bytesAt_length]; exact (stackArg s 2).isLt

theorem SigningABI.used {s : State} (h : SigningABI s) : usedBytes ≤ (stackArg s 4).toNat * 8 := by
  have hl := h.lengths
  have hs := h.scratchLength
  unfold Spec.Dsa.lengthsValid at hl
  unfold Spec.Dsa.scratchWords at hs
  change 15712 ≤ _
  omega

end VG.Proof.Dsa.X86_64
