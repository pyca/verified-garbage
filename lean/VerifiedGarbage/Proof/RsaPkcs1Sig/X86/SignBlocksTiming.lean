module
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
meta import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Sign
meta import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import VerifiedGarbage.Proof.Bignum.X86.CopyByteStep
import VerifiedGarbage.Proof.Bignum.X86.CopyRegion
import VerifiedGarbage.Proof.Bignum.X86.ReverseByteStep
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Cast5.X86.Run
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomEncoding
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.RandomTrace
import VerifiedGarbage.Proof.Dsa.X86.Bytes
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Dsa.X86.FetchByte
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.LoadSlot
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Dsa.X86.Moduli
import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
import VerifiedGarbage.Proof.Dsa.X86.RandomBody
import VerifiedGarbage.Proof.Dsa.X86.RandomCallArgs
import VerifiedGarbage.Proof.Dsa.X86.RandomPrepare
import VerifiedGarbage.Proof.Dsa.X86.RandomSample
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.X86.Reduce
import VerifiedGarbage.Proof.Dsa.X86.RunBytes
import VerifiedGarbage.Proof.Dsa.X86.SaveArgument
import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.StageFrame
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Mont.X86.Chain
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.DynamicAdd
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.DynamicSelect
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Mont.X86.ExponentLoop
import VerifiedGarbage.Proof.Mont.X86.ExponentMask
import VerifiedGarbage.Proof.Mont.X86.ExponentShift
import VerifiedGarbage.Proof.Mont.X86.ExponentStep
import VerifiedGarbage.Proof.Mont.X86.ExponentTimingBlocks
import VerifiedGarbage.Proof.Mont.X86.ExponentWord
import VerifiedGarbage.Proof.Mont.X86.Exponentiate
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.P256Red
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
import VerifiedGarbage.Proof.Mont.X86.PowerTiming
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.RowW
import VerifiedGarbage.Proof.Mont.X86.SparseShift
import VerifiedGarbage.Proof.Mont.X86.SparseStep
import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Rsa.AcceptanceMask32
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.PrivCheckLogic32
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Rsa.X86.PrivABI
import VerifiedGarbage.Proof.Rsa.X86.PrivBody
import VerifiedGarbage.Proof.Rsa.X86.PrivBodyTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivCallInput
import VerifiedGarbage.Proof.Rsa.X86.PrivCallPublic
import VerifiedGarbage.Proof.Rsa.X86.PrivCallsTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivCheck
import VerifiedGarbage.Proof.Rsa.X86.PrivCompare
import VerifiedGarbage.Proof.Rsa.X86.PrivCompareBuffer
import VerifiedGarbage.Proof.Rsa.X86.PrivCompareStep
import VerifiedGarbage.Proof.Rsa.X86.PrivContract
import VerifiedGarbage.Proof.Rsa.X86.PrivContractInput
import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.X86.PrivEntryReady
import VerifiedGarbage.Proof.Rsa.X86.PrivFn
import VerifiedGarbage.Proof.Rsa.X86.PrivFnTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivLocalArgument
import VerifiedGarbage.Proof.Rsa.X86.PrivMasks
import VerifiedGarbage.Proof.Rsa.X86.PrivNoSp
import VerifiedGarbage.Proof.Rsa.X86.PrivObservations
import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputeLength
import VerifiedGarbage.Proof.Rsa.X86.PrivPublicCall
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Rsa.X86.PrivRelease
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseBuffer
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseStep
import VerifiedGarbage.Proof.Rsa.X86.PrivRestore
import VerifiedGarbage.Proof.Rsa.X86.PrivRetained
import VerifiedGarbage.Proof.Rsa.X86.PrivReturn
import VerifiedGarbage.Proof.Rsa.X86.PrivSaveStatus
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Rsa.X86.PrivStatusMask
import VerifiedGarbage.Proof.Rsa.X86.PrivTailContext
import VerifiedGarbage.Proof.Rsa.X86.PrivTailTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.Rsa.X86.PrivZeroTest
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.RsaPkcs1Sig.ByteMath
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeChecks
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeCopyStep
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHash
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHead
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodePadding
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeWrite
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncoding
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackWord
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignWipe
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignWipeArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignZero
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86.MontRed
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! # Taint checks for argument setup, clearing, and register restoration -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Dsa.X86

theorem encArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block encArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem callArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block callArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem restore_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block restore)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

def clearTaint : VG.X86.Taint.T := { regs := .ofList [.esi, .ecx], flags := false }

theorem clear_relCT : RelCT isa (VG.X86.Taint.Agree clearTaint)
    (.loop (.block VG.Impl.Bignum.X86.PublicFn.clearStep) .ne) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) clearTaint (fun _ _ h => h)
  taint_decide

theorem wipeArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp]))
    (.block [.mov .ebx (.reg .eax), .mov .eax (.imm 0), .mov .esi (.reg .esp),
      .alu .add .esi (.imm (BitVec.ofNat 32 emOffset)), .mov .ecx (.mem (incoming 3))])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem return_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .eax (.reg .ebx)])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem zeroArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp]))
    (.block [.mov .esi (.mem (incoming 0)), .mov .ecx (.mem (incoming 1)), .mov .eax (.imm 0)])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaPkcs1Sig.X86.Sgn
