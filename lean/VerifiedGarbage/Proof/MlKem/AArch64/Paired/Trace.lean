module
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero

meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Extra
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Store
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BatchCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BodyCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8CT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8LoopCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Public
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8ScalarCT
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
meta import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Checkpoint
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BatchCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BodyCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8CT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8LoopCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Public
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8ScalarCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.Sha3.AArch64.Call
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad

/-! # Constant-time scalar wrappers around the public rejection loop -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64

theorem rejectEntry_ct (buf out : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block (rejectEntry buf out)) := by
  unfold rejectEntry ptrTo
  split <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem continueEntry_ct (buf : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block (continueEntry buf)) := by
  unfold continueEntry
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem moveFlag_ct (flag : Reg) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block [mov flag .x0]) := by
  cases flag <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem loadCheckpoint_ct (slot : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19]))
    (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)]) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19]) (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem zeroSuffix_ct (w16 : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4])) (Rej8.zeroSuffix w16) := by
  cases w16 <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x3,.x4]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlKem.AArch64.Paired
