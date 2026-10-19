module

public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
public import VerifiedGarbage.Impl.MlKem.AArch64.Paired
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
meta import VerifiedGarbage.Impl.MlKem.AArch64.Paired
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullInit
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Bytes
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecSpec
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Decode
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncLoop
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncMath
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Encode
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.All
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCore
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.OutCall
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Tail
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Word
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Words
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Extra
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullStart
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reinit
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Single
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Start
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
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.Rc4.AArch64.Group
import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Barrett
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Bytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecSpec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Decode
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncLoop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncMath
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Encode
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce1Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Ce4Step
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Narrow
meta import VerifiedGarbage.Proof.MlKem.AArch64.Coeff16
meta import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
meta import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.All
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCore
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.OutCall
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Tail
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Word
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Words
meta import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Zero
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Extra
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Start
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Store
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Accept
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BatchCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8BodyCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8CT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Decode
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Invariant
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Keep
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Loop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8LoopCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Memory
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Public
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8ScalarCT
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Steps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
meta import VerifiedGarbage.Proof.MlKem.AArch64.Shared
meta import VerifiedGarbage.Proof.Rc4.AArch64.Group
meta import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
meta import VerifiedGarbage.Proof.Rc4.AArch64.Rows
meta import VerifiedGarbage.Proof.Rc4.Stream
meta import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.TCB.Axioms

/-! # Public-address timing for paired and singleton SHAKE128 generation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem ct_eraseOff_eq {c d : Prog isa} (rs : List Reg)
    (he : Code.eraseOff c=d) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) d hc).isSome=true) :
    ConstantTime isa (fun _ => True) (VG.AArch64.Taint.Agree (Taint.ofRegs rs)) c :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs rs) (fun _ _ _ _ h => h)
    (Taint.isSome_check_of_eraseOff he h)

theorem init_ct (sb ss a b k : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x28]))
    (.block (Impl.MlKem.AArch64.Paired.init sb ss a b k)) := by
  unfold Impl.MlKem.AArch64.Paired.init ptrTo
  split <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x28])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem squeeze_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x20,.x21,.x22]))
    Impl.MlKem.AArch64.Paired.squeeze := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19,.x20,.x21,.x22])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem single_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x20,.x22]))
    (.loop singleBody (.nonzero .x .x22)) := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19,.x20,.x22])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem squeezeBlock_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x20,.x21]))
    (.seq (Impl.Sha3.AArch64.Neon.X2.call true .x19 .x19 1536)
      (.block (Impl.Sha3.AArch64.Neon.X2.squeeze 21 .x19 .x20 .x21))) := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19,.x20,.x21])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem fullInit_ct {sb ss a k : Nat} (hss : ss<4096) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x28]))
    (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k)) := by
  rw [fullInit_eq hss]
  simp only [ptrTo,ite_eq_left hss]
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19,.x28])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem start_ct (sb ss a b k : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x28]))
    (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b k)) Impl.MlKem.AArch64.Paired.squeeze) := by
  by_cases hs : ss<4096
  · apply ct_eraseOff_eq [.x28]
      (d := Code.eraseOff (.seq (.block (Impl.MlKem.AArch64.Paired.init 0 0 0 0 1)) Impl.MlKem.AArch64.Paired.squeeze))
      (by simp only [Impl.MlKem.AArch64.Paired.init,ptrTo,ite_eq_left hs]; rfl)
    taint_decide
  · apply ct_eraseOff_eq [.x28]
      (d := Code.eraseOff (.seq (.block (Impl.MlKem.AArch64.Paired.init 0 4096 0 0 1)) Impl.MlKem.AArch64.Paired.squeeze))
      (by simp only [Impl.MlKem.AArch64.Paired.init,ptrTo,ite_eq_right hs]; rfl)
    taint_decide

theorem fullStart_ct {sb ss a k : Nat} (hss : ss<4096) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x28]))
    (.seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
      (.loop singleBody (.nonzero .x .x22))) := by
  apply ct_eraseOff_eq [.x19,.x28]
    (d := Code.eraseOff (.seq (.block (Impl.MlKem.AArch64.Paired.fullInit 0 0 0 1))
      (.loop singleBody (.nonzero .x .x22))))
    (by rw [fullInit_eq hss,fullInit_eq (by decide : 0<4096)]; simp only [ptrTo,ite_eq_left hss]; rfl)
  taint_decide

theorem nextBlock_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19])) nextBlock := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlKem.AArch64.Paired
