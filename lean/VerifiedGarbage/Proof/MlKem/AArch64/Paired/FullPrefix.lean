module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.LastStart
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullPrepare
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.AArch64.Syms
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
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Begin
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Extra
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitialOne
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reinit
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Single
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Store
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Trace
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.ZeroBoth
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
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
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
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullStart
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reinit
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Single
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

/-! # Complete singleton stream and vector parser entry for relational timing -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem

structure LastInput (sb ss off : Nat) (p seed out table : Addr) (s : State) : Prop where
 ptr : s.gpr .x28+BitVec.ofNat 64 ss=p
 seedPtr : s.gpr .x28+BitVec.ofNat 64 sb=seed
 outPtr : s.gpr .x28+BitVec.ofNat 64 off=out
 readable : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8
 separate : (Region.mk seed 32).Disjoint ⟨p,2048⟩
 context : SingleContext p out table s
 symbol : s.syms "VG_MLKEM_REJ_SHUFFLE"=table

def fullPrefix (sb ss off a k : Nat) : Prog isa :=
 .seq (.seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
   (.loop singleBody (.nonzero .x .x22))) (.block (fullPrep off))
def fullPrefixRegs : List Reg := fullStartRegs++prepRegs

structure FullPrefixPostW (w16 : Bool) (B : Nat→Byte) (p out : Addr) (s t : State) : Prop where
 keep : Keep fullPrefixRegs s t
 entry : Rej8.EntryW w16 [] 280 B (p+400) out t
 pointer : t.gpr .x19=p
 tablePtr : t.gpr .x16=s.syms "VG_MLKEM_REJ_SHUFFLE"

theorem fullPrefix_ok {w16 : Bool} {s initial : State} {p seed out table : Addr} {sb ss off a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (h : LastInput sb ss off p seed out table s) (hp : s.gpr .x19=p)
    (sv : Noise.Saved p initial s.mem) :
    WP isa (fullPrefix sb ss off a k) s (FullPrefixPostW w16 (xofByte (seedBytes s.mem seed a k)) p out s) := by
  refine WP.seq (WP.mono_syms (fullStart_ok (a:=a) (k:=k) hss hsb h8 hp h.ptr h.seedPtr h.readable h.context.scratch h.separate sv)
    fun u ⟨ku,fu,_,_,u19,_,_,bu⟩ sy => ?_)
  have cu := h.context.frame ku.rd ku.wr (fu.mono (by simp [fullWrites]))
  refine WP.mono (fullPrep_ok (w16 := w16) hoff u19 (by rw [ku.get .x28]; exact h.outPtr)
    cu.scratch cu.output cu.apart (fun i hi => bu.xof hk hk256 hi)
    (by rw [sy,h.symbol]; exact cu.artifact) (by rw [sy,h.symbol]; exact cu.readable)
    (by rw [sy,h.symbol]; exact cu.tableScratch) (by rw [sy,h.symbol]; exact cu.tableOut)) fun t ⟨kt,_,et,tablePtr⟩ => ?_
  exact ⟨ku.trans kt,et,(kt.get .x19).trans u19,by rw [tablePtr,sy]⟩

theorem fullPrefix_ct {sb ss off a k : Nat} (hss : ss<4096) : ConstantTime isa (fun _=>True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19,.x28])) (fullPrefix sb ss off a k) := by
  by_cases ho : off<4096
  · apply ct_eraseOff_eq [.x19,.x28]
      (d := Code.eraseOff (fullPrefix 0 0 0 0 1))
      (by simp only [fullPrefix,fullInit_eq hss,fullInit_eq (by decide : 0<4096),fullPrep,fullEntry,
        Impl.MlKem.AArch64.ptrTo,ite_eq_left hss,ite_eq_left ho]; rfl)
    taint_decide
  · apply ct_eraseOff_eq [.x19,.x28]
      (d := Code.eraseOff (fullPrefix 0 0 4096 0 1))
      (by simp only [fullPrefix,fullInit_eq hss,fullInit_eq (by decide : 0<4096),fullPrep,fullEntry,
        Impl.MlKem.AArch64.ptrTo,ite_eq_left hss,ite_eq_right ho]; rfl)
    taint_decide

end VG.Proof.MlKem.AArch64.Paired
