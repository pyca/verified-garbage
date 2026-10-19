module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Begin
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitialTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SqueezeTiming
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Impl.MlKem.AArch64.Paired
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
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
import VerifiedGarbage.Proof.Framework.RegionsSub
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
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Extra
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullStart
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.InitCore
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Memory
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reinit
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
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # The initial paired matrix parse observes only the public seed -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem

def prepareCode (sb ss a b k : Nat) : Prog isa :=
 .seq (.seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b k)) Impl.MlKem.AArch64.Paired.squeeze)
   (.block Impl.MlKem.AArch64.Rej8.rejConsts)
def prepareRegs : List Reg := startRegs++[.x9,.x16]

structure BeginInput (sb ss oa ob : Nat) (p seed outA outB table : Addr) (s : State) : Prop where
 ptr : s.gpr .x28+BitVec.ofNat 64 ss=p
 seedPtr : s.gpr .x28+BitVec.ofNat 64 sb=seed
 outLeft : s.gpr .x28+BitVec.ofNat 64 oa=outA
 outRight : s.gpr .x28+BitVec.ofNat 64 ob=outB
 readable : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8
 separate : (Region.mk seed 32).Disjoint ⟨p,2048⟩
 context : Context p outA outB table s
 symbol : s.syms "VG_MLKEM_REJ_SHUFFLE"=table

structure PreparedW (w16 : Bool) (A B : Spec.Sha3.State) (oa ob : Nat) (p table : Addr) (s t : State) : Prop where
 keep : Keep prepareRegs s t
 ready : InitialReadyW w16 (shakeStream A) (shakeStream B) oa ob t
 pointer : t.gpr .x19=p
 tablePtr : t.gpr .x16=table

abbrev Prepared := PreparedW false

theorem prepare_ok {w16 : Bool} {s : State} {p seed outA outB table : Addr} {sb ss a b k oa ob : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (h : BeginInput sb ss oa ob p seed outA outB table s) :
    WP isa (prepareCode sb ss a b k) s
      (PreparedW w16 (seedState s.mem seed a k) (seedState s.mem seed b k) oa ob p table s) := by
  refine WP.seq (WP.mono_syms (start_ok (a:=a) (b:=b) (k:=k) hss hsb h8
    h.ptr h.seedPtr h.readable h.context.scratch h.separate) fun u ⟨ku,fu,_,u19,_,_,buA,buB⟩ sy => ?_)
  have cu : Context p outA outB table u := h.context.frame ku.rd ku.wr (fu.mono (by simp [stepWrites]))
  refine WP.mono_syms (Rej8.constants_ok u (by
    rw [u19]; exact Noise.inScratch cu.scratch (by decide) (by decide))) fun v ⟨kv,cv,mv,tv⟩ syv => ?_
  have fv : Frame [⟨p+1408,8⟩] u.mem v.mem := by
    rw [mv,u19]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
  have fvBig : Frame (stepWrites p outA outB) u.mem v.mem := fv.sub (by
    intro r hr; rw [List.mem_singleton.mp hr]
    exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩)
  have ctv := cu.frame kv.rd kv.wr fvBig
  have v19 : v.gpr .x19=p := (kv.get .x19).trans u19
  have v28 : v.gpr .x28=s.gpr .x28 := (kv.get .x28).trans (ku.get .x28)
  have v16 : v.gpr .x16=table := by rw [tv,syv,sy,h.symbol]
  have streamA : ∀i<504,v.mem ((p+400)+BitVec.ofNat 64 i)=shakeStream (seedState s.mem seed a k) i := by
    intro i hi
    have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+400) 504).Disjoint r := by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint p (by decide) (by decide) (by decide)
    exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (buA.byte hi)
  have streamB : ∀i<504,v.mem ((p+904)+BitVec.ofNat 64 i)=shakeStream (seedState s.mem seed b k) i := by
    intro i hi
    have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+904) 504).Disjoint r := by
      intro r hr; rw [List.mem_singleton.mp hr]
      exact Offset.disjoint p (by decide) (by decide) (by decide)
    exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (buB.byte hi)
  have ea := ctv.envW (w16 := w16) (N:=168) (off:=400) v16 (by decide) (by decide) (Or.inl rfl) streamA
  have eb := ctv.envW (w16 := w16) (N:=168) (off:=904) v16 (by decide) (by decide) (Or.inr rfl) streamB
  refine ⟨(ku.trans kv).mono (by simp [prepareRegs]),?_,v19,v16⟩
  refine ⟨⟨?_,cv,?_,?_,?_⟩,⟨?_,cv,?_,?_,?_⟩,?_,?_⟩
  · rw [v19,v28,h.outLeft]; exact ea
  · rw [v19]; exact Noise.inScratch ctv.scratch (by decide) (by decide)
  · rw [v19]; exact Noise.inScratch ctv.scratch (by decide) (by decide)
  · rw [v19,v28,h.outLeft]; exact ctv.farA.symm.sub_right (Offset.sub_base p (by decide))
  · rw [v19,v28,h.outRight]; exact eb
  · rw [v19]; exact Noise.inScratch ctv.scratch (by decide) (by decide)
  · rw [v19]; exact Noise.inScratch ctv.scratch (by decide) (by decide)
  · rw [v19,v28,h.outRight]; exact ctv.farB.symm.sub_right (Offset.sub_base p (by decide))
  · rw [v19,v28,h.outLeft]; exact ctv.farA.symm
  · intro mask hm; rw [v19,v16]; exact ctv.tableScratch.sub_left (Rej8.table_sub table hm)

theorem prepare_ct (sb ss a b k : Nat) : ConstantTime isa (fun _=>True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x28])) (prepareCode sb ss a b k) := by
  by_cases hs : ss<4096
  · apply ct_eraseOff_eq [.x28]
      (d:=Code.eraseOff (prepareCode 0 0 0 0 1))
      (by simp only [prepareCode,Impl.MlKem.AArch64.Paired.init,Impl.MlKem.AArch64.ptrTo,ite_eq_left hs]; rfl)
    taint_decide
  · apply ct_eraseOff_eq [.x28]
      (d:=Code.eraseOff (prepareCode 0 4096 0 0 1))
      (by simp only [prepareCode,Impl.MlKem.AArch64.Paired.init,Impl.MlKem.AArch64.ptrTo,ite_eq_right hs]; rfl)
    taint_decide

theorem begin_relCT {w16 : Bool} {s u : State} {p seed outA outB table : Addr} {sb ss a b k oa ob : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoa : oa<65536) (hob : ob<65536)
    (ps : BeginInput sb ss oa ob p seed outA outB table s) (pu : BeginInput sb ss oa ob p seed outA outB table u)
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedA : seedState s.mem seed a k=seedState u.mem seed a k)
    (seedB : seedState s.mem seed b k=seedState u.mem seed b k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (beginCode sb ss a b k oa ob w16)
      (fun t v=>BeginPostW w16 (seedState s.mem seed a k) (seedState s.mem seed b k) p outA outB table s t ∧
        BeginPostW w16 (seedState u.mem seed a k) (seedState u.mem seed b k) p outA outB table u v) := by
  let R := fun t v : State=>PreparedW w16 (seedState s.mem seed a k) (seedState s.mem seed b k) oa ob p table s t ∧
    PreparedW w16 (seedState u.mem seed a k) (seedState u.mem seed b k) oa ob p table u v
  have start : RelCT isa (fun t v=>t=s ∧ v=u) (prepareCode sb ss a b k) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    exact ⟨prepare_ct sb ss a b k s u tr ur t' v' trivial trivial
      (agree_of sp (by intro r hr; rw [List.mem_singleton.mp hr]; exact base)) et ev,
      exec_post (prepare_ok hss hsb h8 ps) et,exec_post (prepare_ok hss hsb h8 pu) ev⟩
  have grouped : RelCT isa (fun t v=>t=s ∧ v=u)
      (.seq (prepareCode sb ss a b k) (initialCode oa ob w16)) (fun _ _=>True) := by
    refine RelCT.seq start ?_
    intro t v tr ur t' v' h et ev
    exact initial_relCT hoa hob h.1.ready (by rw [seedA,seedB]; exact h.2.ready)
      (h.1.keep.sp.trans (sp.trans h.2.keep.sp.symm))
      (h.1.pointer.trans h.2.pointer.symm)
      (by rw [h.1.keep.get .x28,h.2.keep.get .x28,base])
      (h.1.tablePtr.trans h.2.tablePtr.symm) t v tr ur t' v' ⟨rfl,rfl⟩ et ev
  have trace : RelCT isa (fun t v=>t=s ∧ v=u) (beginCode sb ss a b k oa ob w16) (fun _ _=>True) :=
    RelCT.assoc (RelCT.assoc grouped)
  intro t v tr ur t' v' h et ev
  rcases h with ⟨ht,hv⟩; subst t; subst v
  exact ⟨(trace s u tr ur t' v' ⟨rfl,rfl⟩ et ev).1,
    exec_post (begin_ok hss hsb h8 hoa hob ps.ptr ps.seedPtr ps.outLeft ps.outRight ps.readable ps.separate ps.context ps.symbol) et,
    exec_post (begin_ok hss hsb h8 hoa hob pu.ptr pu.seedPtr pu.outLeft pu.outRight pu.readable pu.separate pu.context pu.symbol) ev⟩

end VG.Proof.MlKem.AArch64.Paired
