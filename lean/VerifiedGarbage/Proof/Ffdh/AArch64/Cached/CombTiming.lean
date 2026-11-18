module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Step
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Phases
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Gather
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ConstTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectScan

/-! ### `Ffdh.AArch64.Cached.RowTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.SelectionTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.ScanTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.SelectTiming`, which only this module used -/

section

/-! Table masks may be secret. Only public pointers and loop counts control the trace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum.AArch64

/-- Loading the public header and computing a secret equality mask has no secret trace. -/
theorem selectHead_ct :
 RelCT isa (Two fun (B : Addr) s => s.gpr .x0=B)
 (.block VG.Impl.Ffdh.AArch64.Cached.Comb.selectHead) (fun _ _ => True) := by
 apply two_taint [.x0]
 · intro B s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   subst r
   exact hs.trans ht.symm
 · taint_decide

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The complete 32-entry scan has a public fixed schedule, independently of its digit. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)

structure ScanPublic where
 B : Addr
 table : Addr
 dst : Addr
 w : Nat
 positive : 0<w
 fit : 8*w≤2^64

structure ScanReady (p : ScanPublic) (j : Nat) (s : State) : Prop where
 env : SelectEnv p.B p.table p.dst p.w s
 pointer : s.gpr .x9=off p.table (8*p.w*j)
 candidate : s.gpr .x11=BitVec.ofNat 64 j
 digit : ∃ v, v<32 ∧ s.gpr .x10=BitVec.ofNat 64 v

theorem scanStep_ct :
 RelCT isa (Two fun (q : ScanPublic × Nat) s => q.2<32 ∧ ScanReady q.1 q.2 s)
 Comb.selectStep (fun _ _ => True) := by
 unfold Comb.selectStep
 refine RelCT.seq (two_post (Ψ:=fun (q : ScanPublic × Nat) s =>
  s.gpr .x9=off q.1.table (8*q.1.w*q.2) ∧ s.gpr .x8=q.1.dst ∧
  s.gpr .x12=BitVec.ofNat 64 q.1.w ∧ s.gpr .x11=BitVec.ofNat 64 q.2)
  (two_map (fun q => q.1.B) (fun _ _ h => h.2.env.base) selectHead_ct) ?_)
  (two_taint [.x9,.x8,.x12,.x11] ?_ (by taint_decide))
 · rintro ⟨p,j⟩ s ⟨hj,h⟩
   obtain ⟨v,hv,digit⟩ := h.digit
   refine WP.mono (selectHead_ok h.env hv hj digit h.candidate) ?_
   rintro t ⟨⟨dst,count,_,_⟩,rest⟩
   exact ⟨(rest.gpr .x9 (by decide)).trans h.pointer,dst,count,
    (rest.gpr .x11 (by decide)).trans h.candidate⟩
 · intro q s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl | rfl | rfl | rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.1.trans ht.2.2.1.symm
   · exact hs.2.2.2.trans ht.2.2.2.symm

private theorem scanCounter : ∀ j<32,
 (BitVec.ofNat 64 (j+1)-32#64 != 0#64)=decide (j+1<32) := by decide +kernel

theorem scan_ct : RelCT isa (Two fun p s => ScanReady p 0 s)
 (.loop Comb.selectStep (.nonzero .x .x3)) (fun _ _ => True) := by
 have loop := two_loop (Φ:=ScanReady) (Ψ:=fun _ _ => True) (fun _ : ScanPublic => 32)
  scanStep_ct (by
   intro p j s hj h
   obtain ⟨v,hv,digit⟩ := h.digit
   refine WP.mono (selectStep_ok h.env p.positive p.fit hv hj digit h.candidate h.pointer) ?_
   rintro t ⟨env,_,_,pointer,digit,candidate,counter,_⟩
   refine ⟨?_,fun _ => ⟨env,pointer,candidate,v,hv,digit⟩,fun _ => trivial⟩
   rw [eval_nonzero,counter]
   exact congrArg some (scanCounter j hj))
 exact loop.mono (fun _ _ ⟨p,hs,ht,sp⟩ => ⟨p,⟨by decide,hs⟩,⟨by decide,ht⟩,sp⟩)
  (fun _ _ _ => trivial)

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Complete selection, including zero initialization and public header loads. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def SelectionReady (p : Parameters) (s : State) : Prop :=
 ∃ bs E i v, Running p bs E i s ∧ v<32 ∧ word s.mem p.B (8*sD)=BitVec.ofNat 64 v

def scanPublic (p : Parameters) : ScanPublic :=
 ⟨p.B,p.table,off p.B (slot p.w 5),p.w,by have := p.positive;omega_using [this],by have := p.width;omega_using [this]⟩

theorem selection_ct : RelCT isa (Two SelectionReady) Comb.select (fun _ _ => True) := by
 unfold Comb.select
 refine RelCT.seq (two_post (Ψ:=SelectionReady)
  (two_map (fun p : Parameters => (⟨p.B,p.Z,p.w⟩ : Ws))
   (fun p s h => by obtain ⟨bs,E,i,v,h,_,_⟩:=h;exact ⟨p.mi,h.power.good,p.room⟩)
   (const_ct 5 0 (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
 · rintro p s ⟨bs,E,i,v,h,hv,digit⟩
   refine WP.mono (const_ok h.power.good p.room (by have := p.positive;omega_using [this]) p.width
    (by decide : 5<8) (by decide : 0<2^16)) ?_
   rintro t ⟨good,_,outside,rest⟩
   have frame : Arrays p.B p.w [5] s.mem t.mem := Arrays.of_outside (j:=5) (by simp) outside
    (by have := p.positive;omega_using []) (by have := h.power.good.scr.nowrap;have := p.room;have := slot_le (w:=p.w) (by decide : 5<8);omega_using [])
   have power := h.power.after_arrays good frame (by decide) (by decide) (by decide) (by decide)
   have keep := rest.mono (show ∀ r∈[.x7,.x8,.x9,.x12,.x13,.x14,.x16],r∈mmRegs by decide)
   exact ⟨bs,E,i,v,h.after_arrays power frame keep (by simp),hv,(arrays_header frame (by decide)).trans digit⟩
 · refine RelCT.seq (two_piece (Ψ:=fun p s => ScanReady (scanPublic p) 0 s) [.x0] ?_ (by taint_decide) ?_)
    (two_map scanPublic (fun _ _ h => h) scan_ct)
   · rintro p s t ⟨bs,E,i,v,hs,_,_⟩ ⟨bt,F,j,u,ht,_,_⟩ r hr
     have : r= .x0 := by simpa using hr
     subst r
     exact hs.power.good.x0.trans ht.power.good.x0.symm
   · rintro p s ⟨bs,E,i,v,h,hv,digit⟩
     refine WP.mono (WP.keep [.x9,.x10,.x11] (Q:=fun t =>
      t.gpr .x9=p.table ∧ t.gpr .x10=BitVec.ofNat 64 v ∧ t.gpr .x11=0#64 ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
     · have table : word s.mem p.B (8*sTab)=p.table := h.tablePointer
       brun [h.power.good.x0,hdr_enc (show sTab<32 by decide),hdr_enc (show sD<32 by decide),
        header_read h.power.good p.room (show sTab<32 by decide),
        header_read h.power.good p.room (show sD<32 by decide),table,digit]
     · rintro t ⟨⟨pointer,digit,candidate,mem⟩,rest⟩
       have hT := h.after_mem mem (rest.mono (by decide))
       refine ⟨selectEnv_good hT.power.good p.room (by have := p.positive;omega_using [this])
        hT.reads.tableRead hT.reads.tableOutside,?_,candidate,v,hv,digit⟩
       simpa [scanPublic,off] using pointer

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.DigitTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.GatherTiming`, which only this module used -/

section

/-! Secret scalar bytes and digit accumulators never control an address or branch. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Proof.Bignum.AArch64

structure GatherPublic where
 source : Addr
 length : BitVec 64
 row : BitVec 64
 spacing : BitVec 64
 bits : BitVec 64

def GatherReady (p : GatherPublic) (s : State) : Prop :=
 s.gpr .x1=p.source ∧ s.gpr .x2=p.length ∧ s.gpr .x9=p.row ∧ s.gpr .x4=p.spacing ∧ s.gpr .x5=p.bits

/-- Neither scalar bytes nor the partial digit must agree between the runs. -/
theorem gather_ct : RelCT isa (Two GatherReady) VG.Impl.Ffdh.AArch64.Cached.Comb.gather (fun _ _ => True) := by
 apply two_taint [.x1,.x2,.x9,.x4,.x5]
 · intro p s t hs ht r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl | rfl | rfl | rfl | rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.1.trans ht.2.2.1.symm
   · exact hs.2.2.2.1.trans ht.2.2.2.1.symm
   · exact hs.2.2.2.2.trans ht.2.2.2.2.symm
 · taint_decide

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Scalar digit extraction permits independent secret byte strings in the two runs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure DigitPublic where
 p : Parameters
 i : Nat
 size : p.k<2^31
 width : p.N≤8*p.k
 positions : i+5*Spec.Rsa.FixedBaseComb.rows p.N<2^63

def DigitReady (q : DigitPublic) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E (q.i+1) s

structure DigitGather (q : DigitPublic) (s : State) : Prop where
 base : s.gpr .x0=q.p.B
 regs : GatherReady ⟨q.p.src,BitVec.ofNat 64 q.p.k,BitVec.ofNat 64 q.i,
  BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.p.N),BitVec.ofNat 64 q.p.N⟩ s
 bytes : ∃ bs, Source q.p.src bs s ∧ bs.length=q.p.k ∧ s.gpr .x16=0#64

theorem digit_ct : RelCT isa (Two DigitReady) Comb.digit (fun _ _ => True) := by
 unfold Comb.digit
 refine RelCT.seq (two_piece (Ψ:=DigitGather) [.x0] ?_ (by taint_decide) ?_) ?_
 · rintro q s t ⟨bs,E,hs⟩ ⟨bt,F,ht⟩ r hr
   have : r= .x0 := by simpa using hr
   subst r
   exact hs.power.good.x0.trans ht.power.good.x0.symm
 · rintro q s ⟨bs,E,h⟩
   refine WP.mono (digitArgs_ok h.power.good q.p.room h.controls h.counter (by have := q.positions;omega_using [this])) ?_
   rintro t ⟨⟨ptr,len,row,spacing,width,zero,mem⟩,rest⟩
   refine ⟨(rest.gpr .x0 (by decide)).trans h.power.good.x0,?_,bs,h.reads.source.of_mem mem rest,h.reads.length,zero⟩
   exact ⟨ptr,h.reads.length ▸ len,row,spacing,width⟩
 · refine RelCT.seq (two_post (Ψ:=fun q s => s.gpr .x0=q.p.B) (two_map (fun q : DigitPublic =>
    (⟨q.p.src,BitVec.ofNat 64 q.p.k,BitVec.ofNat 64 q.i,
     BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.p.N),BitVec.ofNat 64 q.p.N⟩ : GatherPublic))
    (fun _ _ h => h.regs) gather_ct) ?_) ?_
   · intro q s h
     obtain ⟨bs,source,length,zero⟩ := h.bytes
     refine WP.mono (gather_ok s source (length ▸ q.size) (length ▸ q.width) q.positions
      h.regs.1 (length ▸ h.regs.2.1) h.regs.2.2.1 h.regs.2.2.2.2 h.regs.2.2.2.1 zero) ?_
     rintro t ⟨_,_,rest⟩
     exact (rest.gpr .x0 (by simp [gatherClobbers])).trans h.base
   · apply two_taint [.x0]
     · intro q s t hs ht r hr
       have : r= .x0 := by simpa using hr
       subst r
       exact hs.trans ht.symm
     · taint_decide

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! One complete comb row is constant time for independent secret exponents. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def RowReady (q : DigitPublic) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E (q.i+1) s ∧ Spec.Rsa.os2ip bs<2^q.p.N

def RowDigit (q : DigitPublic) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E (q.i+1) s ∧ Spec.Rsa.os2ip bs<2^q.p.N ∧
 word s.mem q.p.B (8*sD)=BitVec.ofNat 64 (VG.Proof.Rsa.FixedBaseComb.digit q.p.N (Spec.Rsa.os2ip bs) q.i)

def RowProduct (q : DigitPublic) (s : State) : Prop :=
 ∃ bs E F, Running q.p bs E (q.i+1) s ∧ Spec.Rsa.os2ip bs<2^q.p.N ∧
 wv s.mem q.p.B (slot q.p.w 5) q.p.w=Spec.Rsa.powMod q.p.G F q.p.P*2^(64*q.p.w)%q.p.P

def digitWs (q : DigitPublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

theorem row_ct (M : Mont) : RelCT isa (Two RowReady) (Comb.step M.mm) (fun _ _ => True) := by
 unfold Comb.step
 refine RelCT.seq (two_post (Ψ:=RowReady)
  (two_map digitWs (fun q s h => by obtain ⟨bs,E,h,_⟩:=h;exact ⟨q.p.mi,h.power.good,q.p.room⟩)
   (M.ct (by simp [MmUse,Public.aY] : MmUse 6 6 6))) ?_) ?_
 · rintro q s ⟨bs,E,h,bound⟩
   exact WP.mono (running_square M h) fun _ h => ⟨bs,2*E,h,bound⟩
 · refine RelCT.seq (two_post (Ψ:=RowDigit)
    (two_map id (fun _ _ h => by obtain ⟨bs,E,h,_⟩:=h;exact ⟨bs,E,h⟩) digit_ct) ?_) ?_
   · rintro q s ⟨bs,E,h,bound⟩
     refine WP.mono (running_digit h (h.reads.length ▸ q.size) (h.reads.length ▸ q.width) q.positions bound) ?_
     rintro t ⟨run,digit⟩
     exact ⟨bs,E,run,bound,digit⟩
   · refine RelCT.seq (two_post (Ψ:=RowProduct)
      (two_map (fun q : DigitPublic => q.p) (fun q s h => by
       obtain ⟨bs,E,h,_,digit⟩:=h
       exact ⟨bs,E,q.i+1,_,h,VG.Proof.Rsa.FixedBaseComb.digit_lt _ _ _,digit⟩) selection_ct) ?_) ?_
     · rintro q s ⟨bs,E,h,bound,digit⟩
       refine WP.mono (running_select h (VG.Proof.Rsa.FixedBaseComb.digit_lt _ _ _) digit) ?_
       rintro t ⟨run,selected⟩
       exact ⟨bs,E,_,run,bound,selected⟩
     · refine RelCT.seq (two_post (Ψ:=RowReady)
        (two_map digitWs (fun q s h => by obtain ⟨bs,E,F,h,_,_⟩:=h;exact ⟨q.p.mi,h.power.good,q.p.room⟩)
         (M.ct (by simp [MmUse,Public.aY,Public.aXm] : MmUse 6 6 5))) ?_)
        (two_taint [.x0] ?_ (by taint_decide))
       · rintro q s ⟨bs,E,F,h,bound,selected⟩
         exact WP.mono (running_product M h selected) fun _ h => ⟨bs,E+F,h,bound⟩
       · rintro q s t ⟨bs,E,hs,_⟩ ⟨bt,F,ht,_⟩ r hr
         have : r= .x0 := by simpa using hr
         subst r
         exact hs.power.good.x0.trans ht.power.good.x0.symm

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.Comb`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.InitControls`, which only this module used -/

section

/-! Store the policy's exact row count and canonical packed-table pointer. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem counter_ok {p : Parameters} {bs : List Byte} {s : State}
 (good : Good s p.B p.Z p.w p.mi) (controls : Controls p.B p.src p.ctx bs.length p.N s) :
 WP isa (.block Comb.initCounter) s fun t =>
 Good t p.B p.Z p.w p.mi ∧ Counter p.B (Spec.Rsa.FixedBaseComb.rows p.N) t ∧
 Outside p.B (8*sI) 8 s.mem t.mem ∧ Keep [.x3] s t := by
 unfold Comb.initCounter
 refine WP.mono (WP.keep [.x3] (Q:=fun t =>t.mem=s.mem.writeW (off p.B (8*sI))
  (BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows p.N))) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sI<32 by decide),hdr_enc (show sRows<32 by decide),
   header_read good p.room (show sRows<32 by decide),controls.rows,
   good.scr.st (d:=8*sI) (by have := hdr_lt_slot p.w 8 (show sI<32 by decide);have := p.room;omega_arith)]
 · rintro t ⟨mem,rest⟩
   have frame : Outside p.B (8*sI) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by decide)
   refine ⟨good_after_header good (by decide) (by decide) frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   unfold Counter
   rw [mem,word_writeW_self]

private theorem table_ok {p : Parameters} {bs : List Byte} {s : State}
 (good : Good s p.B p.Z p.w p.mi) (controls : Controls p.B p.src p.ctx bs.length p.N s)
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w)) :
 WP isa (.block Comb.initTable) s fun t =>
 Good t p.B p.Z p.w p.mi ∧ TablePointer p.B p.table t ∧
 Outside p.B (8*sTab) 8 s.mem t.mem ∧ Keep [.x3,.x4] s t := by
 have shift : BitVec.ofNat 64 p.w <<< 4=BitVec.ofNat 64 (16*p.w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq]
  have := p.width
  omega_using []
 have address : (p.ctx+(BitVec.ofNat 64 p.w <<< 4))+24#64=p.table := by
  rw [shift,pointer,BitVec.add_assoc,show (24#64:Addr)=BitVec.ofNat 64 24 from rfl,←BitVec.ofNat_add]
  congr 2
  omega_using []
 unfold Comb.initTable
 refine WP.mono (WP.keep [.x3,.x4] (Q:=fun t =>t.mem=s.mem.writeW (off p.B (8*sTab)) p.table)
  ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sW<32 by decide),hdr_enc (show sTab<32 by decide),
   header_read good p.room (show sCtx<32 by decide),header_read good p.room (show sW<32 by decide),
   good.hdr.hw,controls.context,address,
   good.scr.st (d:=8*sTab) (by have := hdr_lt_slot p.w 8 (show sTab<32 by decide);have := p.room;omega_arith)]
 · rintro t ⟨mem,rest⟩
   have frame : Outside p.B (8*sTab) 8 s.mem t.mem := by rw [mem];exact writeW_outside _ _ _ (by decide)
   refine ⟨good_after_header good (by decide) (by decide) frame rest ((rest.gpr .x0 (by decide)).trans good.x0),?_,frame,rest⟩
   unfold TablePointer
   rw [mem,word_writeW_self]

theorem init_controls {p : Parameters} {bs : List Byte} {s : State}
 (power : Power p 0 s) (controls : Controls p.B p.src p.ctx bs.length p.N s) (reads : ReadEnv p bs s)
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w)) :
 WP isa (.seq (.block Comb.initCounter) (.block Comb.initTable)) s fun t =>
 Running p bs 0 (Spec.Rsa.FixedBaseComb.rows p.N) t ∧ StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 rw [WP.seq_iff]
 refine WP.mono (counter_ok power.good controls) ?_
 rintro u ⟨goodU,counterU,frameU,keepU⟩
 have powerU := power.after_header goodU frameU (by decide : sI<32)
 have controlsU := controls.after_counter frameU
 have readsU := reads.after_header frameU keepU (by decide : sI<32)
 refine WP.mono (table_ok goodU controlsU pointer) ?_
 rintro t ⟨goodT,tableT,frameT,keepT⟩
 refine ⟨⟨powerU.after_header goodT frameT (by decide : sTab<32),controlsU.after_table frameT,?_,tableT,
  readsU.after_header frameT keepT (by decide : sTab<32)⟩,?_,(keepU.trans keepT).mono (by decide)⟩
 · exact (header_other frameT (by decide) (by decide) (by decide)).trans counterU
 · exact (StableHeader.of_control frameU (Or.inl rfl)).trans (StableHeader.of_control frameT (Or.inr (Or.inr rfl)))

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The complete native cached exponentiation, from canonical R² to ordinary g^x. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Loop.lean`, which only this module imported.
section

/-! The complete fixed public row schedule reconstructs the unrevealed scalar. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Spec.Rsa.FixedBaseComb (rows exponent)
open VG.Proof.Rsa.FixedBaseComb (high high_step high_top high_zero rows_pos rows_small)

theorem comb_loop (M : Mont) {p : Parameters} {bs : List Byte} {s : State}
 (start : Running p bs 0 (rows p.N) s) (positive : 0<p.N) (width : p.N≤8192)
 (size : bs.length<2^31) (widthBound : p.N≤8*bs.length) (bound : Spec.Rsa.os2ip bs<2^p.N) :
 WP isa (.loop (Comb.step M.mm) (.nonzero .x .x3)) s fun t =>
 Running p bs (Spec.Rsa.os2ip bs) 0 t ∧ StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 let x := Spec.Rsa.os2ip bs
 let d := rows p.N
 have dPositive : 0<d := rows_pos positive
 have dBound : d≤1639 := (rows_small width).1
 let I := fun n t => 0<n ∧ n≤d ∧ Running p bs (high p.N x n) n t ∧
  StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t
 refine WP.loop (M:=isa) I ?_ d s ?_
 · intro n t h
   obtain ⟨nPositive,nBound,run,stable,keep⟩ := h
   have eq : n=(n-1)+1 := by omega_using [nPositive]
   have rowBound : n-1<rows p.N := by change n-1<d;omega_using [dPositive, nBound]
   have input : Running p bs (high p.N x ((n-1)+1)) ((n-1)+1) t := by rw [←eq];exact run
   refine WP.mono (running_step M input size widthBound (by change n-1+5*d<2^63;omega_using [dBound, nBound]) bound) ?_
   rintro u ⟨runU,stableU,indexU,keepU⟩
   have powerEq := high_step p.N x (n-1) rowBound
   rw [←powerEq] at runU
   have totalStable := stable.trans stableU
   have totalKeep : Keep mmRegs s u := (keep.trans keepU).mono (by simp)
   by_cases last : n=1
   · left
     refine ⟨?_,?_,totalStable,totalKeep⟩
     · rw [eval_nonzero,indexU]
       change some (BitVec.ofNat 64 (n-1) != 0#64)=some false
       subst n;decide
     · simpa only [last,Nat.sub_self,high_zero p.N x bound] using runU
   · right
     refine ⟨?_,n-1,by omega_using [nPositive],by omega_using [nPositive, last],by omega_using [nBound],runU,totalStable,totalKeep⟩
     rw [eval_nonzero,indexU]
     change some (BitVec.ofNat 64 (n-1) != 0#64)=some true
     rw [ofNat_nonzero (by omega_using [dBound, nBound] : n-1<2^64),decide_eq_true (by omega_using [nPositive, last] : 0<n-1)]
 · refine ⟨dPositive,Nat.le_refl _,?_,StableHeader.refl _ _,Keep.refl _ _⟩
   simpa only [d,high_top] using start

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/Decode.lean`, which only this module imported.
section

/-! Conversion out of Montgomery form produces exactly the ordinary public value. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem power_decode (M : Mont) {p : Parameters} {E : Nat} {s : State} (h : Power p E s) :
 WP isa (M.mm 6 6 7) s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P ∧
 Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound7 : wv s.mem p.B (slot p.w 7) p.w<p.P := by rw [h.one];exact p.modulusPositive
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 7<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound7) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have eq : wv t.mem p.B (slot p.w 6) p.w*2^(64*p.w)%p.P=
  Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P := by
  simpa only [h.one,h.value,Nat.mul_one,Nat.mod_mod] using productT
 have cancel := VG.Proof.Bignum.mont_cancel p.coprime eq
 rw [Nat.mod_eq_of_lt boundT] at cancel
 have decoded : wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P := by
  simpa only [VG.Proof.Bignum.powMod_eq,Nat.mod_mod] using cancel
 exact ⟨modT,decoded,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem reassoc {a b c : Prog isa} {s : State} {Q : State → Prop} :
 WP isa (.seq a (.seq b c)) s Q ↔ WP isa (.seq (.seq a b) c) s Q := by
 exact ⟨WP.assoc',WP.assoc⟩

theorem comb_correct (M : Mont) {p : Parameters} {bs : List Byte} {s : State}
 (start : Initial p bs s) (positive : 0<p.N) (width : p.N≤8192)
 (size : bs.length<2^31) (widthBound : p.N≤8*bs.length) (bound : Spec.Rsa.os2ip bs<2^p.N)
 (pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w)) :
 WP isa (VG.Impl.Ffdh.AArch64.Cached.Comb.code M.mm) s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G (Spec.Rsa.os2ip bs) p.P ∧
 Controls p.B p.src p.ctx bs.length p.N t ∧ ReadEnv p bs t ∧
 StableHeader p.B s.mem t.mem ∧ Keep mmRegs s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.code
 rw [reassoc,WP.seq_iff]
 refine WP.mono (initial_power M start) ?_
 rintro a ⟨powerA,controlsA,readsA,stableA,keepA⟩
 rw [reassoc,WP.seq_iff]
 refine WP.mono (init_controls powerA controlsA readsA pointer) ?_
 rintro b ⟨runB,stableB,keepB⟩
 rw [WP.seq_iff]
 refine WP.mono (comb_loop M runB positive width size widthBound bound) ?_
 rintro c ⟨runC,stableC,keepC⟩
 refine WP.mono (power_decode M runC.power) ?_
 rintro t ⟨modT,valueT,frameT,keepT⟩
 exact ⟨modT,valueT,runC.controls.after_arrays frameT,runC.reads.after_arrays frameT keepT (by simp),
  ((stableA.trans stableB).trans stableC).trans (StableHeader.of_arrays frameT),
  (((keepA.trans keepB).trans keepC).trans keepT).mono (by simp)⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.LoopTiming`, which only this module used -/

section

/-! The complete loop count depends only on the public policy width. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Spec.Rsa.FixedBaseComb (rows)
open VG.Proof.Rsa.FixedBaseComb (rows_pos rows_small)

structure LoopPublic where
 p : Parameters
 positive : 0<p.N
 width : p.N≤8192
 size : p.k<2^31
 scalarWidth : p.N≤8*p.k

def LoopReady (q : LoopPublic) (j : Nat) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E (rows q.p.N-j) s ∧ Spec.Rsa.os2ip bs<2^q.p.N

def LoopDone (q : LoopPublic) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E 0 s

def loopDigit (q : LoopPublic) (j : Nat) : DigitPublic :=
 ⟨q.p,rows q.p.N-j-1,q.size,q.scalarWidth,by have := (rows_small q.width).1;omega_using [this]⟩

theorem loop_ct (M : Mont) : RelCT isa (Two fun q s => LoopReady q 0 s)
 (.loop (Comb.step M.mm) (.nonzero .x .x3)) (Two LoopDone) := by
 have hct : RelCT isa (Two fun (q : LoopPublic × Nat) s => q.2<rows q.1.p.N ∧ LoopReady q.1 q.2 s)
   (Comb.step M.mm) (fun _ _ => True) :=
  two_map (fun q => loopDigit q.1 q.2) (by
   rintro ⟨q,j⟩ s ⟨hj,bs,E,h,bound⟩
   change j<rows q.p.N at hj
   refine ⟨bs,E,?_,bound⟩
   change Running q.p bs E ((rows q.p.N-j-1)+1) s
   have eq : rows q.p.N-j=(rows q.p.N-j-1)+1 := by omega_using [hj]
   rw [←eq]
   exact h) (row_ct M)
 have loop := two_loop (Φ:=LoopReady) (Ψ:=LoopDone) (fun q => rows q.p.N) hct (by
   intro q j s hj h
   obtain ⟨bs,E,h,bound⟩ := h
   have dBound := (rows_small q.width).1
   have eq : rows q.p.N-j=(rows q.p.N-j-1)+1 := by omega_using [hj]
   have run : Running q.p bs E ((rows q.p.N-j-1)+1) s := by rw [←eq];exact h
   refine WP.mono (running_step M run (h.reads.length ▸ q.size) (h.reads.length ▸ q.scalarWidth)
    (by omega_using [dBound]) bound) ?_
   rintro t ⟨next,_,index,_⟩
   have remaining : rows q.p.N-j-1=rows q.p.N-(j+1) := by omega_using []
   refine ⟨?_,fun _ => ⟨bs,_,remaining ▸ next,bound⟩,fun last => ?_⟩
   · rw [eval_nonzero,index]
     change some (BitVec.ofNat 64 (rows q.p.N-j-1) != 0#64)=some (decide (j+1<rows q.p.N))
     rw [ofNat_nonzero (by omega_using [dBound])]
     have eqBool : (0<rows q.p.N-j-1) ↔ (j+1<rows q.p.N) := by omega_using []
     simp only [eqBool]
   · have zero : rows q.p.N-j-1=0 := by omega_using [last]
     exact ⟨bs,_,zero ▸ next⟩)
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>
  ⟨q,⟨rows_pos q.positive,hs⟩,⟨rows_pos q.positive,ht⟩,sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! Complete cached exponentiation with independent secret scalars and public policy geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure CombPublic extends LoopPublic where
 pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w)

def CombReady (q : CombPublic) (s : State) : Prop :=
 ∃ bs, Initial q.p bs s ∧ Spec.Rsa.os2ip bs<2^q.p.N

def InitReady (q : CombPublic) (s : State) : Prop :=
 ∃ bs, Power q.p 0 s ∧ Controls q.p.B q.p.src q.p.ctx bs.length q.p.N s ∧
 ReadEnv q.p bs s ∧ Spec.Rsa.os2ip bs<2^q.p.N

def combWs (q : CombPublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

theorem powerInit_ct (M : Mont) : RelCT isa (Two CombReady)
 (.seq (const 7 1) (M.mm 6 4 7)) (fun _ _ => True) := by
 refine RelCT.seq (two_post (Ψ:=fun q s => GoodW (combWs q) s)
  (two_map combWs (fun q s h => by obtain ⟨bs,h,_⟩:=h;exact ⟨q.p.mi,h.good,q.p.room⟩)
   (const_ct 7 1 (by decide) (by taint_decide) (by taint_decide))) ?_)
  (two_map combWs (fun _ _ h => h) (M.ct (by simp [MmUse,Public.aY,Public.aR2,Public.aOne])))
 rintro q s ⟨bs,h,_⟩
 exact WP.mono (const_ok h.good q.p.room (by have := q.p.positive;omega_using [this]) q.p.width
  (by decide : 7<8) (by decide : 1<2^16)) fun _ ⟨good,_,_,_⟩ => ⟨q.p.mi,good,q.p.room⟩

theorem comb_ct (M : Mont) : RelCT isa (Two CombReady) (Comb.code M.mm) (fun _ _ => True) := by
 unfold Comb.code
 apply RelCT.assoc
 refine RelCT.seq (two_post (Ψ:=InitReady) (powerInit_ct M) ?_) ?_
 · rintro q s ⟨bs,h,bound⟩
   exact WP.mono (initial_power M h) fun _ ⟨power,controls,reads,_,_⟩ => ⟨bs,power,controls,reads,bound⟩
 · apply RelCT.assoc
   refine RelCT.seq (two_piece (Ψ:=fun q s => LoopReady q.toLoopPublic 0 s) [.x0] ?_ (by taint_decide) ?_) ?_
   · rintro q s t ⟨bs,hs,_,_,_⟩ ⟨bt,ht,_,_,_⟩ r hr
     have : r= .x0 := by simpa using hr
     subst r
     exact hs.good.x0.trans ht.good.x0.symm
   · rintro q s ⟨bs,power,controls,reads,bound⟩
     exact WP.mono (init_controls power controls reads q.pointer) fun _ ⟨run,_,_⟩ => ⟨bs,0,run,bound⟩
   · refine RelCT.seq (two_map CombPublic.toLoopPublic (fun _ _ h => h) (loop_ct M)) ?_
     exact two_map (fun q : LoopPublic => (⟨q.p.B,q.p.Z,q.p.w⟩ : Ws))
      (fun q s h => by obtain ⟨bs,E,h⟩:=h;exact ⟨q.p.mi,h.power.good,q.p.room⟩)
      (M.ct (by simp [MmUse,Public.aY,Public.aOne]))

end VG.Proof.Ffdh.AArch64.Cached
