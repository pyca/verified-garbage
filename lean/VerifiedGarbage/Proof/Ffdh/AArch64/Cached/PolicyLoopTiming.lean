module

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTable
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs

/-! ### `Ffdh.AArch64.Cached.PolicyRecordTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PolicyMatchTiming`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.PolicyCompareTiming`, which only this module used -/

section

/-! Exact public-domain comparisons always scan their complete public length. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure ComparePublic where
 B : Addr
 Z : Nat
 src : Addr
 dst : Addr
 bs : List Byte
 cs : List Byte
 room : 256≤Z
 same : bs.length=cs.length
 positive : 0<bs.length
 size : bs.length<2^31

structure PolicyCompareReady (q : ComparePublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 domain : word s.mem q.B (8*sDom)=q.src
 length : word s.mem q.B (8*sDL)=BitVec.ofNat 64 q.bs.length
 pointer : s.gpr .x4=q.dst
 first : Source q.src q.bs s
 second : Source q.dst q.cs s

theorem policyCompare_ct : RelCT isa (Two PolicyCompareReady) Policy.compare (fun _ _ =>True) := by
 unfold Policy.compare
 refine RelCT.seq (two_piece (Ψ:=fun q s =>s.gpr .x1=q.src ∧ s.gpr .x2=q.dst ∧ s.gpr .x5=BitVec.ofNat 64 q.bs.length)
  [.x0,.x4] (fun q s t hs ht r hr =>by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact hs.base.trans ht.base.symm
   · exact hs.pointer.trans ht.pointer.symm) (by taint_decide) ?_)
  (two_taint [.x1,.x2,.x5] (fun q s t hs ht r hr =>by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl|rfl
   · exact hs.1.trans ht.1.symm
   · exact hs.2.1.trans ht.2.1.symm
   · exact hs.2.2.trans ht.2.2.symm) (by taint_decide))
 intro q s h
 brun [h.base,h.pointer,hdr_enc (show sDom<32 by decide),hdr_enc (show sDL<32 by decide),
  h.scratch.ld (d:=8*sDom) (by have :=q.room;unfold sDom;omega_using [this]),
  h.scratch.ld (d:=8*sDL) (by have :=q.room;unfold sDL;omega_using [this]),h.domain,h.length]

theorem policyCompare_agree {q : ComparePublic} {s : State} (h : PolicyCompareReady q s) :
 WP isa Policy.compare s fun t =>
 s.gpr .x0=t.gpr .x0 ∧ isa.eval (.zero .x .x11) t=some (decide (q.bs=q.cs)) := by
 refine WP.mono (policyCompare_ok h.scratch q.room h.base h.domain h.length h.pointer h.first h.second q.same q.positive q.size) ?_
 rintro t ⟨equal,_,rest⟩
 refine ⟨(rest.gpr .x0 (by simp [compareClobbers])).symm,?_⟩
 rw [VG.Proof.MlKem.AArch64.eval_zero]
 change some (t.gpr .x11==0#64)=_
 apply congrArg some
 apply Bool.eq_iff_iff.mpr
 simpa only [beq_iff_eq,decide_eq_true_eq] using equal

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! The exact-match branch is public because both complete domain encodings are public. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def CompareDone (q : ComparePublic) (s : State) : Prop :=
 s.gpr .x0=q.B ∧ isa.eval (.zero .x .x11) s=some (decide (q.bs=q.cs))

theorem compareChoice_ct : RelCT isa (Two PolicyCompareReady)
 (.seq Policy.compare (.ite (.zero .x .x11) (.block Policy.matched) (.block []))) (fun _ _ =>True) := by
 refine RelCT.seq (two_post (Ψ:=CompareDone) policyCompare_ct ?_) ?_
 · intro q s h
   exact WP.mono (policyCompare_agree h) (fun _ ⟨base,flag⟩ =>⟨base.symm.trans h.base,flag⟩)
 · refine RelCT.ite ?_ ?_ (RelCT.block_nil (fun _ _ _ =>trivial))
   · rintro s t ⟨q,hs,ht,_⟩
     exact hs.2.trans ht.2.symm
   · exact (two_taint [.x0] (Φ:=CompareDone) (fun q s t hs ht r hr =>by
      have eq : r= .x0 := by simpa using hr
      subst r;exact hs.1.trans ht.1.symm) (by taint_decide)).mono (fun _ _ h =>h.1) (fun _ _ h =>h)

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PolicyChoiceTiming`, which only this module used -/

section

/-! Record selection branches only on the public domain width and exact public encoding. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_zero)

structure ChoicePublic where
 B : Addr
 Z : Nat
 src : Addr
 recordPtr : Addr
 dom : List Byte
 g : Policy.Group
 k : Nat
 room : 256≤Z
 shape : dom.length=2*k ∨ dom.length=3*k
 positive : 0<k
 size : k<2^28

structure ChoiceReady (q : ChoicePublic) (s : State) : Prop where
 scratch : Scr s q.B q.Z
 base : s.gpr .x0=q.B
 source : Source q.src q.dom s
 record : PolicyRecordAt q.B q.recordPtr q.g s
 domain : word s.mem q.B (8*sDom)=q.src
 length : word s.mem q.B (8*sDL)=BitVec.ofNat 64 q.dom.length
 pointer : s.gpr .x4=off q.recordPtr 8
 test : s.gpr .x3=BitVec.ofNat 64 q.k-BitVec.ofNat 64 q.g.len

theorem choice_eval {q : ChoicePublic} {s : State} (h : ChoiceReady q s) :
 isa.eval (.zero .x .x3) s=some (decide (q.k=q.g.len)) := by
 rw [eval_zero,h.test]
 change some (BitVec.ofNat 64 q.k-BitVec.ofNat 64 q.g.len==0#64)=_
 rw [sub_zero_iff (by have :=q.size;omega_using [this]) (by have :=h.record.lenFit;omega_using [this])]

def choiceCompare (q : ChoicePublic) (same : q.k=q.g.len) : ComparePublic :=
 ⟨q.B,q.Z,q.src,off q.recordPtr 8,q.dom,q.g.domain.take q.dom.length,q.room,
  by rw [List.length_take,policyDomain_length];have :=q.shape;omega_using [same, this],
  by have :=q.shape;have :=q.positive;omega_arith,
  by have :=q.shape;have :=q.size;omega_arith⟩

theorem choice_compare_ready {q : ChoicePublic} {s : State} (h : ChoiceReady q s) (same : q.k=q.g.len) :
 PolicyCompareReady (choiceCompare q same) s :=
 ⟨h.scratch,h.base,h.domain,h.length,h.pointer,h.source,h.record.source.take q.dom.length⟩

theorem policyChoice_ct : RelCT isa (Two ChoiceReady) Policy.recordChoice (fun _ _ =>True) := by
 change RelCT isa (fun s t =>∃ q,ChoiceReady q s ∧ ChoiceReady q t ∧ s.sp=t.sp) _ _
 apply RelCT.exists_
 intro q
 unfold Policy.recordChoice
 refine RelCT.ite (fun s t h =>(choice_eval h.1).trans (choice_eval h.2.1).symm) ?_ (RelCT.block_nil (fun _ _ _ =>trivial))
 by_cases same : q.k=q.g.len
 · exact compareChoice_ct.mono (fun s t h =>⟨choiceCompare q same,
    choice_compare_ready h.1.1 same,choice_compare_ready h.1.2.1 same,h.1.2.2⟩) (fun _ _ h =>h)
 · apply RelCT.of_false
   rintro s t ⟨⟨hs,_,_⟩,condition⟩
   rw [choice_eval hs,decide_eq_false same] at condition
   contradiction

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! Each public record has public length, cap, exact comparison, and next-record address. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure RecordPublic where
 choice : ChoicePublic
 N : Nat
 fit : N<2^64

structure RecordReady (q : RecordPublic) (s : State) : Prop where
 scratch : Scr s q.choice.B q.choice.Z
 base : s.gpr .x0=q.choice.B
 source : Source q.choice.src q.choice.dom s
 record : PolicyRecordAt q.choice.B q.choice.recordPtr q.choice.g s
 domain : word s.mem q.choice.B (8*sDom)=q.choice.src
 length : word s.mem q.choice.B (8*sDL)=BitVec.ofNat 64 q.choice.dom.length
 keyLength : word s.mem q.choice.B (8*sLen)=BitVec.ofNat 64 q.choice.k
 width : word s.mem q.choice.B (8*sBits)=BitVec.ofNat 64 q.N
 pointer : s.gpr .x4=q.choice.recordPtr

structure RecordChoiceReady (q : RecordPublic) (s : State) : Prop extends ChoiceReady q.choice s where
 width : word s.mem q.choice.B (8*sBits)=BitVec.ofNat 64 q.N
 cap : s.gpr .x6=BitVec.ofNat 64 q.choice.g.bits

theorem policyRecord_ct : RelCT isa (Two RecordReady) Policy.record (fun _ _ =>True) := by
 unfold Policy.record
 refine RelCT.seq (two_piece (Ψ:=RecordChoiceReady) [.x0,.x4] (fun q s t hs ht r hr =>by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hs.base.trans ht.base.symm
  · exact hs.pointer.trans ht.pointer.symm) (by taint_decide) ?_) ?_
 · intro q s h
   refine WP.mono (policyRecordHead h.scratch q.choice.room h.base h.keyLength h.pointer h.record.readLen h.record.readBits
    h.record.length h.record.bits h.record.lenFit h.record.bitsFit) ?_
   rintro t ⟨⟨ptr,cap,test,mem⟩,rest⟩
   exact ⟨⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,h.source.of_mem mem rest,h.record.after_mem mem rest,
    mem ▸ h.domain,mem ▸ h.length,ptr,test⟩,mem ▸ h.width,cap⟩
 · refine RelCT.seq (two_post (Ψ:=fun q s =>s.gpr .x4=off q.choice.recordPtr 8)
    (two_map RecordPublic.choice (fun _ _ h =>h.toChoiceReady) policyChoice_ct) ?_)
    (two_taint [.x4] (fun q s t hs ht r hr =>by
     have eq : r= .x4 := by simpa using hr
     subst r;exact hs.trans ht.symm) (by taint_decide))
   intro q s h
   refine WP.mono (policyChoice_ok h.scratch q.choice.room h.base h.source h.record q.choice.shape q.choice.positive q.choice.size
    h.domain h.length h.width q.fit h.pointer h.cap h.test) ?_
   rintro t ⟨_,_,rest⟩
   exact (rest.gpr .x4 (by simp [choiceClobbers])).trans h.pointer

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Early policy-recognition exits are completely determined by public records and domain bytes. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyLoopTimingState.lean`, which only this module imported.
section

/-! Public remaining records determine each policy-loop exit and continuation. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure PolicyLoopPublic where
 choice : ChoicePublic
 tail : List Policy.Group
 N : Nat
 fit : N<2^64
 small : tail.length+1<2^64

def loopRecord (q : PolicyLoopPublic) : RecordPublic :=⟨q.choice,q.N,q.fit⟩

structure PolicyLoopReady (q : PolicyLoopPublic) (s : State) : Prop where
 record : RecordReady (loopRecord q) s
 records : PolicyTableAt q.choice.B q.choice.recordPtr (q.choice.g::q.tail) s
 count : s.gpr .x7=BitVec.ofNat 64 (q.tail.length+1)

abbrev recordMatches (q : PolicyLoopPublic) : Prop :=
 q.choice.k=q.choice.g.len ∧ q.choice.dom=q.choice.g.domain.take q.choice.dom.length

def RecordOutcome (q : PolicyLoopPublic) (s t : State) : Prop :=
 t.mem=(if recordMatches q then s.mem.writeW (off q.choice.B (8*sBits)) (BitVec.ofNat 64 (min q.N q.choice.g.bits)) else s.mem) ∧
 t.gpr .x7=BitVec.ofNat 64 (if recordMatches q then 0 else q.tail.length) ∧
 t.gpr .x4=off q.choice.recordPtr (8+3*q.choice.g.len) ∧ Keep recordClobbers s t

theorem policyLoop_record_ok {q : PolicyLoopPublic} {s : State} (h : PolicyLoopReady q s) :
 WP isa Policy.record s (RecordOutcome q s) := by
 have r:=h.record
 refine WP.mono (policyStep_ok r.scratch q.choice.room r.base r.source r.record q.choice.shape q.choice.positive q.choice.size
  r.domain r.length r.keyLength r.width q.fit r.pointer h.count (by omega_using [])) ?_
 rintro t ⟨mem,count,ptr,rest⟩
 have count' : t.gpr .x7=BitVec.ofNat 64 (if recordMatches q then 0 else q.tail.length) :=by
  simpa only [Nat.add_sub_cancel,loopRecord,recordMatches] using count

 exact ⟨mem,count',ptr,rest⟩

def policyNext (q : PolicyLoopPublic) (g : Policy.Group) (tail : List Policy.Group) (shorter : tail.length<q.tail.length) : PolicyLoopPublic :=
 ⟨{q.choice with recordPtr:=off q.choice.recordPtr (8+3*q.choice.g.len),g:=g},tail,q.N,q.fit,by have :=q.small;omega_using [shorter, this]⟩

theorem policyLoop_next {q : PolicyLoopPublic} {s t : State} {g : Policy.Group} {tail : List Policy.Group}
 (h : PolicyLoopReady q s) (outcome : RecordOutcome q s t) (miss : ¬recordMatches q) (tails : q.tail=g::tail) :
 PolicyLoopReady (policyNext q g tail (by rw [tails];simp)) t := by
 obtain ⟨mem,count,ptr,rest⟩:=outcome
 rw [ite_eq_right miss] at mem count
 have nextTable : PolicyTableAt q.choice.B (off q.choice.recordPtr (8+3*q.choice.g.len)) (g::tail) t :=by
  have table:=h.records.2
  rw [tails] at table
  exact table.after_mem mem rest
 refine ⟨⟨h.record.scratch.congr rest.wr,(rest.gpr .x0 (by simp [recordClobbers])).trans h.record.base,
  h.record.source.of_mem mem rest,nextTable.1,?_,?_,?_,?_,ptr⟩,nextTable,?_⟩
 · change word t.mem q.choice.B (8*sDom)=q.choice.src;rw [mem];exact h.record.domain
 · change word t.mem q.choice.B (8*sDL)=BitVec.ofNat 64 q.choice.dom.length;rw [mem];exact h.record.length
 · change word t.mem q.choice.B (8*sLen)=BitVec.ofNat 64 q.choice.k;rw [mem];exact h.record.keyLength
 · change word t.mem q.choice.B (8*sBits)=BitVec.ofNat 64 q.N;rw [mem];exact h.record.width
 · change t.gpr .x7=BitVec.ofNat 64 (tail.length+1)
   simpa only [tails,List.length_cons] using count

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)

def PolicyLoopPair (n : Nat) (s t : State) : Prop :=
 ∃ q : PolicyLoopPublic,q.tail.length+1=n ∧ PolicyLoopReady q s ∧ PolicyLoopReady q t ∧ s.sp=t.sp

theorem policyLoop_ct : RelCT isa (Two PolicyLoopReady)
 (.loop Policy.record (.nonzero .x .x7)) (fun _ _ =>True) := by
 have step (n : Nat) : RelCT isa (PolicyLoopPair n) Policy.record fun s t =>
  isa.eval (.nonzero .x .x7) s=isa.eval (.nonzero .x .x7) t ∧
  (isa.eval (.nonzero .x .x7) s=some false→True) ∧
  (isa.eval (.nonzero .x .x7) s=some true→∃ m<n,PolicyLoopPair m s t) := by
  intro s t ts tt u v hp es et
  obtain ⟨q,length,hs,ht,sp⟩:=hp
  have ct:RelCT isa (Two PolicyLoopReady) Policy.record (fun _ _ =>True) :=
   two_map loopRecord (fun _ _ h =>h.record) policyRecord_ct
  have trace :=(ct _ _ _ _ _ _ ⟨q,hs,ht,sp⟩ es et).1
  obtain ⟨_,u',eu,ou⟩:=policyLoop_record_ok hs
  obtain ⟨_,v',ev,ov⟩:=policyLoop_record_ok ht
  obtain ⟨_,rfl⟩:=Exec.det es eu
  obtain ⟨_,rfl⟩:=Exec.det et ev
  refine ⟨trace,?_,fun _ =>trivial,?_⟩
  · rw [eval_nonzero,eval_nonzero,ou.2.1,ov.2.1]
  · intro more
    by_cases hit : recordMatches q
    · rw [eval_nonzero,ou.2.1,ite_eq_left hit] at more
      contradiction
    · cases tails : q.tail with
      | nil =>
        rw [eval_nonzero,ou.2.1,ite_eq_right hit,tails] at more
        contradiction
      | cons g tail =>
        refine ⟨tail.length+1,by rw [←length,tails];simp,policyNext q g tail (by rw [tails];simp),rfl,
         policyLoop_next hs ou hit tails,policyLoop_next ht ov hit tails,?_⟩
        rw [(Exec.rdwr es).2.2,(Exec.rdwr et).2.2]
        exact sp
 intro s t ts tt u v ⟨q,hs,ht,sp⟩ es et
 exact (RelCT.loop PolicyLoopPair step (q.tail.length+1)) _ _ _ _ _ _ ⟨q,rfl,hs,ht,sp⟩ es et

end VG.Proof.Ffdh.AArch64.Cached
