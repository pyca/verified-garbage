module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecordTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyTableFrame
import VerifiedGarbage.Proof.Framework.Omega

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
  r.domain r.length r.keyLength r.width q.fit r.pointer h.count (by omega)) ?_
 rintro t ⟨mem,count,ptr,rest⟩
 have count' : t.gpr .x7=BitVec.ofNat 64 (if recordMatches q then 0 else q.tail.length) :=by
  simpa only [Nat.add_sub_cancel,loopRecord,recordMatches] using count

 exact ⟨mem,count',ptr,rest⟩

def policyNext (q : PolicyLoopPublic) (g : Policy.Group) (tail : List Policy.Group) (shorter : tail.length<q.tail.length) : PolicyLoopPublic :=
 ⟨{q.choice with recordPtr:=off q.choice.recordPtr (8+3*q.choice.g.len),g:=g},tail,q.N,q.fit,by have :=q.small;omega⟩

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
