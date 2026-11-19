module

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PolicyRecordEnv
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Layout
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
import VerifiedGarbage.Proof.Bignum.AArch64.Row

/-! ### `Ffdh.AArch64.Cached.PolicyCompareArgs`, which this module and modules that import it used -/

section

/-! Bind the complete byte-comparison loop to the public domain header. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyCompareStep.lean`, which only this module imported.
section

/-! A public domain byte comparison, preserving an exact mismatch accumulator. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

private theorem read1_eq (m : Mem) (p : Addr) : m.read p 1=m p := by
 change (0#0 ++ m p : BitVec (0+8))=m p
 exact BitVec.zero_width_append _ _
private theorem byte_zext (b : Byte) : (b.setWidth 32).setWidth 64=BitVec.ofNat 64 b.toNat := by
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 have := b.isLt
 omega_using []

theorem byte_cast_eq (b c : Byte) : BitVec.ofNat 64 b.toNat=BitVec.ofNat 64 c.toNat ↔ b=c := by
 constructor
 · intro eq
   have := congrArg BitVec.toNat eq
   have := b.isLt
   have := c.isLt
   apply BitVec.eq_of_toNat_eq
   simp only [BitVec.toNat_ofNat] at *
   omega_using [this]
 · rintro rfl;rfl

theorem policyCompareStep {s : State} {src dst : Addr} {bs cs : List Byte} {i : Nat}
 (first : Source src bs s) (second : Source dst cs s) (inside : i<bs.length) (insideC : i<cs.length)
 (ptr1 : s.gpr .x1=off src i) (ptr2 : s.gpr .x2=off dst i) :
 WP isa (.block Policy.compareBody) s fun t =>
 (t.gpr .x1=off src (i+1) ∧ t.gpr .x2=off dst (i+1) ∧
 t.gpr .x11=s.gpr .x11 ||| (BitVec.ofNat 64 (bs.getD i 0).toNat ^^^ BitVec.ofNat 64 (cs.getD i 0).toNat) ∧
 t.mem=s.mem) ∧ Keep [.x1,.x2,.x8,.x9,.x11] s t := by
 refine WP.keep [.x1,.x2,.x8,.x9,.x11] ?_ rfl rfl rfl
 unfold Policy.compareBody
 brun [ptr1,ptr2,first.readable i inside,second.readable i insideC,
  first.bytes i inside,second.bytes i insideC,read1_eq,byte_zext]

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyCompare.lean`, which only this module imported.
section

/-! Every byte is compared; a zero accumulator means exact equality. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def compareClobbers : List Reg := [.x1,.x2,.x5,.x8,.x9,.x11]

structure CompareInv (s0 : State) (src dst : Addr) (bs cs : List Byte) (i : Nat) (s : State) : Prop where
 first : s.gpr .x1=off src i
 second : s.gpr .x2=off dst i
 equal : s.gpr .x11=0#64 ↔ ∀ j<i,bs.getD j 0=cs.getD j 0
 mem : s.mem=s0.mem
 keep : Keep compareClobbers s0 s

theorem policyCompareLoopStep {s0 t : State} {src dst : Addr} {bs cs : List Byte} {i : Nat}
 (first : Source src bs s0) (second : Source dst cs s0) (same : bs.length=cs.length)
 (inside : i<bs.length) (h : CompareInv s0 src dst bs cs i t) :
 WP isa (.block (Policy.compareBody++([.subImm .x .x5 .x5 1] : List Instr))) t fun u =>
 CompareInv s0 src dst bs cs (i+1) u ∧ u.gpr .x5=t.gpr .x5-1#64 := by
 rw [WP.block_append_iff]
 refine WP.mono (policyCompareStep (first.of_mem h.mem h.keep) (second.of_mem h.mem h.keep)
  inside (by omega_using [same, inside]) h.first h.second) ?_
 rintro v ⟨⟨ptr1,ptr2,value,mem⟩,rest⟩
 have equal : v.gpr .x11=0#64 ↔ ∀ j<i+1,bs.getD j 0=cs.getD j 0 := by
  rw [value,BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff,byte_cast_eq,h.equal]
  constructor
  · rintro ⟨prev,current⟩ j hj
    by_cases lt : j<i
    · exact prev j lt
    · have eq : j=i := by omega_using [hj, lt]
      simpa only [eq] using current
  · intro all
    exact ⟨fun j hj => all j (by omega_using [hj]),all i (by omega_using [])⟩
 refine WP.mono (dec_ok v .x5) ?_
 rintro u ⟨⟨count,memU,_⟩,restU⟩
 refine ⟨⟨(restU.gpr .x1 (by decide)).trans ptr1,(restU.gpr .x2 (by decide)).trans ptr2,?_,
  (memU.trans mem).trans h.mem,((h.keep.trans rest).trans restU).mono (by simp [compareClobbers])⟩,?_⟩
 · rw [restU.gpr .x11 (by decide)]
   exact equal
 · rw [count,rest.gpr .x5 (by decide)]

theorem policyCompareLoop_ok (s : State) {src dst : Addr} {bs cs : List Byte}
 (first : Source src bs s) (second : Source dst cs s) (same : bs.length=cs.length)
 (positive : 0<bs.length) (size : bs.length<2^31)
 (ptr1 : s.gpr .x1=src) (ptr2 : s.gpr .x2=dst) (count : s.gpr .x5=BitVec.ofNat 64 bs.length)
 (zero : s.gpr .x11=0#64) :
 WP isa (countLoop .x5 Policy.compareBody) s fun t =>
 (t.gpr .x11=0#64 ↔ bs=cs) ∧ t.mem=s.mem ∧ Keep compareClobbers s t := by
 have init : CompareInv s src dst bs cs 0 s :=
  ⟨by simpa [off] using ptr1,by simpa [off] using ptr2,by simp [zero],rfl,Keep.refl _ _⟩
 unfold countLoop
 refine WP.mono (wp_countdown (by omega_using [size]) positive (CompareInv s src dst bs cs)
  (fun i hi t h _ => policyCompareLoopStep first second same hi h) init count) ?_
 rintro t h
 refine ⟨?_,h.mem,h.keep⟩
 rw [h.equal]
 constructor
 · intro equal
   apply List.ext_getElem same
   intro i hi hj
   simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] using equal i hi
 · rintro rfl i hi
   rfl

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem policyCompare_ok {s : State} {B src dst : Addr} {Z : Nat} {bs cs : List Byte}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (pointer : word s.mem B (8*sDom)=src) (length : word s.mem B (8*sDL)=BitVec.ofNat 64 bs.length)
 (record : s.gpr .x4=dst) (first : Source src bs s) (second : Source dst cs s)
 (same : bs.length=cs.length) (positive : 0<bs.length) (size : bs.length<2^31) :
 WP isa Policy.compare s fun t => (t.gpr .x11=0#64 ↔ bs=cs) ∧
 t.mem=s.mem ∧ Keep compareClobbers s t := by
 unfold Policy.compare
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2,.x5,.x11] (Q:=fun u =>
  u.gpr .x1=src ∧ u.gpr .x2=dst ∧ u.gpr .x5=BitVec.ofNat 64 bs.length ∧ u.gpr .x11=0#64 ∧ u.mem=s.mem)
  ?_ rfl rfl rfl) ?_
 · brun [base,hdr_enc (show sDom<32 by decide),hdr_enc (show sDL<32 by decide),
   scratch.ld (d:=8*sDom) (by unfold sDom;omega_using [room]),scratch.ld (d:=8*sDL) (by unfold sDL;omega_using [room]),pointer,length,record]
 · rintro u ⟨⟨ptr1,ptr2,count,zero,mem⟩,rest⟩
   refine WP.mono (policyCompareLoop_ok u (first.of_mem mem rest) (second.of_mem mem rest)
    same positive size ptr1 ptr2 count zero) ?_
   rintro t ⟨equal,memT,restT⟩
   exact ⟨equal,memT.trans mem,(rest.trans restT).mono (by simp [compareClobbers])⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.PolicyChoice`, which this module and modules that import it used -/

section

/-! A cap is applied only after the complete vetted-domain match. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/PolicyMatch.lean`, which only this module imported.
section

/-! Exact matches cap the width by the reviewed policy, never increase it. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem publicCarry {a b : Nat} (fitA : a<2^64) (fitB : b<2^64) :
 decide (2^64≤(BitVec.ofNat 64 a).toNat+(~~~BitVec.ofNat 64 b).toNat+1)=decide (b≤a) := by
 simp only [BitVec.toNat_not,BitVec.toNat_ofNat]
 rw [Nat.mod_eq_of_lt fitA,Nat.mod_eq_of_lt fitB]
 apply decide_eq_decide.mpr
 omega_using [fitB]

theorem policyMatch_ok {s : State} {B : Addr} {Z N cap : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (width : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (fit : N<2^64)
 (limit : s.gpr .x6=BitVec.ofNat 64 cap) (capFit : cap<2^64) :
 WP isa (.block Policy.matched) s fun t =>
 (t.mem=s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N cap)) ∧ t.gpr .x7=1#64) ∧
 Keep [.x7,.x9,.x10] s t := by
 have choose : (if decide (cap≤N) then BitVec.ofNat 64 cap else BitVec.ofNat 64 N)=BitVec.ofNat 64 (min N cap) := by
  by_cases h : cap≤N
  · simp only [decide_eq_true h,ite_true,Nat.min_eq_right h]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,Nat.min_eq_left (show N≤cap by omega_using [h])]
 refine WP.keep [.x7,.x9,.x10] ?_ rfl rfl rfl
 unfold Policy.matched
 brun [base,hdr_enc (show sBits<32 by decide),scratch.ld (d:=8*sBits) (by unfold sBits;omega_using [room]),
  scratch.st (d:=8*sBits) (by unfold sBits;omega_using [room]),width,limit,Bool.toNat_true,publicCarry fit capFit,choose]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

def choiceClobbers : List Reg := [.x1,.x2,.x5,.x7,.x8,.x9,.x10,.x11]

theorem policyChoice_ok {s : State} {B src rec : Addr} {Z k N : Nat} {dom : List Byte} {g : Policy.Group}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (source : Source src dom s) (record : PolicyRecordAt B rec g s)
 (shape : dom.length=2*k ∨ dom.length=3*k) (positive : 0<k) (size : k<2^28)
 (domain : word s.mem B (8*sDom)=src) (length : word s.mem B (8*sDL)=BitVec.ofNat 64 dom.length)
 (width : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (fit : N<2^64)
 (pointer : s.gpr .x4=off rec 8) (cap : s.gpr .x6=BitVec.ofNat 64 g.bits)
 (test : s.gpr .x3=BitVec.ofNat 64 k-BitVec.ofNat 64 g.len) :
 WP isa Policy.recordChoice s fun t =>
 (t.mem=if k=g.len ∧ dom=g.domain.take dom.length then
  s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N g.bits)) else s.mem) ∧
 (t.gpr .x7=if k=g.len ∧ dom=g.domain.take dom.length then 1#64 else s.gpr .x7) ∧
 Keep choiceClobbers s t := by
 unfold Policy.recordChoice
 refine WP.ite (decide (k=g.len)) ?_ ?_ ?_
 · rw [eval_zero,test]
   change some (BitVec.ofNat 64 k-BitVec.ofNat 64 g.len == 0#64)=_
   rw [sub_zero_iff (by omega_using [size]) (by have := record.lenFit;omega_using [this])]
 · intro yes
   have same := of_decide_eq_true yes
   have limit : dom.length≤g.domain.length := by rw [policyDomain_length];omega_using [shape, same]
   rw [WP.seq_iff]
   refine WP.mono (policyCompare_ok scratch room base domain length pointer source
    (record.source.take dom.length) (by simp only [List.length_take];omega_using [limit]) (by omega_using [shape, positive]) (by omega_using [shape, size])) ?_
   rintro u ⟨equal,memU,restU⟩
   have choose : isa.eval (.zero .x .x11) u=some (decide (dom=g.domain.take dom.length)) := by
    rw [eval_zero]
    change some (u.gpr .x11 == 0#64)=_
    apply congrArg some
    apply Bool.eq_iff_iff.mpr
    simpa only [beq_iff_eq,decide_eq_true_eq] using equal
   refine WP.ite (decide (dom=g.domain.take dom.length)) choose ?_ ?_
   · intro yesDomain
     have sameDomain := of_decide_eq_true yesDomain
     have matched : k=g.len ∧ dom=g.domain.take dom.length := ⟨same,sameDomain⟩
     refine WP.mono (policyMatch_ok (scratch.congr restU.wr) room
      ((restU.gpr .x0 (by simp [compareClobbers])).trans base) (memU ▸ width) fit
      ((restU.gpr .x6 (by simp [compareClobbers])).trans cap) (by have := record.bitsFit;omega_using [this])) ?_
     rintro t ⟨⟨memT,countT⟩,restT⟩
     refine ⟨?_,?_,(restU.trans restT).mono (by simp [compareClobbers,choiceClobbers])⟩
     · simpa only [ite_eq_left matched,memU] using memT
     · simpa only [ite_eq_left matched] using countT
   · intro noDomain
     have different := of_decide_eq_false noDomain
     refine WP.block_nil ⟨?_,?_,restU.mono (by simp [compareClobbers,choiceClobbers])⟩
     · simpa only [same,different,and_false,ite_false] using memU
     · simpa only [same,different,and_false,ite_false] using restU.gpr .x7 (by simp [compareClobbers])
 · intro no
   have different := of_decide_eq_false no
   refine WP.block_nil ⟨?_,?_,(Keep.refl [] s).mono (by simp)⟩
   · simp only [different,false_and,ite_false]
   · simp only [different,false_and,ite_false]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! One record either caps the exponent and stops, or advances without changing memory. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def recordClobbers : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11]

theorem policyStep_ok {s : State} {B src rec : Addr} {Z k N n : Nat} {dom : List Byte} {g : Policy.Group}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B)
 (source : Source src dom s) (record : PolicyRecordAt B rec g s)
 (shape : dom.length=2*k ∨ dom.length=3*k) (positive : 0<k) (size : k<2^28)
 (domain : word s.mem B (8*sDom)=src) (length : word s.mem B (8*sDL)=BitVec.ofNat 64 dom.length)
 (keyLength : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (width : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (fit : N<2^64)
 (pointer : s.gpr .x4=rec) (count : s.gpr .x7=BitVec.ofNat 64 n) (countPositive : 0<n) :
 WP isa Policy.record s fun t =>
 (t.mem=if k=g.len ∧ dom=g.domain.take dom.length then
  s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N g.bits)) else s.mem) ∧
 (t.gpr .x7=BitVec.ofNat 64 (if k=g.len ∧ dom=g.domain.take dom.length then 0 else n-1)) ∧
 t.gpr .x4=off rec (8+3*g.len) ∧ Keep recordClobbers s t := by
 unfold Policy.record
 rw [WP.seq_iff]
 refine WP.mono (policyRecordHead scratch room base keyLength pointer record.readLen record.readBits
  record.length record.bits record.lenFit record.bitsFit) ?_
 rintro a ⟨⟨pointerA,capA,testA,memA⟩,restA⟩
 rw [WP.seq_iff]
 refine WP.mono (policyChoice_ok (scratch.congr restA.wr) room
  ((restA.gpr .x0 (by decide)).trans base) (source.of_mem memA restA)
  (record.after_mem memA restA) shape positive size (memA ▸ domain) (memA ▸ length)
  (memA ▸ width) fit pointerA capA testA) ?_
 rintro b ⟨memB,countB,restB⟩
 let matched := k=g.len ∧ dom=g.domain.take dom.length
 have mem : b.mem=if matched then
  s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N g.bits)) else s.mem := by rw [memB,memA]
 have lengthB : b.mem.readW rec 32=BitVec.ofNat 32 g.len := by
  rw [mem]
  split_ifs
  · have frame : Outside B (8*sBits) 8 s.mem
      (s.mem.writeW (off B (8*sBits)) (BitVec.ofNat 64 (min N g.bits))) := writeW_outside _ _ _ (by decide)
    exact (Mem.readW_congr fun i hi => frame _ (Or.inr (record.separate i hi))).trans record.length
  · exact record.length
 have countValue : b.gpr .x7=BitVec.ofNat 64 (if matched then 1 else n) := by
  rw [countB,restA.gpr .x7 (by decide),count]
  split_ifs <;> rfl
 have countPos : 0<(if matched then 1 else n) := by split_ifs <;> omega_arith
 have rest := restA.trans restB
 refine WP.mono (policyRecordTail ((restB.gpr .x4 (by simp [choiceClobbers])).trans pointerA)
  countValue (by rw [rest.rd,rest.wr];exact record.readLen) lengthB record.lenFit countPos) ?_
 rintro t ⟨⟨pointerT,countT,memT⟩,restT⟩
 refine ⟨memT.trans mem,?_,pointerT,(rest.trans restT).mono (by simp [choiceClobbers,recordClobbers])⟩
 rw [countT]
 change BitVec.ofNat 64 ((if matched then 1 else n)-1)=BitVec.ofNat 64 (if matched then 0 else n-1)
 split_ifs <;> rfl

end VG.Proof.Ffdh.AArch64.Cached
