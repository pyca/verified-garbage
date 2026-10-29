module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Policy
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Row
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
 omega

theorem byte_cast_eq (b c : Byte) : BitVec.ofNat 64 b.toNat=BitVec.ofNat 64 c.toNat ↔ b=c := by
 constructor
 · intro eq
   have := congrArg BitVec.toNat eq
   have := b.isLt
   have := c.isLt
   apply BitVec.eq_of_toNat_eq
   simp only [BitVec.toNat_ofNat] at *
   omega
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
  inside (by omega) h.first h.second) ?_
 rintro v ⟨⟨ptr1,ptr2,value,mem⟩,rest⟩
 have equal : v.gpr .x11=0#64 ↔ ∀ j<i+1,bs.getD j 0=cs.getD j 0 := by
  rw [value,BitVec.or_eq_zero_iff,BitVec.xor_eq_zero_iff,byte_cast_eq,h.equal]
  constructor
  · rintro ⟨prev,current⟩ j hj
    by_cases lt : j<i
    · exact prev j lt
    · have eq : j=i := by omega
      simpa only [eq] using current
  · intro all
    exact ⟨fun j hj => all j (by omega),all i (by omega)⟩
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
 refine WP.mono (wp_countdown (by omega) positive (CompareInv s src dst bs cs)
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
   scratch.ld (d:=8*sDom) (by unfold sDom;omega),scratch.ld (d:=8*sDL) (by unfold sDL;omega),pointer,length,record]
 · rintro u ⟨⟨ptr1,ptr2,count,zero,mem⟩,rest⟩
   refine WP.mono (policyCompareLoop_ok u (first.of_mem mem rest) (second.of_mem mem rest)
    same positive size ptr1 ptr2 count zero) ?_
   rintro t ⟨equal,memT,restT⟩
   exact ⟨equal,memT.trans mem,(rest.trans restT).mono (by simp [compareClobbers])⟩

end VG.Proof.Ffdh.AArch64.Cached
