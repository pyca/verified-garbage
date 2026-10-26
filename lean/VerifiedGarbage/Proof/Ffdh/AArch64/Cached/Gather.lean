module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Tactic.SplitIfs

/-! Five disjoint bit positions produce exactly the canonical comb digit. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64

def prefixValue (bs : List Byte) (N i d : Nat) : Nat → Nat
 | 0 => 0
 | j+1 => prefixValue bs N i d j + 2^j*bitValue bs N (i+j*d)

theorem prefixValue_lt (bs : List Byte) (N i d j : Nat) : prefixValue bs N i d j<2^j := by
 induction j with
 | zero => simp [prefixValue]
 | succ j ih =>
  have bit := bitValue_lt bs N (i+j*d)
  have product : 2^j*bitValue bs N (i+j*d)≤2^j := by
   simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^j) (show bitValue bs N (i+j*d)≤1 by omega)
  simp only [prefixValue,Nat.pow_succ]
  omega

private theorem combine : ∀ j<5, ∀ d<2^j, ∀ b<2,
 BitVec.ofNat 64 d ||| (BitVec.ofNat 64 b <<< j) = BitVec.ofNat 64 (d+2^j*b) := by
 decide +kernel

private theorem toothTail_ok (s : State) {j k d acc b : Nat} (hj : j<5)
 (ha : acc<2^j) (hb : b<2)
 (index : s.gpr .x9=BitVec.ofNat 64 k) (stride : s.gpr .x4=BitVec.ofNat 64 d)
 (digit : s.gpr .x16=BitVec.ofNat 64 acc) (bit : s.gpr .x11=BitVec.ofNat 64 b) :
 WP isa (.block ((if j=0 then [] else ([.lsl .x .x11 .x11 j] : List Instr)) ++
 ([.logic .orr .x .x16 .x16 .x11,.add .x .x9 .x9 .x4] : List Instr))) s fun t =>
 (t.gpr .x9=BitVec.ofNat 64 (k+d) ∧ t.gpr .x16=BitVec.ofNat 64 (acc+2^j*b) ∧ t.mem=s.mem) ∧
 Keep [.x9,.x11,.x16] s t := by
 refine WP.keep [.x9,.x11,.x16] ?_ (by split_ifs <;> rfl) (by split_ifs <;> rfl) (by split_ifs <;> rfl)
 by_cases zero : j=0
 · subst j
   simp only [ite_true,List.nil_append]
   brun [index,stride,digit,bit]
   constructor
   · exact (BitVec.ofNat_add _ _).symm
   · simpa only [BitVec.shiftLeft_zero] using combine 0 (by decide) acc ha b hb
 · simp only [ite_eq_right zero,List.cons_append,List.nil_append]
   brun [index,stride,digit,bit,show j<64 by omega]
   constructor
   · exact (BitVec.ofNat_add _ _).symm
   · exact combine j hj acc ha b hb

def gatherClobbers : List Reg := [.x8,.x9,.x10,.x11,.x16]

private structure GatherInv (s0 : State) (bs : List Byte) (N i d j : Nat) (s : State) : Prop where
 index : s.gpr .x9=BitVec.ofNat 64 (i+j*d)
 digit : s.gpr .x16=BitVec.ofNat 64 (prefixValue bs N i d j)
 mem : s.mem=s0.mem
 rest : Keep gatherClobbers s0 s

theorem tooth_ok (s : State) {src : Addr} {bs : List Byte} {N k d acc j : Nat}
 (source : Source src bs s) (size : bs.length<2^31) (widthBound : N≤8*bs.length)
 (hk : k<2^63) (hj : j<5) (ha : acc<2^j)
 (ptr : s.gpr .x1=src) (length : s.gpr .x2=BitVec.ofNat 64 bs.length)
 (index : s.gpr .x9=BitVec.ofNat 64 k) (width : s.gpr .x5=BitVec.ofNat 64 N)
 (stride : s.gpr .x4=BitVec.ofNat 64 d) (digit : s.gpr .x16=BitVec.ofNat 64 acc) :
 WP isa (VG.Impl.Ffdh.AArch64.Cached.Comb.tooth j) s fun t =>
 t.gpr .x9=BitVec.ofNat 64 (k+d) ∧ t.gpr .x16=BitVec.ofNat 64 (acc+2^j*bitValue bs N k) ∧
 t.mem=s.mem ∧ Keep gatherClobbers s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.tooth
 rw [WP.seq_iff]
 refine WP.mono (bit_ok s source size widthBound hk ptr length index width) ?_
 rintro u ⟨bit,memU,restU⟩
 refine WP.mono (toothTail_ok u hj ha (bitValue_lt bs N k)
  ((restU.gpr .x9 (by decide)).trans index) ((restU.gpr .x4 (by decide)).trans stride)
  ((restU.gpr .x16 (by decide)).trans digit) bit) ?_
 rintro t ⟨⟨index,digit,mem⟩,rest⟩
 exact ⟨index,digit,mem.trans memU,(restU.trans rest).mono (by decide)⟩


theorem gather_ok (s : State) {src : Addr} {bs : List Byte} {N i d : Nat}
 (source : Source src bs s) (size : bs.length<2^31) (widthBound : N≤8*bs.length)
 (positions : i+5*d<2^63)
 (ptr : s.gpr .x1=src) (length : s.gpr .x2=BitVec.ofNat 64 bs.length)
 (index : s.gpr .x9=BitVec.ofNat 64 i) (width : s.gpr .x5=BitVec.ofNat 64 N)
 (stride : s.gpr .x4=BitVec.ofNat 64 d) (digit : s.gpr .x16=0#64) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.gather s fun t =>
 t.gpr .x16=BitVec.ofNat 64 (prefixValue bs N i d 5) ∧ t.mem=s.mem ∧ Keep gatherClobbers s t := by
 have step (j : Nat) (hj : j<5) (t : State) (h : GatherInv s bs N i d j t) :
  WP isa (VG.Impl.Ffdh.AArch64.Cached.Comb.tooth j) t (GatherInv s bs N i d (j+1)) := by
  have bound := Nat.mul_le_mul_right d (show j≤5 by omega)
  refine WP.mono (tooth_ok t (source.of_mem h.mem h.rest) size widthBound (by omega) hj
   (prefixValue_lt bs N i d j)
   ((h.rest.gpr .x1 (by simp [gatherClobbers])).trans ptr)
   ((h.rest.gpr .x2 (by simp [gatherClobbers])).trans length)
   h.index ((h.rest.gpr .x5 (by simp [gatherClobbers])).trans width)
   ((h.rest.gpr .x4 (by simp [gatherClobbers])).trans stride) h.digit) ?_
  rintro u ⟨index,digit,mem,rest⟩
  refine ⟨?_,digit,mem.trans h.mem,(h.rest.trans rest).mono (by simp [gatherClobbers])⟩
  simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using index
 have init : GatherInv s bs N i d 0 s := by
  refine ⟨?_,?_,rfl,Keep.refl _ _⟩
  · simpa using index
  · exact digit
 change WP isa (.seq (VG.Impl.Ffdh.AArch64.Cached.Comb.tooth 0)
  (.seq (VG.Impl.Ffdh.AArch64.Cached.Comb.tooth 1)
   (.seq (VG.Impl.Ffdh.AArch64.Cached.Comb.tooth 2)
    (.seq (VG.Impl.Ffdh.AArch64.Cached.Comb.tooth 3) (VG.Impl.Ffdh.AArch64.Cached.Comb.tooth 4))))) s _
 rw [WP.seq_iff]
 refine WP.mono (step 0 (by decide) s init) ?_
 intro s1 h1
 rw [WP.seq_iff]
 refine WP.mono (step 1 (by decide) s1 h1) ?_
 intro s2 h2
 rw [WP.seq_iff]
 refine WP.mono (step 2 (by decide) s2 h2) ?_
 intro s3 h3
 rw [WP.seq_iff]
 refine WP.mono (step 3 (by decide) s3 h3) ?_
 intro s4 h4
 exact WP.mono (step 4 (by decide) s4 h4) fun _ h => ⟨h.digit,h.mem,h.rest⟩

theorem bitValue_eq_bit (bs : List Byte) (N k : Nat) (size : N≤8*bs.length)
 (bound : Spec.Rsa.os2ip bs<2^N) :
 bitValue bs N k=VG.Proof.Rsa.FixedBaseComb.bit (Spec.Rsa.os2ip bs) k := by
 unfold bitValue VG.Proof.Rsa.FixedBaseComb.bit
 by_cases inside : k<N
 · rw [ite_eq_left inside]
   rw [←List.getElem_eq_getD 0]
   exact (VG.Proof.Ffdh.CombBitBytes.os2ip_bit bs k (by omega)).symm
 · rw [ite_eq_right inside]
   have limit : Spec.Rsa.os2ip bs<2^k :=
    Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega))
   rw [Nat.div_eq_of_lt limit]

theorem prefixValue_eq_digit (bs : List Byte) (N i : Nat) (size : N≤8*bs.length)
 (bound : Spec.Rsa.os2ip bs<2^N) :
 prefixValue bs N i (Spec.Rsa.FixedBaseComb.rows N) 5=
 VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i := by
 simp only [prefixValue,bitValue_eq_bit bs N _ size bound,VG.Proof.Rsa.FixedBaseComb.digit,
  Nat.pow_zero,Nat.pow_one,show 2^2=4 from rfl,show 2^3=8 from rfl,show 2^4=16 from rfl,
  Nat.zero_mul,Nat.add_zero,Nat.one_mul,Nat.zero_add]

end VG.Proof.Ffdh.AArch64.Cached
