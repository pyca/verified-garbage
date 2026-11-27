module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Frame
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Const
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
public import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Row
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Bit
public import VerifiedGarbage.Proof.Rsa.FixedBaseComb

/-! ### `Ffdh.AArch64.Cached.Gather`, which this module and modules that import it used -/

section

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
   simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2^j) (show bitValue bs N (i+j*d)≤1 by omega_using [bit])
  simp only [prefixValue,Nat.pow_succ]
  omega_using [ih, product]

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
   brun [index,stride,digit,bit,show j<64 by omega_using [hj]]
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
  have bound := Nat.mul_le_mul_right d (show j≤5 by omega_using [hj])
  refine WP.mono (tooth_ok t (source.of_mem h.mem h.rest) size widthBound (by omega_using [positions, bound]) hj
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
   exact (VG.Proof.Ffdh.CombBitBytes.os2ip_bit bs k (by omega_using [size, inside])).symm
 · rw [ite_eq_right inside]
   have limit : Spec.Rsa.os2ip bs<2^k :=
    Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by omega_using [inside]))
   rw [Nat.div_eq_of_lt limit]

theorem prefixValue_eq_digit (bs : List Byte) (N i : Nat) (size : N≤8*bs.length)
 (bound : Spec.Rsa.os2ip bs<2^N) :
 prefixValue bs N i (Spec.Rsa.FixedBaseComb.rows N) 5=
 VG.Proof.Rsa.FixedBaseComb.digit N (Spec.Rsa.os2ip bs) i := by
 simp only [prefixValue,bitValue_eq_bit bs N _ size bound,VG.Proof.Rsa.FixedBaseComb.digit,
  Nat.pow_zero,Nat.pow_one,show 2^2=4 from rfl,show 2^3=8 from rfl,show 2^4=16 from rfl,
  Nat.zero_mul,Nat.add_zero,Nat.one_mul,Nat.zero_add]

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.SelectScan`, which this module and modules that import it used -/

section

/-! ### `Ffdh.AArch64.Cached.SelectEnv`, which only this module used -/

section

/-! Read-only packed table geometry and the two public header cells used by the scan. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SelectWord.lean`, which only this module imported.
section

/-! Each masked table word reads both operands, stores only the destination,
and advances both pointers by eight. The mask is never used as an address. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64

theorem selectWord_ok (s : State) {src dst : Addr} {mask : BitVec 64}
 (source : s.gpr .x9=src) (output : s.gpr .x8=dst) (choose : s.gpr .x6=mask)
 (readSource : InRegions (s.rd++s.wr) src 8) (readOutput : InRegions (s.rd++s.wr) dst 8)
 (writeOutput : InRegions s.wr dst 8) :
 WP isa (.block VG.Impl.Ffdh.AArch64.Cached.Comb.selectWord) s fun t =>
 (t.mem=s.mem.writeW dst (s.mem.readW dst 64 ||| (s.mem.readW src 64 &&& mask)) ∧
 t.gpr .x9=src+8#64 ∧ t.gpr .x8=dst+8#64) ∧ Keep [.x3,.x4,.x8,.x9] s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.selectWord
 refine WP.keep [.x3,.x4,.x8,.x9] ?_ rfl rfl rfl
 brun [source,output,choose,readSource,readOutput,writeOutput]

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SelectRow.lean`, which only this module imported.
section

/-! A complete masked read-only table row. The only changed memory is the output row. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure SelectRowInv (s0 : State) (src dst : Addr) (mask : BitVec 64) (j : Nat) (s : State) : Prop where
 keep : Keep [.x3,.x4,.x8,.x9,.x12] s0 s
 source : s.gpr .x9=off src (8*j)
 output : s.gpr .x8=off dst (8*j)
 done : ∀ i<j, word s.mem dst (8*i)=word s0.mem dst (8*i) ||| (word s0.mem src (8*i) &&& mask)
 frame : Outside dst 0 (8*j) s0.mem s.mem

theorem selectRowStep_ok {s0 t : State} {src dst : Addr} {mask : BitVec 64} {w j : Nat}
 (fit : 8*w≤2^64) (hj : j<w)
 (readSource : ∀ i<w, InRegions (s0.rd++s0.wr) (off src (8*i)) 8)
 (readOutput : ∀ i<w, InRegions (s0.rd++s0.wr) (off dst (8*i)) 8)
 (writeOutput : ∀ i<w, InRegions s0.wr (off dst (8*i)) 8)
 (separate : ∀ i<w, ∀ b<8, 8*w≤ofs dst (off src (8*i)+BitVec.ofNat 64 b))
 (choose : s0.gpr .x6=mask) (h : SelectRowInv s0 src dst mask j t) :
 WP isa (.block (VG.Impl.Ffdh.AArch64.Cached.Comb.selectWord ++ ([.subImm .x .x12 .x12 1] : List Instr))) t fun u =>
 SelectRowInv s0 src dst mask (j+1) u ∧ u.gpr .x12=t.gpr .x12-1#64 := by
 rw [WP.block_append_iff]
 refine WP.mono (selectWord_ok t h.source h.output ((h.keep.gpr .x6 (by decide)).trans choose)
  (by rw [h.keep.rd,h.keep.wr];exact readSource j hj)
  (by rw [h.keep.rd,h.keep.wr];exact readOutput j hj)
  (by rw [h.keep.wr];exact writeOutput j hj)) ?_
 rintro v ⟨⟨memV,srcV,dstV⟩,restV⟩
 have srcWord : word t.mem src (8*j)=word s0.mem src (8*j) := by
  exact Mem.readW_congr fun b hb => h.frame (off src (8*j)+BitVec.ofNat 64 b)
   (Or.inr (by have := separate j hj b hb;omega_using [hj, this]))
 have dstWord : word t.mem dst (8*j)=word s0.mem dst (8*j) :=
  h.frame.word (Or.inr (by omega_using [])) (by omega_using [fit, hj])
 have mem : v.mem=t.mem.writeW (off dst (8*j))
  (word s0.mem dst (8*j) ||| (word s0.mem src (8*j) &&& mask)) := by
  change v.mem=t.mem.writeW (off dst (8*j))
   (word t.mem dst (8*j) ||| (word t.mem src (8*j) &&& mask)) at memV
  rw [srcWord,dstWord] at memV
  exact memV
 refine WP.mono (dec_ok v .x12) ?_
 rintro u ⟨⟨countU,memU,_⟩,restU⟩
 refine ⟨⟨((h.keep.trans restV).trans restU).mono (by decide),?_,?_,?_,?_⟩,?_⟩
 · rw [restU.gpr .x9 (by decide),srcV,show (8#64:Addr)=BitVec.ofNat 64 8 from rfl,
    off_add]
   congr 1
 · rw [restU.gpr .x8 (by decide),dstV,show (8#64:Addr)=BitVec.ofNat 64 8 from rfl,
    off_add]
   congr 1
 · intro i hi
   rw [memU,mem]
   rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
   · rw [(writeW_outside t.mem dst _ (by omega_using [fit, hj])).word (by omega_using [hi]) (by omega_arith)]
     exact h.done i hi
   · exact word_writeW_self _ _ _ _
 · rw [memU,mem]
   intro x hx
   rw [writeW_outside t.mem dst _ (by omega_using [fit, hj]) x (by omega_using [hx])]
   exact h.frame x (by omega_using [hx])
 · rw [countU,restV.gpr .x12 (by decide)]


theorem selectRow_ok (s : State) {src dst : Addr} {mask : BitVec 64} {w : Nat}
 (positive : 0<w) (fit : 8*w≤2^64)
 (source : s.gpr .x9=src) (output : s.gpr .x8=dst) (choose : s.gpr .x6=mask)
 (count : s.gpr .x12=BitVec.ofNat 64 w)
 (readSource : ∀ i<w, InRegions (s.rd++s.wr) (off src (8*i)) 8)
 (readOutput : ∀ i<w, InRegions (s.rd++s.wr) (off dst (8*i)) 8)
 (writeOutput : ∀ i<w, InRegions s.wr (off dst (8*i)) 8)
 (separate : ∀ i<w, ∀ b<8, 8*w≤ofs dst (off src (8*i)+BitVec.ofNat 64 b)) :
 WP isa (countLoop .x12 VG.Impl.Ffdh.AArch64.Cached.Comb.selectWord) s fun t =>
 (∀ i<w, word t.mem dst (8*i)=word s.mem dst (8*i) ||| (word s.mem src (8*i) &&& mask)) ∧
 Outside dst 0 (8*w) s.mem t.mem ∧ t.gpr .x9=off src (8*w) ∧
 t.gpr .x8=off dst (8*w) ∧ Keep [.x3,.x4,.x8,.x9,.x12] s t := by
 have init : SelectRowInv s src dst mask 0 s :=
  ⟨Keep.refl _ _,by simpa [off] using source,by simpa [off] using output,
   fun i hi => by omega,Outside.refl _ _ _ _⟩
 unfold countLoop
 exact WP.mono (wp_countdown (by omega_using [fit]) positive (SelectRowInv s src dst mask)
  (fun j hj t h _ => selectRowStep_ok fit hj readSource readOutput writeOutput separate choose h)
  init count) fun _ h => ⟨h.done,h.frame,h.source,h.output,h.keep⟩

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure SelectEnv (B table dst : Addr) (w : Nat) (s : State) : Prop where
 base : s.gpr .x0=B
 destination : word s.mem B (8*sArr 5)=dst
 width : word s.mem B (8*sW)=BitVec.ofNat 64 w
 readDestinationHeader : InRegions (s.rd++s.wr) (off B (8*sArr 5)) 8
 readWidthHeader : InRegions (s.rd++s.wr) (off B (8*sW)) 8
 readSource : ∀ j<32, ∀ i<w, InRegions (s.rd++s.wr) (off table (8*w*j+8*i)) 8
 readOutput : ∀ i<w, InRegions (s.rd++s.wr) (off dst (8*i)) 8
 writeOutput : ∀ i<w, InRegions s.wr (off dst (8*i)) 8
 separate : ∀ j<32, ∀ i<w, ∀ b<8, 8*w≤ofs dst (off table (8*w*j+8*i)+BitVec.ofNat 64 b)
 separateDestinationHeader : ∀ b<8, 8*w≤ofs dst (off B (8*sArr 5)+BitVec.ofNat 64 b)
 separateWidthHeader : ∀ b<8, 8*w≤ofs dst (off B (8*sW)+BitVec.ofNat 64 b)

theorem SelectEnv.after_frame {B table dst : Addr} {w : Nat} {s t : State} {rs : List Reg}
 (h : SelectEnv B table dst w s) (frame : Outside dst 0 (8*w) s.mem t.mem)
 (rest : Keep rs s t) (base : t.gpr .x0=B) : SelectEnv B table dst w t := by
 refine ⟨base,?_,?_,?_,?_,?_,?_,?_,h.separate,h.separateDestinationHeader,h.separateWidthHeader⟩
 · have same : word t.mem B (8*sArr 5)=word s.mem B (8*sArr 5) :=
    Mem.readW_congr fun b hb => frame (off B (8*sArr 5)+BitVec.ofNat 64 b)
     (Or.inr (by simpa only [Nat.zero_add] using h.separateDestinationHeader b hb))
   exact same.trans h.destination
 · have same : word t.mem B (8*sW)=word s.mem B (8*sW) :=
    Mem.readW_congr fun b hb => frame (off B (8*sW)+BitVec.ofNat 64 b)
     (Or.inr (by simpa only [Nat.zero_add] using h.separateWidthHeader b hb))
   exact same.trans h.width
 · rw [rest.rd,rest.wr];exact h.readDestinationHeader
 · rw [rest.rd,rest.wr];exact h.readWidthHeader
 · intro j hj i hi;rw [rest.rd,rest.wr];exact h.readSource j hj i hi
 · intro i hi;rw [rest.rd,rest.wr];exact h.readOutput i hi
 · intro i hi;rw [rest.wr];exact h.writeOutput i hi

theorem SelectEnv.source_word {B table dst : Addr} {w : Nat} {s t : State}
 (h : SelectEnv B table dst w s) (frame : Outside dst 0 (8*w) s.mem t.mem) {j i : Nat}
 (hj : j<32) (hi : i<w) : word t.mem table (8*w*j+8*i)=word s.mem table (8*w*j+8*i) :=
 Mem.readW_congr fun b hb => frame _ (Or.inr (by simpa only [Nat.zero_add] using h.separate j hj i hi b hb))

private theorem exec_cselc_x (s : State) (d n m : Reg) (cond : CondCode) :
 exec (.cselc .x d n m cond) s =
 some (s.write .x d (if cond.holds s then s.gpr n else s.gpr m)) := rfl

private theorem zeroFlag (s : State) (d : Reg) (a b : BitVec 64) (c : Bool) :
 (s.addWithCarry .x d a b c).zf=decide (a+b+BitVec.ofNat 64 c.toNat=0#64) := rfl

private theorem matching_mask : ∀ v<32, ∀ j<32,
 (if decide ((BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 j) + ~~~0#64 + 1#64 = 0#64) then 0#64-1#64 else 0#64) =
 (if v=j then BitVec.allOnes 64 else 0#64) := by
 decide +kernel

theorem selectHead_ok {s : State} {B table dst : Addr} {w v j : Nat}
 (env : SelectEnv B table dst w s) (hv : v<32) (hj : j<32)
 (digit : s.gpr .x10=BitVec.ofNat 64 v) (candidate : s.gpr .x11=BitVec.ofNat 64 j) :
 WP isa (.block VG.Impl.Ffdh.AArch64.Cached.Comb.selectHead) s fun t =>
 (t.gpr .x8=dst ∧ t.gpr .x12=BitVec.ofNat 64 w ∧
 t.gpr .x6=(if v=j then BitVec.allOnes 64 else 0#64) ∧ t.mem=s.mem) ∧
 Keep [.x3,.x6,.x7,.x8,.x12] s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.selectHead
 refine WP.keep [.x3,.x6,.x7,.x8,.x12] ?_ rfl rfl rfl
 brun [env.base,hdr_enc (show sArr 5<32 by decide),hdr_enc (show sW<32 by decide),
 env.readDestinationHeader,env.readWidthHeader,env.destination,env.width,digit,candidate,exec_cselc_x,CondCode.holds,RegUpd.zf_write,zeroFlag,Bool.toNat_true]
 exact matching_mask v hv j hj

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! Exactly 32 masked rows select the canonical entry without a secret address. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SelectStep.lean`, which only this module imported.
section

/-! One of exactly 32 table rows, preserving the context and public cursor. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem off_off (B : Addr) (a b : Nat) : off (off B a) b=off B (a+b) := by
 simp only [off,BitVec.add_assoc,BitVec.ofNat_add]

private theorem next_ok (s : State) {j : Nat} (candidate : s.gpr .x11=BitVec.ofNat 64 j) :
 WP isa (.block [.addImm .x .x11 .x11 1,.subImm .x .x3 .x11 32]) s fun t =>
 (t.gpr .x11=BitVec.ofNat 64 (j+1) ∧ t.gpr .x3=BitVec.ofNat 64 (j+1)-32#64 ∧ t.mem=s.mem) ∧
 Keep [.x3,.x11] s t := by
 refine WP.keep [.x3,.x11] ?_ rfl rfl rfl
 brun [candidate,←BitVec.ofNat_add]

def selectClobbers : List Reg := [.x3,.x4,.x6,.x7,.x8,.x9,.x11,.x12]

theorem selectStep_ok {s : State} {B table dst : Addr} {w v j : Nat}
 (env : SelectEnv B table dst w s) (positive : 0<w) (fit : 8*w≤2^64)
 (hv : v<32) (hj : j<32)
 (digit : s.gpr .x10=BitVec.ofNat 64 v) (candidate : s.gpr .x11=BitVec.ofNat 64 j)
 (pointer : s.gpr .x9=off table (8*w*j)) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.selectStep s fun t =>
 SelectEnv B table dst w t ∧
 (∀ i<w, word t.mem dst (8*i)=word s.mem dst (8*i) |||
  (word s.mem table (8*w*j+8*i) &&& (if v=j then BitVec.allOnes 64 else 0#64))) ∧
 Outside dst 0 (8*w) s.mem t.mem ∧
 t.gpr .x9=off table (8*w*(j+1)) ∧ t.gpr .x10=BitVec.ofNat 64 v ∧
 t.gpr .x11=BitVec.ofNat 64 (j+1) ∧ t.gpr .x3=BitVec.ofNat 64 (j+1)-32#64 ∧
 Keep selectClobbers s t := by
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.selectStep
 rw [WP.seq_iff]
 refine WP.mono (selectHead_ok env hv hj digit candidate) ?_
 rintro u ⟨⟨dstU,countU,maskU,memU⟩,restU⟩
 rw [WP.seq_iff]
 refine WP.mono (selectRow_ok u positive fit ((restU.gpr .x9 (by decide)).trans pointer)
  dstU maskU countU ?_ ?_ ?_ ?_) ?_
 · intro i hi
   rw [off_off,restU.rd,restU.wr]
   exact env.readSource j hj i hi
 · intro i hi;rw [restU.rd,restU.wr];exact env.readOutput i hi
 · intro i hi;rw [restU.wr];exact env.writeOutput i hi
 · intro i hi b hb
   rw [off_off]
   exact env.separate j hj i hi b hb
 · rintro z ⟨words,frame,srcZ,_,restZ⟩
   refine WP.mono (next_ok z ((restZ.gpr .x11 (by decide)).trans
    ((restU.gpr .x11 (by decide)).trans candidate))) ?_
   rintro t ⟨⟨next,counter,memT⟩,restT⟩
   have keep : Keep selectClobbers s t := ((restU.trans restZ).trans restT).mono (by decide)
   have totalFrame : Outside dst 0 (8*w) s.mem t.mem := by rw [memT,←memU];exact frame
   refine ⟨env.after_frame totalFrame keep ((keep.gpr .x0 (by simp [selectClobbers])).trans env.base),
    ?_,totalFrame,?_,(keep.gpr .x10 (by simp [selectClobbers])).trans digit,next,counter,keep⟩
   · intro i hi
     rw [memT,words i hi,memU]
     simp only [word,off_off]
   · rw [restT.gpr .x9 (by decide),srcZ,off_off]
     congr 1

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero)
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure SelectScanInv (s0 : State) (B table dst : Addr) (w v j : Nat) (s : State) : Prop where
 env : SelectEnv B table dst w s
 pointer : s.gpr .x9=off table (8*w*j)
 digit : s.gpr .x10=BitVec.ofNat 64 v
 candidate : s.gpr .x11=BitVec.ofNat 64 j
 words : ∀ i<w, word s.mem dst (8*i)=if v<j then word s0.mem table (8*w*v+8*i) else 0#64
 frame : Outside dst 0 (8*w) s0.mem s.mem
 keep : Keep selectClobbers s0 s

private theorem counterFlag : ∀ j<32,
 (BitVec.ofNat 64 (j+1)-32#64 != 0#64) = decide (j+1<32) := by
 decide +kernel

theorem selectScanStep_ok {s0 t : State} {B table dst : Addr} {w v j : Nat}
 (env : SelectEnv B table dst w s0) (positive : 0<w) (fit : 8*w≤2^64)
 (hv : v<32) (hj : j<32) (h : SelectScanInv s0 B table dst w v j t) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.selectStep t fun u =>
 SelectScanInv s0 B table dst w v (j+1) u ∧
 isa.eval (.nonzero .x .x3) u=some (decide (j+1<32)) := by
 refine WP.mono (selectStep_ok h.env positive fit hv hj h.digit h.candidate h.pointer) ?_
 rintro u ⟨envU,wordsU,frameU,pointerU,digitU,candidateU,counterU,keepU⟩
 refine ⟨⟨envU,pointerU,digitU,candidateU,?_,h.frame.trans frameU,(h.keep.trans keepU).mono (by simp [selectClobbers])⟩,?_⟩
 · intro i hi
   rw [wordsU i hi,h.words i hi]
   by_cases eq : v=j
   · subst j
     rw [env.source_word h.frame hv hi]
     simp only [Nat.lt_irrefl,ite_false,ite_true,BitVec.and_allOnes,BitVec.zero_or,Nat.lt_succ_self]
   · have same : v<j+1 ↔ v<j := by omega_using [eq]
     simp only [eq,ite_false,BitVec.and_zero,BitVec.or_zero,same]
 · rw [eval_nonzero,counterU]
   change some (BitVec.ofNat 64 (j+1)-32#64 != 0#64)=some (decide (j+1<32))
   rw [counterFlag j hj]

theorem selectScan_ok (s : State) {B table dst : Addr} {w v : Nat}
 (env : SelectEnv B table dst w s) (positive : 0<w) (fit : 8*w≤2^64) (hv : v<32)
 (pointer : s.gpr .x9=table) (digit : s.gpr .x10=BitVec.ofNat 64 v) (candidate : s.gpr .x11=0#64)
 (zeros : ∀ i<w, word s.mem dst (8*i)=0#64) :
 WP isa (.loop VG.Impl.Ffdh.AArch64.Cached.Comb.selectStep (.nonzero .x .x3)) s fun t =>
 SelectEnv B table dst w t ∧
 (∀ i<w, word t.mem dst (8*i)=word s.mem table (8*w*v+8*i)) ∧
 Outside dst 0 (8*w) s.mem t.mem ∧ Keep selectClobbers s t := by
 let I := fun remaining t => ∃ j, remaining=32-j ∧ j<32 ∧ SelectScanInv s B table dst w v j t
 refine WP.loop (M:=isa) I ?_ 32 s ?_
 · intro remaining t h
   obtain ⟨j,rem,hj,inv⟩ := h
   refine WP.mono (selectScanStep_ok env positive fit hv hj inv) ?_
   rintro u ⟨next,condition⟩
   by_cases more : j+1<32
   · right
     refine ⟨?_,32-(j+1),by omega_using [rem, hj],j+1,rfl,more,next⟩
     rw [condition,decide_eq_true more]
   · have last : j+1=32 := by omega_using [hj, more]
     left
     refine ⟨?_,next.env,?_,next.frame,next.keep⟩
     · rw [condition,decide_eq_false more]
     · intro i hi
       simpa only [last,ite_eq_left hv] using next.words i hi
 · refine ⟨0,rfl,by decide,env,?_,digit,candidate,?_,Outside.refl _ _ _ _,Keep.refl _ _⟩
   · simpa [off] using pointer
   · intro i hi
     simpa only [Nat.not_lt_zero,ite_false] using zeros i hi

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.Controls`, which this module and modules that import it used -/

section

/-! Public comb controls remain fixed while arrays, the row counter and the digit change. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure Controls (B src ctx : Addr) (k N : Nat) (s : State) : Prop where
 context : word s.mem B (8*sCtx)=ctx
 source : word s.mem B (8*sX)=src
 length : word s.mem B (8*sLen)=BitVec.ofNat 64 k
 bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N
 rows : word s.mem B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows N)

def Counter (B : Addr) (i : Nat) (s : State) : Prop := word s.mem B (8*sI)=BitVec.ofNat 64 i

def TablePointer (B table : Addr) (s : State) : Prop := word s.mem B (8*sTab)=table

theorem arrays_header {B : Addr} {w i : Nat} {m m' : Mem} {js : List Nat}
 (frame : Arrays B w js m m') (hi : i<32) : word m' B (8*i)=word m B (8*i) :=
 frame.word_eq (fun j _ => Or.inl (hdr_lt_slot w j hi)) (by omega_using [hi])

theorem Controls.after_arrays {B src ctx : Addr} {k N w : Nat} {s t : State} {js : List Nat}
 (h : Controls B src ctx k N s) (frame : Arrays B w js s.mem t.mem) : Controls B src ctx k N t := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact (arrays_header frame (by decide)).trans h.context
 · exact (arrays_header frame (by decide)).trans h.source
 · exact (arrays_header frame (by decide)).trans h.length
 · exact (arrays_header frame (by decide)).trans h.bits
 · exact (arrays_header frame (by decide)).trans h.rows

theorem Controls.after_counter {B src ctx : Addr} {k N : Nat} {s t : State}
 (h : Controls B src ctx k N s) (frame : Outside B (8*sI) 8 s.mem t.mem) : Controls B src ctx k N t := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.context
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.source
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.length
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.bits
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.rows

theorem Controls.after_digit {B src ctx : Addr} {k N : Nat} {s t : State}
 (h : Controls B src ctx k N s) (frame : Outside B (8*sD) 8 s.mem t.mem) : Controls B src ctx k N t := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.context
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.source
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.length
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.bits
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.rows


theorem Controls.after_table {B src ctx : Addr} {k N : Nat} {s t : State}
 (h : Controls B src ctx k N s) (frame : Outside B (8*sTab) 8 s.mem t.mem) : Controls B src ctx k N t := by
 refine ⟨?_,?_,?_,?_,?_⟩
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.context
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.source
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.length
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.bits
 · exact (header_other frame (by decide) (by decide) (by decide)).trans h.rows

end VG.Proof.Ffdh.AArch64.Cached

end

end

/-! ### `Ffdh.AArch64.Cached.Select`, which only this module used -/

section

/-! ### `Ffdh.AArch64.Cached.SelectLayout`, which only this module used -/

section

/-! The packed immutable context lies outside the existing Montgomery workspace. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem selectEnv_good {s : State} {B table : Addr} {Z w : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w)
 (readSource : ∀ j<32, ∀ i<w, InRegions (s.rd++s.wr) (off table (8*w*j+8*i)) 8)
 (sourceOutside : ∀ j<32, ∀ i<w, ∀ b<8, Z≤ofs B (off table (8*w*j+8*i)+BitVec.ofNat 64 b)) :
 SelectEnv B table (off B (slot w 5)) w s := by
 have arrayRoom : slot w 5+8*(w+2)≤Z := Nat.le_trans (slot_le (by decide : 5<8)) room
 have size : Z≤2^64 := by have := good.scr.nowrap;omega
 have hd : slot w 5<2^64 := by omega
 have fit : slot w 5+8*w≤2^64 := by omega
 refine ⟨good.x0,good.hdr.harr 5 (by decide),good.hdr.hw,?_,?_,readSource,?_,?_,?_,?_,?_⟩
 · exact good.scr.ld (by have := hdr_lt_slot w 8 (show sArr 5<32 by decide);omega)
 · exact good.scr.ld (by have := hdr_lt_slot w 8 (show sW<32 by decide);omega)
 · intro i hi
   rw [off_off]
   exact good.scr.ld (by omega)
 · intro i hi
   rw [off_off]
   exact good.scr.st (by omega)
 · intro j hj i hi b hb
   exact (outside_shift_iff B _ hd fit).mp (Or.inr (by have := sourceOutside j hj i hi b hb;omega))
 · intro b hb
   apply (outside_shift_iff B _ hd fit).mp
   left
   rw [ofs_off B (by have := hdr_lt_slot w 5 (show sArr 5<32 by decide);omega)]
   have := hdr_lt_slot w 5 (show sArr 5<32 by decide)
   omega
 · intro b hb
   apply (outside_shift_iff B _ hd fit).mp
   left
   rw [ofs_off B (by have := hdr_lt_slot w 5 (show sW<32 by decide);omega)]
   have := hdr_lt_slot w 5 (show sW<32 by decide)
   omega

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! Complete canonical-context selection into the existing Montgomery operand array. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem select_ok {s : State} {B table : Addr} {Z w v : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (width : w<2^31) (hv : v<32)
 (tablePtr : word s.mem B (8*VG.Impl.Ffdh.AArch64.Cached.sTab)=table)
 (digit : word s.mem B (8*VG.Impl.Ffdh.AArch64.Cached.sD)=BitVec.ofNat 64 v)
 (readSource : ∀ j<32, ∀ i<w, InRegions (s.rd++s.wr) (off table (8*w*j+8*i)) 8)
 (sourceOutside : ∀ j<32, ∀ i<w, ∀ b<8, Z≤ofs B (off table (8*w*j+8*i)+BitVec.ofNat 64 b)) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.select s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 5) w=wv s.mem table (8*w*v) w ∧
 Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
 have convert (m : Mem) (i : Nat) : word m (off B (slot w 5)) (8*i)=word m B (slot w 5+8*i) := by
  simp only [word,VG.Proof.Bignum.off_off]
 have nowrap : slot w 5+8*(w+2)≤2^64 := by
  have := good.scr.nowrap
  have := slot_le (w:=w) (by decide : 5<8)
  omega_arith
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.select
 rw [WP.seq_iff]
 refine WP.mono (const_ok good room positive width (by decide : 5<8) (by decide : 0<2^16)) ?_
 rintro u ⟨goodU,zeroU,frameU,restU⟩
 have arraysU : Arrays B w [5] s.mem u.mem := Arrays.of_outside (j:=5) (by simp) frameU (by omega_using []) (by omega_using [])
 have headerU (i : Nat) (hi : i<32) : word u.mem B (8*i)=word s.mem B (8*i) :=
  frameU.word (Or.inl (hdr_lt_slot w 5 hi)) (by omega_using [hi])
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x9,.x10,.x11] (Q:=fun z =>
  z.gpr .x9=table ∧ z.gpr .x10=BitVec.ofNat 64 v ∧ z.gpr .x11=0#64 ∧ z.mem=u.mem)
  ?_ rfl rfl rfl) ?_
 · brun [goodU.x0,hdr_enc (show VG.Impl.Ffdh.AArch64.Cached.sTab<32 by decide),
   hdr_enc (show VG.Impl.Ffdh.AArch64.Cached.sD<32 by decide),
   goodU.scr.ld (d:=8*VG.Impl.Ffdh.AArch64.Cached.sTab)
    (by have := hdr_lt_slot w 8 (show VG.Impl.Ffdh.AArch64.Cached.sTab<32 by decide);omega_using [room, this]),
   goodU.scr.ld (d:=8*VG.Impl.Ffdh.AArch64.Cached.sD)
    (by have := hdr_lt_slot w 8 (show VG.Impl.Ffdh.AArch64.Cached.sD<32 by decide);omega_using [room, this]),
   headerU VG.Impl.Ffdh.AArch64.Cached.sTab (by decide),
   headerU VG.Impl.Ffdh.AArch64.Cached.sD (by decide),tablePtr,digit]
 · rintro z ⟨⟨pointerZ,digitZ,candidateZ,memZ⟩,restZ⟩
   have restUZ := restU.trans restZ
   have goodZ : Good z B Z w mi :=
    ⟨goodU.scr.congr restZ.wr,(restZ.gpr .x0 (by decide)).trans goodU.x0,memZ ▸ goodU.hdr⟩
   have envZ : SelectEnv B table (off B (slot w 5)) w z := selectEnv_good goodZ room positive
    (fun j hj i hi => by rw [restUZ.rd,restUZ.wr];exact readSource j hj i hi) sourceOutside
   have zeros : ∀ i<w, word z.mem (off B (slot w 5)) (8*i)=0#64 := by
    intro i hi
    rw [convert,memZ]
    exact (wv_eq_zero_iff _ _ _ _).mp zeroU i hi
   refine WP.mono (selectScan_ok z envZ positive (by omega_using [width]) hv pointerZ digitZ candidateZ zeros) ?_
   rintro t ⟨_,words,frame,restT⟩
   have frameZ : Outside B (slot w 5) (8*w) z.mem t.mem :=
    outside_to_workspace (by omega_using [nowrap]) (by omega_using [nowrap]) frame
   have arraysZ : Arrays B w [5] z.mem t.mem := Arrays.of_outside (j:=5) (by simp) frameZ (by omega_using []) (by omega_using [])
   have totalArrays : Arrays B w [5] s.mem t.mem := by
    rw [memZ] at arraysZ
    exact arraysU.trans arraysZ
   have totalRest : Keep mmRegs s t := (restUZ.trans restT).mono (by simp [selectClobbers,mmRegs])
   refine ⟨good_after_arrays good totalArrays totalRest
    ((totalRest.gpr .x0 (by decide)).trans good.x0),?_,totalArrays,totalRest⟩
   apply wv_congr2
   intro i hi
   rw [←convert,words i hi,memZ]
   exact Mem.readW_congr fun b hb => InScr.of_arrays arraysU room (by simp) _ (sourceOutside v hv i hi b hb)

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The same Montgomery residues and bounds used by RSA, with a fixed-base exponent. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure Parameters where
 B : Addr
 Z : Nat
 w : Nat
 mi : BitVec 64
 P : Nat
 G : Nat
 N : Nat
 k : Nat
 src : Addr
 ctx : Addr
 table : Addr
 room : slot w 8≤Z
 positive : 2≤w
 width : w<2^31
 modulusPositive : 1<P
 coprime : Nat.Coprime (2^(64*w)) P

structure ModState (p : Parameters) (s : State) : Prop where
 good : Good s p.B p.Z p.w p.mi
 modulus : wv s.mem p.B (slot p.w 0) p.w=p.P
 inverse : ((word s.mem p.B (slot p.w 0)).toNat*p.mi.toNat+1)%2^64=0
 one : wv s.mem p.B (slot p.w 7) p.w=1
 r2 : wv s.mem p.B (slot p.w 4) p.w=2^(128*p.w)%p.P

structure Power (p : Parameters) (E : Nat) (s : State) : Prop extends ModState p s where
 bound : wv s.mem p.B (slot p.w 6) p.w<p.P
 value : wv s.mem p.B (slot p.w 6) p.w=Spec.Rsa.powMod p.G E p.P*2^(64*p.w)%p.P

theorem ModState.after_arrays {p : Parameters} {s t : State} {js : List Nat}
 (h : ModState p s) (good : Good t p.B p.Z p.w p.mi) (frame : Arrays p.B p.w js s.mem t.mem)
 (zero : 0∉js) (one : 7∉js) (r2 : 4∉js) : ModState p t := by
 have nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega_arith
 refine ⟨good,?_,?_,?_,?_⟩
 · exact (frame.wv_of_not_mem (by decide) zero nowrap).trans h.modulus
 · rw [frame.word0_of_not_mem (by decide) zero nowrap (by have := p.positive;omega_using [this])]
   exact h.inverse
 · exact (frame.wv_of_not_mem (by decide) one nowrap).trans h.one
 · exact (frame.wv_of_not_mem (by decide) r2 nowrap).trans h.r2

theorem ModState.after_header {p : Parameters} {s t : State} {i : Nat}
 (h : ModState p s) (good : Good t p.B p.Z p.w p.mi)
 (frame : Outside p.B (8*i) 8 s.mem t.mem) (hi : i<32) : ModState p t := by
 have nowrap : slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega_arith
 have below (j : Nat) : 8*i+8≤slot p.w j := hdr_lt_slot _ _ hi
 refine ⟨good,?_,?_,?_,?_⟩
 · exact (frame.wv (Or.inr (below 0)) (by have := slot_le (w:=p.w) (by decide : 0<8);omega_using [nowrap, this])).trans h.modulus
 · rw [frame.word (Or.inr (below 0)) (by have := slot_le (w:=p.w) (by decide : 0<8);omega_using [nowrap, this])]
   exact h.inverse
 · exact (frame.wv (Or.inr (below 7)) (by have := slot_le (w:=p.w) (by decide : 7<8);omega_using [nowrap, this])).trans h.one
 · exact (frame.wv (Or.inr (below 4)) (by have := slot_le (w:=p.w) (by decide : 4<8);omega_using [nowrap, this])).trans h.r2

theorem Power.after_arrays {p : Parameters} {E : Nat} {s t : State} {js : List Nat}
 (h : Power p E s) (good : Good t p.B p.Z p.w p.mi) (frame : Arrays p.B p.w js s.mem t.mem)
 (zero : 0∉js) (one : 7∉js) (r2 : 4∉js) (y : 6∉js) : Power p E t := by
 have nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega_arith
 have same := frame.wv_of_not_mem (by decide : 6<8) y nowrap
 exact ⟨h.toModState.after_arrays good frame zero one r2,by rw [same];exact h.bound,by rw [same];exact h.value⟩

theorem Power.after_header {p : Parameters} {E : Nat} {s t : State} {i : Nat}
 (h : Power p E s) (good : Good t p.B p.Z p.w p.mi)
 (frame : Outside p.B (8*i) 8 s.mem t.mem) (hi : i<32) : Power p E t := by
 have nowrap : slot p.w 8≤2^64 := by have := h.good.scr.nowrap;have := p.room;omega_arith
 have same : wv t.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w :=
  frame.wv (Or.inr (hdr_lt_slot _ _ hi)) (by have := slot_le (w:=p.w) (by decide : 6<8);omega_using [nowrap, this])
 exact ⟨h.toModState.after_header good frame hi,by rw [same];exact h.bound,by rw [same];exact h.value⟩

/-- One genuine Montgomery square doubles the encoded exponent. -/
theorem power_square (M : Mont) {p : Parameters} {E : Nat} {s : State} (h : Power p E s) :
 WP isa (M.mm 6 6 6) s fun t =>
 Power p (2*E) t ∧ Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 6<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse h.bound) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have valueT := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded p.coprime boundT h.value productT
 exact ⟨⟨modT,boundT,valueT⟩,frame,rest⟩

/-- A selected residue adds its canonical comb exponent. -/
theorem power_product (M : Mont) {p : Parameters} {E F : Nat} {s : State} (h : Power p E s)
 (selected : wv s.mem p.B (slot p.w 5) p.w=Spec.Rsa.powMod p.G F p.P*2^(64*p.w)%p.P) :
 WP isa (M.mm 6 6 5) s fun t =>
 Power p (E+F) t ∧ Arrays p.B p.w [2,3,6] s.mem t.mem ∧ Keep mmRegs s t := by
 have bound5 : wv s.mem p.B (slot p.w 5) p.w<p.P := by rw [selected];exact Nat.mod_lt _ (by have := p.modulusPositive;omega_using [this])
 refine WP.mono (crtMmN_ok M h.good p.room p.positive p.width (by decide : 6<8)
  (by decide : 6<8) (by decide : 5<8) (by decide) (by decide) (by decide) (by decide) (by decide)
  h.modulus h.inverse bound5) ?_
 rintro t ⟨goodT,modulusT,inverseT,boundT,productT,frame,rest⟩
 have modT := h.toModState.after_arrays goodT frame (by decide) (by decide) (by decide)
 have valueT := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded p.coprime boundT h.value selected productT
 exact ⟨⟨modT,boundT,valueT⟩,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached
