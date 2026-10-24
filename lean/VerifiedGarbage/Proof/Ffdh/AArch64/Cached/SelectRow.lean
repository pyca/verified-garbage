module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectWord
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

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
   (Or.inr (by have := separate j hj b hb;omega))
 have dstWord : word t.mem dst (8*j)=word s0.mem dst (8*j) :=
  h.frame.word (Or.inr (by omega)) (by omega)
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
   · rw [(writeW_outside t.mem dst _ (by omega)).word (by omega) (by omega)]
     exact h.done i hi
   · exact word_writeW_self _ _ _ _
 · rw [memU,mem]
   intro x hx
   rw [writeW_outside t.mem dst _ (by omega) x (by omega)]
   exact h.frame x (by omega)
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
 exact WP.mono (wp_countdown (by omega) positive (SelectRowInv s src dst mask)
  (fun j hj t h _ => selectRowStep_ok fit hj readSource readOutput writeOutput separate choose h)
  init count) fun _ h => ⟨h.done,h.frame,h.source,h.output,h.keep⟩

end VG.Proof.Ffdh.AArch64.Cached
