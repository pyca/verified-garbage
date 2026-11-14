module

public import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Bignum.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp

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
