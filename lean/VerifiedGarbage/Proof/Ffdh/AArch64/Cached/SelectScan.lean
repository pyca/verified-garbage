module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectEnv

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
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
   · have same : v<j+1 ↔ v<j := by omega
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
     refine ⟨?_,32-(j+1),by omega,j+1,rfl,more,next⟩
     rw [condition,decide_eq_true more]
   · have last : j+1=32 := by omega
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
