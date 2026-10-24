module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectStep
import VerifiedGarbage.Proof.Framework.Omega

/-! Exactly 32 masked rows select the canonical entry without a secret address. -/
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
