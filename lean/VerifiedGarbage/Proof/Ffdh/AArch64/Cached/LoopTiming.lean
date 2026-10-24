module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.RowTiming
import VerifiedGarbage.Proof.Framework.Omega

/-! The complete loop count depends only on the public policy width. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero)
open VG.Spec.Rsa.FixedBaseComb (rows)
open VG.Proof.Rsa.FixedBaseComb (rows_pos rows_small)

structure LoopPublic where
 p : Parameters
 positive : 0<p.N
 width : p.N≤8192
 size : p.k<2^31
 scalarWidth : p.N≤8*p.k

def LoopReady (q : LoopPublic) (j : Nat) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E (rows q.p.N-j) s ∧ Spec.Rsa.os2ip bs<2^q.p.N

def LoopDone (q : LoopPublic) (s : State) : Prop :=
 ∃ bs E, Running q.p bs E 0 s

def loopDigit (q : LoopPublic) (j : Nat) : DigitPublic :=
 ⟨q.p,rows q.p.N-j-1,q.size,q.scalarWidth,by have := (rows_small q.width).1;omega⟩

theorem loop_ct (M : Mont) : RelCT isa (Two fun q s => LoopReady q 0 s)
 (.loop (Comb.step M.mm) (.nonzero .x .x3)) (Two LoopDone) := by
 have hct : RelCT isa (Two fun (q : LoopPublic × Nat) s => q.2<rows q.1.p.N ∧ LoopReady q.1 q.2 s)
   (Comb.step M.mm) (fun _ _ => True) :=
  two_map (fun q => loopDigit q.1 q.2) (by
   rintro ⟨q,j⟩ s ⟨hj,bs,E,h,bound⟩
   change j<rows q.p.N at hj
   refine ⟨bs,E,?_,bound⟩
   change Running q.p bs E ((rows q.p.N-j-1)+1) s
   have eq : rows q.p.N-j=(rows q.p.N-j-1)+1 := by omega
   rw [←eq]
   exact h) (row_ct M)
 have loop := two_loop (Φ:=LoopReady) (Ψ:=LoopDone) (fun q => rows q.p.N) hct (by
   intro q j s hj h
   obtain ⟨bs,E,h,bound⟩ := h
   have dBound := (rows_small q.width).1
   have eq : rows q.p.N-j=(rows q.p.N-j-1)+1 := by omega
   have run : Running q.p bs E ((rows q.p.N-j-1)+1) s := by rw [←eq];exact h
   refine WP.mono (running_step M run (h.reads.length ▸ q.size) (h.reads.length ▸ q.scalarWidth)
    (by omega) bound) ?_
   rintro t ⟨next,_,index,_⟩
   have remaining : rows q.p.N-j-1=rows q.p.N-(j+1) := by omega
   refine ⟨?_,fun _ => ⟨bs,_,remaining ▸ next,bound⟩,fun last => ?_⟩
   · rw [eval_nonzero,index]
     change some (BitVec.ofNat 64 (rows q.p.N-j-1) != 0#64)=some (decide (j+1<rows q.p.N))
     rw [ofNat_nonzero (by omega)]
     have eqBool : (0<rows q.p.N-j-1) ↔ (j+1<rows q.p.N) := by omega
     simp only [eqBool]
   · have zero : rows q.p.N-j-1=0 := by omega
     exact ⟨bs,_,zero ▸ next⟩)
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>
  ⟨q,⟨rows_pos q.positive,hs⟩,⟨rows_pos q.positive,ht⟩,sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.Cached
