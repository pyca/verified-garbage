module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeSquareLoop
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Comb-table squaring uses a public row count with independent residue values. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (eval_nonzero ne_zero_iff)

structure SquarePublic where
 p : Parameters
 n : Nat
 positive : 0<n
 fit : n<2^64

def SquareReady (q : SquarePublic) (j : Nat) (s : State) : Prop :=
 ∃ E,Power q.p E s ∧ Counter q.p.B (q.n-j) s

theorem squareStep_ct (M : Mont) :
 RelCT isa (Two fun (q : SquarePublic × Nat) s => SquareReady q.1 q.2 s)
 (.seq (M.mm 6 6 6) (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI])) (fun _ _ => True) := by
 refine RelCT.seq (two_post (Ψ:=fun (q : SquarePublic × Nat) s =>SquareReady q.1 q.2 s)
  (two_map (fun q => (⟨q.1.p.B,q.1.p.Z,q.1.p.w⟩ : Ws))
   (fun q s h =>by obtain ⟨E,power,_⟩:=h;exact ⟨q.1.p.mi,power.good,q.1.p.room⟩)
   (M.ct (by simp [MmUse,Public.aY]))) ?_) (two_taint [.x0] ?_ (by taint_decide))
 · rintro ⟨q,j⟩ s ⟨E,power,counter⟩
   refine WP.mono (power_square M power) ?_
   rintro t ⟨powerT,frame,_⟩
   exact ⟨2*E,powerT,(arrays_header frame (by decide)).trans counter⟩
 · intro q s t hs ht r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   obtain ⟨E,power,_⟩ := hs
   obtain ⟨F,other,_⟩ := ht
   exact power.good.x0.trans other.good.x0.symm

theorem squareLoop_ct (M : Mont) :
 RelCT isa (Two fun q s =>SquareReady q 0 s)
 (.loop (.seq (M.mm 6 6 6) (.block [ldh .x3 sI,.subImm .x .x3 .x3 1,sth .x3 sI]))
  (.nonzero .x .x3)) (fun _ _ => True) := by
 have loop := two_loop (cond:= .nonzero .x .x3) (Φ:=SquareReady) (Ψ:=fun _ _ =>True) (fun q =>q.n)
  ((squareStep_ct M).mono (fun _ _ h =>two_mono (fun _ _ h =>h.2) h) (fun _ _ h =>h)) (by
   intro q j s hj h
   obtain ⟨E,power,counter⟩ := h
   have initial : SquareInv s q.p E (q.n-j) 0 s :=
    ⟨by simpa using power,by simpa using counter,Frm.refl _ _ _,VG.Proof.MlKem.AArch64.Keep.refl _ _⟩
   refine WP.mono (precomputeSquareStep M (by have := q.fit;omega) (by omega : 0<q.n-j) initial) ?_
   rintro t ⟨state,branch⟩
   refine ⟨?_,fun _ =>⟨_,state.power,?_⟩,fun _ =>trivial⟩
   · rw [eval_nonzero,ne_zero_iff]
     have eq : (0+1≠q.n-j) ↔ j+1<q.n := by omega
     by_cases nonzero : (t.gpr .x3).toNat≠0
     · rw [decide_eq_true nonzero,decide_eq_true ((branch.trans eq).mp nonzero)]
     · have last : ¬j+1<q.n := fun h =>nonzero ((branch.trans eq).mpr h)
       rw [decide_eq_false nonzero,decide_eq_false last]
   · change Counter q.p.B (q.n-(j+1)) t
     have eq : q.n-j-(0+1)=q.n-(j+1) := by omega
     simpa only [eq] using state.counter)
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>⟨q,⟨q.positive,hs⟩,⟨q.positive,ht⟩,sp⟩) (fun _ _ _ =>trivial)

end VG.Proof.Ffdh.AArch64.Cached
