module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.RowTiming
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! ### `Ffdh.AArch64.Cached.LoopTiming`, which only this module used -/

section

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
 ⟨q.p,rows q.p.N-j-1,q.size,q.scalarWidth,by have := (rows_small q.width).1;omega_using [this]⟩

theorem loop_ct (M : Mont) : RelCT isa (Two fun q s => LoopReady q 0 s)
 (.loop (Comb.step M.mm) (.nonzero .x .x3)) (Two LoopDone) := by
 have hct : RelCT isa (Two fun (q : LoopPublic × Nat) s => q.2<rows q.1.p.N ∧ LoopReady q.1 q.2 s)
   (Comb.step M.mm) (fun _ _ => True) :=
  two_map (fun q => loopDigit q.1 q.2) (by
   rintro ⟨q,j⟩ s ⟨hj,bs,E,h,bound⟩
   change j<rows q.p.N at hj
   refine ⟨bs,E,?_,bound⟩
   change Running q.p bs E ((rows q.p.N-j-1)+1) s
   have eq : rows q.p.N-j=(rows q.p.N-j-1)+1 := by omega_using [hj]
   rw [←eq]
   exact h) (row_ct M)
 have loop := two_loop (Φ:=LoopReady) (Ψ:=LoopDone) (fun q => rows q.p.N) hct (by
   intro q j s hj h
   obtain ⟨bs,E,h,bound⟩ := h
   have dBound := (rows_small q.width).1
   have eq : rows q.p.N-j=(rows q.p.N-j-1)+1 := by omega_using [hj]
   have run : Running q.p bs E ((rows q.p.N-j-1)+1) s := by rw [←eq];exact h
   refine WP.mono (running_step M run (h.reads.length ▸ q.size) (h.reads.length ▸ q.scalarWidth)
    (by omega_using [dBound]) bound) ?_
   rintro t ⟨next,_,index,_⟩
   have remaining : rows q.p.N-j-1=rows q.p.N-(j+1) := by omega_using []
   refine ⟨?_,fun _ => ⟨bs,_,remaining ▸ next,bound⟩,fun last => ?_⟩
   · rw [eval_nonzero,index]
     change some (BitVec.ofNat 64 (rows q.p.N-j-1) != 0#64)=some (decide (j+1<rows q.p.N))
     rw [ofNat_nonzero (by omega_using [dBound])]
     have eqBool : (0<rows q.p.N-j-1) ↔ (j+1<rows q.p.N) := by omega_using []
     simp only [eqBool]
   · have zero : rows q.p.N-j-1=0 := by omega_using [last]
     exact ⟨bs,_,zero ▸ next⟩)
 exact loop.mono (fun _ _ ⟨q,hs,ht,sp⟩ =>
  ⟨q,⟨rows_pos q.positive,hs⟩,⟨rows_pos q.positive,ht⟩,sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! Complete cached exponentiation with independent secret scalars and public policy geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure CombPublic extends LoopPublic where
 pointer : p.table=p.ctx+BitVec.ofNat 64 (24+16*p.w)

def CombReady (q : CombPublic) (s : State) : Prop :=
 ∃ bs, Initial q.p bs s ∧ Spec.Rsa.os2ip bs<2^q.p.N

def InitReady (q : CombPublic) (s : State) : Prop :=
 ∃ bs, Power q.p 0 s ∧ Controls q.p.B q.p.src q.p.ctx bs.length q.p.N s ∧
 ReadEnv q.p bs s ∧ Spec.Rsa.os2ip bs<2^q.p.N

def combWs (q : CombPublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

theorem powerInit_ct (M : Mont) : RelCT isa (Two CombReady)
 (.seq (const 7 1) (M.mm 6 4 7)) (fun _ _ => True) := by
 refine RelCT.seq (two_post (Ψ:=fun q s => GoodW (combWs q) s)
  (two_map combWs (fun q s h => by obtain ⟨bs,h,_⟩:=h;exact ⟨q.p.mi,h.good,q.p.room⟩)
   (const_ct 7 1 (by decide) (by taint_decide) (by taint_decide))) ?_)
  (two_map combWs (fun _ _ h => h) (M.ct (by simp [MmUse,Public.aY,Public.aR2,Public.aOne])))
 rintro q s ⟨bs,h,_⟩
 exact WP.mono (const_ok h.good q.p.room (by have := q.p.positive;omega_using [this]) q.p.width
  (by decide : 7<8) (by decide : 1<2^16)) fun _ ⟨good,_,_,_⟩ => ⟨q.p.mi,good,q.p.room⟩

theorem comb_ct (M : Mont) : RelCT isa (Two CombReady) (Comb.code M.mm) (fun _ _ => True) := by
 unfold Comb.code
 apply RelCT.assoc
 refine RelCT.seq (two_post (Ψ:=InitReady) (powerInit_ct M) ?_) ?_
 · rintro q s ⟨bs,h,bound⟩
   exact WP.mono (initial_power M h) fun _ ⟨power,controls,reads,_,_⟩ => ⟨bs,power,controls,reads,bound⟩
 · apply RelCT.assoc
   refine RelCT.seq (two_piece (Ψ:=fun q s => LoopReady q.toLoopPublic 0 s) [.x0] ?_ (by taint_decide) ?_) ?_
   · rintro q s t ⟨bs,hs,_,_,_⟩ ⟨bt,ht,_,_,_⟩ r hr
     have : r= .x0 := by simpa using hr
     subst r
     exact hs.good.x0.trans ht.good.x0.symm
   · rintro q s ⟨bs,power,controls,reads,bound⟩
     exact WP.mono (init_controls power controls reads q.pointer) fun _ ⟨run,_,_⟩ => ⟨bs,0,run,bound⟩
   · refine RelCT.seq (two_map CombPublic.toLoopPublic (fun _ _ h => h) (loop_ct M)) ?_
     exact two_map (fun q : LoopPublic => (⟨q.p.B,q.p.Z,q.p.w⟩ : Ws))
      (fun q s h => by obtain ⟨bs,E,h⟩:=h;exact ⟨q.p.mi,h.power.good,q.p.room⟩)
      (M.ct (by simp [MmUse,Public.aY,Public.aOne]))

end VG.Proof.Ffdh.AArch64.Cached
