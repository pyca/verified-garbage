module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Comb
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LoopTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

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
 exact WP.mono (const_ok h.good q.p.room (by have := q.p.positive;omega) q.p.width
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
