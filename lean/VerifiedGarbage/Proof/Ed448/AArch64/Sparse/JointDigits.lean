module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Core
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointLoop
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Const
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint

import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.TrimStep
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
/-! Complete joint multiplication from the two public signed digit streams. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/Trim.lean`, which only this module imported.
section

/-! Leading zero pairs may be omitted: both remaining recoded scalars are zero above the chosen start. -/

section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off)

private theorem residual_zero {wide:Bool} {k i:Nat}
    (hr:residual wide k (i+1)=0) (hd:digitAt wide k i=0) : residual wide k i=0:=by
  have h:=WnafWide.residual_step wide k i
  rw [hr,hd] at h
  omega

theorem trim_ok {s:State} {base:Addr} (hs:Scr s base) {S K:Nat}
    (hS:S<VG.Impl.Ed448.WnafWide.scalarLimit) (hK:K<VG.Impl.Ed448.WnafWide.scalarLimit) (hc:s.gpr .x19=BitVec.ofNat 64 464)
    (hsd:∀ i<464,s.mem (off base (SDIG+i))=BitVec.ofInt 8 (digitAt true S i))
    (hkd:∀ i<464,s.mem (off base (BITS+i))=BitVec.ofInt 8 (digitAt false K i)) :
    WP isa (.loop (.block trimStep) (.zero .x .x9)) s fun t =>
      ∃ i<464,t.gpr .x19=BitVec.ofNat 64 i ∧ residual true S (i+1)=0 ∧ residual false K (i+1)=0 ∧
        Keeps trimClob s t ∧ t.mem=s.mem:=by
  have rS:residual true S 464=0:=WnafWide.residual_end true (k:=S) (by exact hS)
  have rK:residual false K 464=0:=WnafWide.residual_end false (k:=K) (by exact hK)
  let inv:=fun m (t:State) =>
    0<m ∧ m≤464 ∧ t.gpr .x19=BitVec.ofNat 64 m ∧
      residual true S m=0 ∧ residual false K m=0 ∧ Keeps trimClob s t ∧ t.mem=s.mem
  refine WP.loop (M:=isa) (body:=.block trimStep) (c:=.zero .x .x9)
    (Q:=fun t => ∃ i<464,t.gpr .x19=BitVec.ofNat 64 i ∧ residual true S (i+1)=0 ∧
      residual false K (i+1)=0 ∧ Keeps trimClob s t ∧ t.mem=s.mem)
    inv ?_ 464 s ⟨by decide,by decide,hc,rS,rK,Keeps.refl _ _,rfl⟩
  intro m u ⟨hm,hm',u19,rs,rk,ku,um⟩
  obtain ⟨i,rfl⟩:∃ i,m=i+1:=⟨m-1,by omega⟩
  have hi:i<464:=by omega
  refine WP.mono (trimStep_ok (ds:=digitAt true S i) (dk:=digitAt false K i) (hs.of_keeps ku (by decide)) hi u19
    (baseDigit_bound S i) (by have := keyDigit_bound K i;omega)
    (by rw [um];exact hsd i hi) (by rw [um];exact hkd i hi))
    fun t ⟨t19,tz,kt,tm⟩ => ?_
  simp only [eval,State.read,BitVec.setWidth_eq,tz]
  by_cases hz:digitAt true S i=0 ∧ digitAt false K i=0 ∧ i≠0
  · refine Or.inr ⟨?_,i,by omega,?_⟩
    · exact congrArg some (decide_eq_true hz)
    · exact ⟨by omega,by omega,t19,residual_zero rs hz.1,residual_zero rk hz.2.1,
        ku.trans kt,tm.trans um⟩
  · refine Or.inl ⟨?_,i,hi,t19,rs,rk,ku.trans kt,tm.trans um⟩
    exact congrArg some (decide_eq_false hz)

end VG.Proof.Ed448.AArch64.Sparse
end

end

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/JointInit.lean`, which only this module imported.
section

/-! Initialize a bounded neutral accumulator and the joint public counter. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Impl.X448.AArch64.Base (constSlot)
open VG.Proof.X448.AArch64 (Scr Keeps Outside2 limbs word)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.X448.AArch64.Base (pt limb_lt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem jointInit_ok {s:State} {base:Addr} (hs:Scr s base) (hb:BEnv s.mem base) :
    WP isa (.block init) s fun t => Core base t ∧ t.gpr .x19=BitVec.ofNat 64 464 ∧
      pt (EV t.mem base) 3 4 5=Spec.Ed448.identity ∧
      Outside2 base 64 2816 ACC 1152 s.mem t.mem ∧
      Keeps (.x19::pointClob) s t := by
  simp only [init,List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (constE hs hb 3 0) fun a ⟨ab,_,ae,_,ao,ak⟩ => ?_
  have ha:=hs.of_keeps ak (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE ha ab 4 1) fun b ⟨bb,_,be,_,bo,bk⟩ => ?_
  have hb':=ha.of_keeps bk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE hb' bb 5 1) fun c ⟨cb,_,ce,cv,co,ck⟩ => ?_
  have hc:=hb'.of_keeps ck (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE hc cb 19 0) fun d ⟨db,dsm,de,dv,do',dk⟩ => ?_
  have hd:=hc.of_keeps dk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (constE hd db 20 1) fun e ⟨eb,esm,ee,_,eo,ek⟩ => ?_
  have he:=hd.of_keeps ek (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setCounter_ok e 464 (by decide))
    fun t ⟨t19,tg,tm,tr,tw⟩ => ?_
  have tk:Keeps [.x19] e t:=⟨fun r hr => tg r (by simpa only [List.mem_singleton] using hr),tr,tw⟩
  have et:EV t.mem base=EV e.mem base:=by rw [tm]
  refine ⟨⟨he.of_keeps tk (by decide),?_,?_,?_,?_⟩,t19,?_,?_,?_⟩
  · rw [tm]
    exact eb
  · intro w hw
    rw [tm,esm 19 (by decide) w hw]
    change (word d.mem base (slot (19:Index).val+8*w)).toNat=0
    rw [dv w hw,Window.limb_zero]
    rfl
  · rw [et,ee]
    rfl
  · intro w hw
    change limbs t.mem base (slot (5:Index).val) w<Mb
    rw [tm,esm 5 (by decide) w hw,dsm 5 (by decide) w hw]
    change (word c.mem base (slot (5:Index).val+8*w)).toNat<Mb
    rw [cv w hw]
    exact Nat.lt_of_lt_of_le (limb_lt 1 w) (by decide)
  · rw [et,ee,de,ce,be,ae]
    rfl
  · intro x hx _
    rw [tm,eo x (by simp only [slot] at hx ⊢;omega),do' x (by simp only [slot] at hx ⊢;omega),
      co x (by simp only [slot] at hx ⊢;omega),bo x (by simp only [slot] at hx ⊢;omega),
      ao x (by simp only [slot] at hx ⊢;omega)]
  · have k1:Keeps (.x19::pointClob) s c:=((ak.mono (by decide)).trans (bk.mono (by decide))).trans
      (ck.mono (by decide))
    have k2:Keeps (.x19::pointClob) c t:=((dk.mono (by decide)).trans (ek.mono (by decide))).trans
      (tk.mono (by decide))
    exact k1.trans k2

end VG.Proof.Ed448.AArch64.Sparse
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.WnafWide (digitAt residual)
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Scr Keeps off)
open VG.Proof.X448.AArch64.Fast (BEnv)
open VG.Proof.Curve448.AArch64.Fast (Mb)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Proof.Ed448 (Rep baseAff dZ)
open VG.Proof.EdwardsLaw (EPoint)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem incCounter_ok {s:State} {i:Nat} (hc:s.gpr .x19=BitVec.ofNat 64 i) :
    WP isa (.block [.addImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19=BitVec.ofNat 64 (i+1) ∧ Keeps [.x19] s t ∧ t.mem=s.mem:=by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,Nat.reduceLT,
    ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,hc,Option.some.injEq,exists_eq_left']
  refine ⟨(BitVec.ofNat_add i 1).symm,⟨fun r hr => ?_,rfl,rfl⟩,rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write,hr,ite_false]

structure JointOut (s:State) (base:Addr) (P:Spec.Ed448.Point) (S K:Nat) (t:State) : Prop where
  core : Core base t
  rep : ∀ a:EPoint dZ,Rep P a → Rep (pt (EV t.mem base) 3 4 5) ((S:Int) • baseAff+(K:Int) • a)
  chk : t.gpr .x20=s.gpr .x20
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  mem : JointFrame base s.mem t.mem

theorem jointDigits_ok (hA:AffineOk) {s:State} {base:Addr} {P:Spec.Ed448.Point} {S K:Nat}
    (hs:Scr s base) (hb:BEnv s.mem base) (ht:OddTabOk s.mem base P 8)
    (hxb:∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<Mb)
    (hbt:BaseTableAt s base (s.syms baseSym)) (hS:S<VG.Impl.Ed448.WnafWide.scalarLimit) (hK:K<VG.Impl.Ed448.WnafWide.scalarLimit)
    (hsd:∀ i<464,s.mem (off base (SDIG+i))=BitVec.ofInt 8 (digitAt true S i))
    (hkd:∀ i<464,s.mem (off base (BITS+i))=BitVec.ofInt 8 (digitAt false K i)) :
    WP isa jointDigits s (JointOut s base P S K):=by
  unfold jointDigits
  refine WP.seq (WP.mono_syms (jointInit_ok hs hb) fun a ⟨ha,a19,ap,af,ak⟩ asy => ?_)
  have fa:JointFrame base s.mem a.mem:=fun x hx hy _ => af x hx hy
  have asd:∀ i<464,a.mem (off base (SDIG+i))=BitVec.ofInt 8 (digitAt true S i):=by
    intro i hi
    rw [fa.baseDigit hi]
    exact hsd i hi
  have akd:∀ i<464,a.mem (off base (BITS+i))=BitVec.ofInt 8 (digitAt false K i):=by
    intro i hi
    rw [fa.keyDigit hi]
    exact hkd i hi
  refine WP.seq (WP.mono_syms (trim_ok ha.scr hS hK a19 asd akd)
    fun b ⟨i,hi,b19,rs,rk,bk,bm⟩ bsy => ?_)
  have hb':=ha.regsOnly bk bm (by decide)
  refine WP.seq (WP.mono_syms (incCounter_ok b19) fun c ⟨c19,ck,cm⟩ csy => ?_)
  have hc:=hb'.regsOnly ck cm (by decide)
  have mc:c.mem=a.mem:=cm.trans bm
  have fc:JointFrame base s.mem c.mem:=by rw [mc];exact fa
  have cs:Keeps (.x19::pointClob) s c:=
    ak.trans ((bk.mono (by decide)).trans (ck.mono (by decide)))
  have ci:JointInv c base P S K (i+1) c:=by
    refine ⟨by omega,hc,c19,fc.oddTable ht,fc.xbounds hxb,?_,?_,?_,?_,rfl,rfl,rfl,fun _ _ _ _ => rfl⟩
    · rw [csy,bsy,asy]
      exact hbt.of_frame (by rw [cs.2.1,cs.2.2]) fc
    · intro j hj
      rw [mc]
      exact asd j hj
    · intro j hj
      rw [mc]
      exact akd j hj
    · intro q _
      rw [mc,ap,rs,rk]
      simpa only [Int.natCast_zero,zero_smul,add_zero] using VG.Proof.Ed448.identity_rep
  refine WP.mono (jointLoop_ok hA (by omega) ci) fun t ht => ?_
  refine ⟨ht.core,?_,?_,?_,?_,fun x a b c => (ht.mem x a b c).trans (fc x a b c)⟩
  · intro a ha
    exact ht.rep a ha
  · rw [ht.chk,cs.1 _ (by decide)]
  · rw [ht.rd,cs.2.1]
  · rw [ht.wr,cs.2.2]

end VG.Proof.Ed448.AArch64.Sparse
