module

import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Trim
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointInit
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Core
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.JointLoop

/-! Complete joint multiplication from the two public signed digit streams. -/

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
