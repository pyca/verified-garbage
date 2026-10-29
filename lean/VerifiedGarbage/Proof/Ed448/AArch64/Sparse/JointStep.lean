module

public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.BaseOperand
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Sign
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Table
public import VerifiedGarbage.Proof.Ed448.AArch64.Window.Select

import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Move
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.DigitLoads
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Magnitude
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X448.AArch64.Base.AddEnv
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.SelectCopy
import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
/-! A shared doubling followed by the two signed public additions. -/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/AddBase.lean`, which only this module imported.
section

/-! One signed affine base addition, skipping the zero digit. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Proof.X448.AArch64 (off)
open VG.Proof.X448.AArch64.Weak (Env)
open VG.Proof.X448.AArch64.Base (pt zero_env affEnv affPt affPt_eq)
open VG.Proof.Ed448.WnafWide (maybeAdd baseEntry signedPoint)
open VG.Proof.X448 (basePt)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

private theorem signedEnv_affine (negative:Bool) (e:Env) :
    basePt (signedEnv negative e 6,signedEnv negative e 7)=
      signedPoint negative (basePt (e 6,e 7)):=by cases negative <;> rfl

private theorem affinePoint (e:Env) : pt (affEnv 3 4 5 6 7 e) 3 4 5=
    affPt (e 3) (e 4) (e 5) (e 6) (e 7) (e 19):=rfl

theorem addBase_ok (hA:AffineOk) {s:State} {base:Addr} (h:Core base s)
    (ht:BaseTableAt s base (s.syms baseSym))
    {i:Nat} (hi:i<464) (hc:s.gpr .x19=BitVec.ofNat 64 i)
    {d:Int} (hd:-127≤d ∧ d≤127) (hbit:s.mem (off base (SDIG+i))=BitVec.ofInt 8 d) :
    WP isa addBase s fun t => Core base t ∧ PointKeep base s t ∧
      pt (EV t.mem base) 3 4 5=maybeAdd d (pt (EV s.mem base) 3 4 5) (baseEntry d) := by
  unfold addBase
  refine WP.seq (WP.mono_syms (baseDigit_ok h.scr hi hc) fun a ⟨a11,ak,am⟩ asy => ?_)
  have ka:=PointKeep.of_keeps (base:=base) ak am (by decide)
  have ha:=h.of_keeps ka am
  have az:(a.gpr .x11==0)=decide (d=0):=by rw [a11,hbit];exact encoded_zero hd
  by_cases h0:d=0
  · have ev:isa.eval (.nonzero .x .x11) a=some false:=by
      simp only [eval,State.read,BitVec.setWidth_eq,bne,az,h0,decide_true,Bool.not_true]
    refine VG.WP.ite false ev (fun z => Bool.noConfusion z) fun _ => WP.block_nil ?_
    refine ⟨ha,ka,?_⟩
    rw [am,maybeAdd,ite_eq_left h0]
  · have ev:isa.eval (.nonzero .x .x11) a=some true:=by
      simp only [eval,State.read,BitVec.setWidth_eq,bne,az,h0,decide_false,Bool.not_false]
    refine VG.WP.ite true ev (fun _ => ?_) (fun z => Bool.noConfusion z)
    rw [WP.seq_iff]
    refine WP.mono_syms (magnitude_ok hd (by rw [a11,hbit])) fun b ⟨b21,b11,bk,bm⟩ bsy => ?_
    have kb:=PointKeep.of_keeps (base:=base) bk bm (by decide)
    have hb:=ha.of_keeps kb bm
    have htab:BaseTableAt b base (b.syms baseSym):=by
      rw [bsy,asy]
      exact (ka.trans kb).baseTable ht
    rw [WP.seq_iff]
    refine WP.mono (baseOperand_ok hb.scr hb.env htab (by omega) b11)
      fun c ⟨ck,cb,csm,cx,cp,cr⟩ => ?_
    have kc:=PointKeep.of_field ck
    have hcorec:=hb.unchanged kc cb csm (by decide) (by decide) (by decide)
    have c21:c.gpr .x21=BitVec.ofNat 64 (if decide (d<0) then 1 else 0):=by
      rw [cr.1 _ (by decide),b21]
      by_cases hn:d<0 <;> simp only [hn,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false]
    refine WP.seq (WP.mono (negateIf_ok (decide (d<0)) hcorec cx c21)
      fun u ⟨hu,ku,usm,ue⟩ => ?_)
    have up:basePt (EV u.mem base 6,EV u.mem base 7)=baseEntry d:=by
      rw [ue,signedEnv_affine,congrArg basePt cp,baseEntry,ite_eq_right h0]
    have uq:pt (EV u.mem base) 3 4 5=pt (EV s.mem base) 3 4 5:=by
      rw [acc_of_same usm (by decide) (by decide) (by decide),
        acc_of_same csm (by decide) (by decide) (by decide),bm,am]
    refine WP.mono (hA.ok hu.scr hu.env (zero_env hu.zero).2)
      fun t ⟨tk,tb,tsm,_,_,tz,te⟩ => ?_
    have kp:=PointKeep.of_affine tk
    refine ⟨hu.after kp tb tsm (by decide) (by decide) tz,
      (((ka.trans kb).trans kc).trans ku).trans kp,?_⟩
    rw [te,affinePoint,(zero_env hu.zero).1,affPt_eq,maybeAdd,ite_eq_right h0]
    change VG.Proof.X448.addPt (pt (EV u.mem base) 3 4 5) (basePt (EV u.mem base 6,EV u.mem base 7))=_
    rw [uq,up]

end VG.Proof.Ed448.AArch64.Sparse
end

end

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/SelectKey.lean`, which only this module imported.
section

/-! Direct public indexing of one of eight projective odd key multiples. -/

section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.Ed448.AArch64 (TAB)
open VG.Proof.X448.AArch64 (Scr Keeps Outside off ofs word ofs_off')
open VG.Proof.Ed448.AArch64.Window (dst tw)

private theorem address_fact : ∀ m<16,
    ((BitVec.ofNat 64 m>>>1)<<<7)+((BitVec.ofNat 64 m>>>1)<<<6)=
      BitVec.ofNat 64 (192*(m/2)) := by decide +kernel

private def keyAddress : List Instr :=
  [.lsr .x .x11 .x11 1,.lsl .x .x8 .x11 7,.lsl .x .x9 .x11 6,
   .add .x .x8 .x8 .x9,.add .x .x8 .x8 .x3]

private theorem keyAddress_ok {s:State} {base:Addr} (hs:Scr s base) {m:Nat}
    (hm:m<16) (h11:s.gpr .x11=BitVec.ofNat 64 m) :
    WP isa (.block keyAddress) s fun t =>
      t.gpr .x8=off base (192*(m/2)) ∧ Keeps [.x11,.x8,.x9] s t ∧ t.mem=s.mem := by
  apply WP.of_runBlock
  simp only [keyAddress,runBlock_cons,runStep_some,runBlock_nil,exec,State.read,Size.bits,
    Nat.reduceLT,ite_true,RegUpd.gpr_write,BitVec.setWidth_eq,h11,hs.x3,
    ite_false,reduceCtorEq,address_fact m hm,Option.some.injEq,exists_eq_left']
  refine ⟨BitVec.add_comm _ _,⟨fun r hr => ?_,rfl,rfl⟩,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [RegUpd.gpr_write,hr.1,hr.2.1,hr.2.2,ite_false]

theorem selectKey_ok {s:State} {base:Addr} (hs:Scr s base) {m:Nat}
    (hm:m<16) (h11:s.gpr .x11=BitVec.ofNat 64 m) :
    WP isa (.block selectKey) s fun t =>
      (∀ w<24,word t.mem base (dst w)=tw s.mem base (m/2) w) ∧
      Outside base 832 384 s.mem t.mem ∧ Keeps [.x11,.x8,.x9,.x4] s t := by
  have he:selectKey=keyAddress++copyWords 24 TAB:=rfl
  rw [he,WP.block_append_iff]
  refine WP.mono (keyAddress_ok hs hm h11) fun a ⟨a8,ka,am⟩ => ?_
  have ha:=hs.of_keeps ka (by decide)
  have ho:∀ w<24,off base (192*(m/2))+BitVec.ofNat 64 (TAB+8*w)=
      off base (TAB+192*(m/2)+8*w) := by
    intro w _
    rw [off,off,Offset.add_add]
    exact congrArg (fun n => base+BitVec.ofNat 64 n) (by omega)
  refine WP.mono (copyWords_ok ha a8 (Nat.le_refl 24) (by decide) (by decide)
    (fun w hw => by rw [ho w hw];exact ha.read (by simp only [TAB];omega))
    (fun w hw j hj => by
      rw [ho w hw,VG.Proof.X448.AArch64.ofs_off base (by simp only [TAB];omega)]
      simp only [TAB]
      omega)) fun t ⟨tv,fo,kt⟩ => ?_
  refine ⟨fun w hw => ?_,?_,(ka.mono (by decide)).trans (kt.mono (by decide))⟩
  · rw [tv w hw,ho w hw,am]
    rfl
  · rw [am] at fo
    exact fo

end VG.Proof.Ed448.AArch64.Sparse
end

end

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/KeyOperand.lean`, which only this module imported.
section

/-! The directly indexed odd-key operand preserves bounded field slots. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Proof.X448.AArch64 (Scr limbs word)
open VG.Proof.X448.AArch64.Weak (Index)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd FKeep Same)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Proof.Ed448.AArch64.Window (dst tw TPt)
open VG.Proof.Ed448.WnafWide (oddPoint)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem keyOperand_ok {s:State} {base:Addr} {P:Spec.Ed448.Point}
    (hs:Scr s base) (hb:BEnv s.mem base) (ht:OddTabOk s.mem base P 8)
    (hxb:∀ e<8,∀ w<8,(tw s.mem base e w).toNat<Mb) {m:Nat}
    (hm:m<16) (h11:s.gpr .x11=BitVec.ofNat 64 m) :
    WP isa (.block VG.Impl.Ed448.AArch64.Sparse.selectKey) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ Same base [6,7,8] s.mem t.mem ∧
      Bnd Mb t.mem base (slot 6) ∧ pt (EV t.mem base) 6 7 8=oddPoint P (m/2) ∧
      VG.Proof.X448.AArch64.Keeps [.x11,.x8,.x9,.x4] s t := by
  refine WP.mono (selectKey_ok hs hm h11) fun t ⟨tv,fo,kt⟩ => ?_
  have sm:Same base [6,7,8] s.mem t.mem:=by
    intro i hi j hj
    have n6:i.val≠6:=fun h => hi (by rw [show i=(6:Index) from Fin.ext h];decide)
    have n7:i.val≠7:=fun h => hi (by rw [show i=(7:Index) from Fin.ext h];decide)
    have n8:i.val≠8:=fun h => hi (by rw [show i=(8:Index) from Fin.ext h];decide)
    have hilt:=i.isLt
    exact fo.limbs (by simp only [slot];omega) (by simp only [slot];omega) (by omega)
  have cw:∀ c<3,∀ j<8,word t.mem base (slot (6+c)+8*j)=tw s.mem base (m/2) (8*c+j):=by
    intro c hc j hj
    have hd:dst (8*c+j)=slot (6+c)+8*j:=by simp only [dst,slot];omega
    rw [←hd,tv _ (by omega)]
  have tb:BEnv t.mem base:=by
    intro i j hj
    by_cases hi:i∈[(6:Index),7,8]
    · have he:i.val=6 ∨ i.val=7 ∨ i.val=8:=by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl <;> simp
      have hr:slot i.val=slot (6+(i.val-6)):=by congr 1;omega
      show (word t.mem base (slot i.val+8*j)).toNat<Ib
      rw [hr,cw _ (by omega) j hj]
      exact (ht (m/2) (by omega)).2 _ (by omega)
    · rw [sm i hi j hj]
      exact hb i j hj
  refine ⟨⟨kt.mono (by decide),fun x hx _ => fo x (by omega)⟩,tb,sm,?_,?_,kt⟩
  · intro j hj
    show (word t.mem base (slot 6+8*j)).toNat<Mb
    rw [cw 0 (by decide) j hj]
    simpa only [Nat.mul_zero,Nat.zero_add] using hxb (m/2) (by omega) j hj
  · rw [←(ht (m/2) (by omega)).1]
    symm
    unfold TPt pt
    refine Spec.Ed448.Point.mk.injEq _ _ _ _ _ _ |>.mpr ⟨?_,?_,?_⟩
    · exact Window.FV_entry _ _ _ (e:=m/2) (c:=0) (by omega) (fun j hj => (cw 0 (by decide) j hj).symm)
    · exact Window.FV_entry _ _ _ (e:=m/2) (c:=1) (by omega) (fun j hj => (cw 1 (by decide) j hj).symm)
    · exact Window.FV_entry _ _ _ (e:=m/2) (c:=2) (by omega) (fun j hj => (cw 2 (by decide) j hj).symm)

end VG.Proof.Ed448.AArch64.Sparse
end

end

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Sparse/AddKey.lean`, which only this module imported.
section

/-! One signed odd key addition, skipping the zero digit. -/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (off)
open VG.Proof.X448.AArch64.Base (pt zero_env genPt_eq)
open VG.Proof.Ed448.WnafWide (maybeAdd keyEntry signedPoint)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem addKey_ok {s:State} {base:Addr} {P:Spec.Ed448.Point} (h:Core base s)
    (ht:OddTabOk s.mem base P 8)
    (hxb:∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<VG.Proof.Curve448.AArch64.Fast.Mb)
    {i:Nat} (hi:i<464) (hc:s.gpr .x19=BitVec.ofNat 64 i)
    {d:Int} (hd:-15≤d ∧ d≤15) (hbit:s.mem (off base (BITS+i))=BitVec.ofInt 8 d) :
    WP isa addKey s fun t => Core base t ∧ PointKeep base s t ∧
      pt (EV t.mem base) 3 4 5=maybeAdd d (pt (EV s.mem base) 3 4 5) (keyEntry P d) := by
  unfold addKey
  refine WP.seq (WP.mono (keyDigit_ok h.scr hi hc) fun a ⟨a11,ak,am⟩ => ?_)
  have ka:=PointKeep.of_keeps (base:=base) ak am (by decide)
  have ha:=h.of_keeps ka am
  have hd':-127≤d ∧ d≤127:=by omega
  have az:(a.gpr .x11==0)=decide (d=0):=by rw [a11,hbit];exact encoded_zero hd'
  by_cases h0:d=0
  · have ev:isa.eval (.nonzero .x .x11) a=some false:=by
      simp only [eval,State.read,BitVec.setWidth_eq,bne,az,h0,decide_true,Bool.not_true]
    refine VG.WP.ite false ev (fun z => Bool.noConfusion z) fun _ => WP.block_nil ?_
    refine ⟨ha,ka,?_⟩
    rw [am,maybeAdd,ite_eq_left h0]
  · have ev:isa.eval (.nonzero .x .x11) a=some true:=by
      simp only [eval,State.read,BitVec.setWidth_eq,bne,az,h0,decide_false,Bool.not_false]
    refine VG.WP.ite true ev (fun _ => ?_) (fun z => Bool.noConfusion z)
    rw [WP.seq_iff]
    refine WP.mono (magnitude_ok hd' (by rw [a11,hbit])) fun b ⟨b21,b11,bk,bm⟩ => ?_
    have kb:=PointKeep.of_keeps (base:=base) bk bm (by decide)
    have hb:=ha.of_keeps kb bm
    have htab:OddTabOk b.mem base P 8:=by rw [bm,am];exact ht
    have hxx:∀ e<8,∀ w<8,(Window.tw b.mem base e w).toNat<VG.Proof.Curve448.AArch64.Fast.Mb:=by
      rw [bm,am]
      exact hxb
    rw [WP.seq_iff]
    refine WP.mono (keyOperand_ok hb.scr hb.env htab hxx (by omega) b11)
      fun c ⟨ck,cb,csm,cx,cp,cr⟩ => ?_
    have kc:=PointKeep.of_field ck
    have hcorec:=hb.unchanged kc cb csm (by decide) (by decide) (by decide)
    have c21:c.gpr .x21=BitVec.ofNat 64 (if decide (d<0) then 1 else 0):=by
      rw [cr.1 _ (by decide),b21]
      by_cases hn:d<0 <;> simp only [hn,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false]
    refine WP.seq (WP.mono (negateIf_ok (decide (d<0)) hcorec cx c21)
      fun u ⟨hu,ku,usm,ue⟩ => ?_)
    have up:pt (EV u.mem base) 6 7 8=keyEntry P d:=by
      rw [ue,signedEnv_point,cp,keyEntry,ite_eq_right h0]
    have uq:pt (EV u.mem base) 3 4 5=pt (EV s.mem base) 3 4 5:=by
      rw [acc_of_same usm (by decide) (by decide) (by decide),
        acc_of_same csm (by decide) (by decide) (by decide),bm,am]
    refine WP.mono (Point56.addCall_ok hu.scr hu.env (zero_env hu.zero).2)
      fun t ⟨tk,tb,tsm,_,_,tz,te,_⟩ => ?_
    have kp:=PointKeep.of_call tk
    refine ⟨hu.after kp tb tsm (by decide) (by decide) tz,
      (((ka.trans kb).trans kc).trans ku).trans kp,?_⟩
    rw [te,Point56.genEnv_pt,(zero_env hu.zero).1,genPt_eq,uq,up,maybeAdd,ite_eq_right h0]

end VG.Proof.Ed448.AArch64.Sparse
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Sparse

open VG VG.AArch64
open VG.Impl.Ed448.AArch64.Sparse
open VG.Impl.X448.AArch64 (BITS)
open VG.Proof.X448.AArch64 (Keeps off)
open VG.Proof.X448.AArch64.Base (pt)
open VG.Proof.Ed448.WnafWide (maybeAdd baseEntry keyEntry)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

structure StepKeep (base:Addr) (s t:State) : Prop where
  regs : Keeps (.x19::pointClob) s t
  mem : JointFrame base s.mem t.mem

def roundPoint (P Q:Spec.Ed448.Point) (ds dk:Int) : Spec.Ed448.Point :=
  maybeAdd dk (maybeAdd ds (VG.Proof.Ed448.double Q) (baseEntry ds)) (keyEntry P dk)

theorem jointStep_ok (hA:AffineOk) {s:State} {base:Addr} {P:Spec.Ed448.Point} (h:Core base s)
    (ht:OddTabOk s.mem base P 8)
    (hxb:∀ e<8,∀ w<8,(Window.tw s.mem base e w).toNat<VG.Proof.Curve448.AArch64.Fast.Mb)
    (hbt:BaseTableAt s base (s.syms baseSym)) {i:Nat} (hi:i<464)
    (hc:s.gpr .x19=BitVec.ofNat 64 (i+1)) {ds dk:Int}
    (hds:-127≤ds ∧ ds≤127) (hdk:-15≤dk ∧ dk≤15)
    (hsd:s.mem (off base (SDIG+i))=BitVec.ofInt 8 ds)
    (hkd:s.mem (off base (BITS+i))=BitVec.ofInt 8 dk) :
    WP isa step s fun t => Core base t ∧ StepKeep base s t ∧
      t.gpr .x19=BitVec.ofNat 64 i ∧ t.gpr .x9=BitVec.ofNat 64 i ∧
      pt (EV t.mem base) 3 4 5=roundPoint P (pt (EV s.mem base) 3 4 5) ds dk := by
  unfold step
  refine WP.seq (WP.mono_syms (VG.Proof.X448.AArch64.Weak.decCounter_ok (by omega) hc)
    fun a ⟨a19,ag,am,ar,aw,_⟩ asy => ?_)
  have ak:Keeps [.x19] s a:=⟨fun r hr => ag r (by simpa only [List.mem_singleton] using hr),ar,aw⟩
  have ha:=h.regsOnly ak am (by decide)
  refine WP.seq (WP.mono_syms (Point56.doubleCall_ok ha.scr ha.env ha.zbound)
    fun b ⟨bk,bb,bsm,_,_,bz,be,_⟩ bsy => ?_)
  have kb:=PointKeep.of_call bk
  have hb:=ha.after kb bb bsm (by decide) (by decide) bz
  have b19:b.gpr .x19=BitVec.ofNat 64 i:=(kb.regs.1 _ (by decide)).trans a19
  have btab:BaseTableAt b base (b.syms baseSym):=by
    rw [bsy,asy]
    apply kb.baseTable
    refine ⟨?_,hbt.far,?_⟩
    · rw [ar,aw]
      exact hbt.read
    · rw [am]
      exact hbt.val
  refine WP.seq (WP.mono (addBase_ok hA hb btab hi b19 hds (by rw [kb.baseDigit hi,am];exact hsd))
    fun c ⟨hc',kc,cp⟩ => ?_)
  have kbc:=kb.trans kc
  have ctab:OddTabOk c.mem base P 8:=by
    apply kbc.oddTable
    rw [am]
    exact ht
  have cxb:∀ e<8,∀ w<8,(Window.tw c.mem base e w).toNat<VG.Proof.Curve448.AArch64.Fast.Mb:=by
    apply kbc.xbounds
    rw [am]
    exact hxb
  have c19:c.gpr .x19=BitVec.ofNat 64 i:=(kc.regs.1 _ (by decide)).trans b19
  refine WP.seq (WP.mono (addKey_ok hc' ctab cxb hi c19 hdk
    (by rw [kbc.keyDigit hi,am];exact hkd)) fun d ⟨hd,kd,dp⟩ => ?_)
  have d19:d.gpr .x19=BitVec.ofNat 64 i:=(kd.regs.1 _ (by decide)).trans c19
  refine WP.mono (Window.mov_ok .x9 .x19 d) fun t ⟨t9,tm,tk⟩ => ?_
  have kt:=PointKeep.of_keeps (base:=base) tk tm (by decide)
  have kap:=((kb.trans kc).trans kd).trans kt
  refine ⟨hd.of_keeps kt tm,⟨?_,?_⟩,(tk.1 _ (by decide)).trans d19,t9.trans d19,?_⟩
  · exact (ak.mono (by decide)).trans (kap.regs.mono (by decide))
  · rw [←am]
    exact kap.mem
  · rw [tm,dp,cp,be,Window.dblEnv_345,ha.one,Window.dblPt_eq,am]
    rfl

end VG.Proof.Ed448.AArch64.Sparse
