module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.BaseOperand
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Sign
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.DigitLoads
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Magnitude
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.X448.AArch64.Base.AddEnv
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Recode
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem

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
