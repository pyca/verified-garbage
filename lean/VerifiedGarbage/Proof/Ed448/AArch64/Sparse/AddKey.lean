module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.KeyOperand
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Sign
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.DigitLoads
import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Magnitude
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X448.AArch64.Base.AddGen
public import VerifiedGarbage.Impl.Ed448.AArch64.Sparse.Joint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.AArch64.Mem

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
