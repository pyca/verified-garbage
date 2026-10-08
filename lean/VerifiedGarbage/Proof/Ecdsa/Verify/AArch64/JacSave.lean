import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Timing
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum

/-! The fixed-base comb and saved result preserve the variable-base inputs. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)

structure JacSavePost (c : Cfg) (base : Addr) (g : Reg → BitVec 64) (a b : State) : Prop where
  scr : Scr b base size
  fixed : Fixed c base g b.mem
  px_lt : sv c base b PX<c.C.p
  py_lt : sv c base b PY<c.C.p
  px : tmv c.C c.n base b (c.sl PX)=tmv c.C c.n base a (c.sl PX)
  py : tmv c.C c.n base b (c.sl PY)=tmv c.C c.n base a (c.sl PY)
  onep : tmv c.C c.n base b (c.sl ONEP)=tmv c.C c.n base a (c.sl ONEP)
  v : sv c base b V=sv c base a V
  sp : b.sp=a.sp

/-- Saving `[u]G` leaves the public point and variable scalar unchanged. -/
theorem jacSave_ok {c : Cfg} (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C)
    (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start)
    {s₀ a : State} {g : Reg → BitVec 64} (hM : Mid c s₀ (s₀.gpr .x3) g a)
    (hr : CombReady c s₀ a) :
    WP isa (.seq (Jacobian.jacComb c.combCfg) (.block (VG.Impl.Ecdsa.Verify.AArch64.Cfg.save c))) a
      (JacSavePost c (s₀.gpr .x3) g a) := by
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x,c.mont x<c.C.p := fun _ => Nat.mod_lt _ (by omega)
  have hpR := unitMod_pow_two hc.p_odd (64*c.n)
  have WC := jacComb_ok (tcombLay hc) (combA hc) hC hc.onG (tcombVals hc hC hT) hc.p_lt hn4
    (jacComb_sum_ok (tcombLay hc) (combA hc) hC hc.am3 hpR hn4 (hmont 1)) hr.1 hr.2.1 hr.2.2
  refine WP.seq (WP.mono WC fun b ⟨kb,ub,_,_,_⟩ => ?_)
  have fb := hM.fixed.unch h7 hn fixedOk_tcombW ub
  have sb := hM.scr.of_keepRegs kb (x0_not_tcombClob hc.n10)
  rw [tcombW_eq] at ub
  refine WP.mono (save_ok hc sb) fun d ⟨sd,kd,ud,_,_,_,_,_,_⟩ => ?_
  have fd := fb.unch h7 hn (fixedOk_slW (by decide)) ud
  have subb : ∀ i∈[RX,RY,RZ,TX,TY,TZ,PT,T0,T1,T2,T3,T4,T5,DX,DY,DZ,TMP],i∈ptsW := by decide
  have subd : ∀ i∈saveW,i∈ptsW := by decide
  have eqv : ∀ {i},i<45 → i∉ptsW → sv c (s₀.gpr .x3) d i=sv c (s₀.gpr .x3) a i := fun hi hl =>
    (sv_unch ud h7 hn hi (apart_slW (fun h => hl (subd _ h)))).trans
      (sv_unch ub h7 hn hi (apart_append (apart_slW (fun h => hl (subb _ h))) (apart_zw hi)))
  have eqf : ∀ {i},i<45 → i∉ptsW →
      tmv c.C c.n (s₀.gpr .x3) d (c.sl i)=tmv c.C c.n (s₀.gpr .x3) a (c.sl i) := by
    intro i hi hl
    change toM _ _ (sv c _ d i)=toM _ _ (sv c _ a i)
    rw [eqv hi hl]
  exact ⟨sd,fd,by rw [eqv (by decide) (by decide)]; exact hM.px_lt,
    by rw [eqv (by decide) (by decide)]; exact hM.py_lt,
    eqf (by decide) (by decide),eqf (by decide) (by decide),eqf (by decide) (by decide),
    eqv (by decide) (by decide),kd.sp.trans kb.sp⟩

end VG.Proof.Ecdsa.Verify.AArch64
