module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLoop
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSource
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointWindow
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixed
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointLayout
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

theorem fixedStep_of_source {C : Curve} {base T : Addr} {P G : Point C} {s₀ : State} {u v : Nat}
 (hL : NafLay P521Joint.K 8192) (hp : UnitMod C.p (2^(64*P521Joint.K.M.n)))
 (hC : Law C) (hM3 : AM3 C) (hone : P521Joint.K.one<C.p) (hG : onCurve C G=true)
 (hF : NafFixed P521Joint.K C base s₀ P v)
 (source : FixedGenerator C base 8192 G T s₀)
 (bytes : ∀j<577,s₀.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j)
 (one : tmv C P521Joint.K.M.n base s₀ (p521.sl ONEP)=1) :
 FixedStep C base P G s₀ u := by
 intro s j A hj hA sy h
 have src := source.unch h.st.unch (by decide) h.st.keep.rd h.st.keep.wr sy
 have gb : s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j := by
  rw [h.st.unch.byte (by
    intro w hw
    have ha:=generator_apart w (List.mem_append_left _ hw)
    omega) (by change 3304+j<2^64; omega)]
  exact bytes j hj
 have ho : tmv C P521Joint.K.M.n base s (p521.sl ONEP)=1 := by
  unfold tmv
  rw [h.st.unch.wordsVal (by decide) (by decide)]
  exact one
 exact fixedDigit_ok hL hp hC hM3 hone hG hA hF h ho src hj gb

/-- The concrete fixed generator discharges the loop's arithmetic callback. -/
theorem window_source_ok {C : Curve} {base T : Addr} {u v : Nat} (hL : NafLay P521Joint.K 8192)
 (hp : UnitMod C.p (2^(64*P521Joint.K.M.n))) (hC : Law C) (hM3 : AM3 C)
 (hpn : C.p<2^(64*P521Joint.K.M.n)) (hone : P521Joint.K.one<C.p)
 (h1 : toM C.p (2^(64*P521Joint.K.M.n)) P521Joint.K.one=1) (hO : PrimeOrder C) (hn : 17≤C.n)
 {P G : Point C} (hP : onCurve C P=true) (hG : onCurve C G=true) {s : State}
 (hs : Scr s base 8192) (hm : ModOkA P521Joint.K.M 8192 C.p s.mem base)
 (hf : NafFixed P521Joint.K C base s P v) (hz : tmv C P521Joint.K.M.n base s P521Joint.K.P.z=1)
 (hv : v<2^(64*P521Joint.K.M.n)) (hu : u<2^(64*P521Joint.K.M.n))
 (source : FixedGenerator C base 8192 G T s)
 (bytes : ∀j<577,s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j) :
 WP isa P521Joint.window s fun t=>Scr t base 8192 ∧ KeepRegs (nafClob P521Joint.K.M.n) s t ∧
  Unch base (winW P521Joint.K++cacheW P521Joint.K) s.mem t.mem ∧ ModOkA P521Joint.K.M 8192 C.p t.mem base ∧
  (∀x∈[P521Joint.K.R.x,P521Joint.K.R.y,P521Joint.K.R.z],wordsVal t.mem base x P521Joint.K.M.n<C.p) ∧
  Rep C (tmv C P521Joint.K.M.n base t P521Joint.K.R.x) (tmv C P521Joint.K.M.n base t P521Joint.K.R.y)
   (tmv C P521Joint.K.M.n base t P521Joint.K.R.z) (add (mul u G) (mul v P)) := by
 refine window_ok hL hp hC hM3 hpn hone h1 hO hn hP hG hs hm hf hz hv hu ?_
 intro a ua rd wr sy
 have ha := hf.rebase hL ua hs.nowrap
 have src := source.unch ua (by decide) rd wr sy
 apply fixedStep_of_source hL hp hC hM3 hone hG ha src
 · intro j hj
   rw [ua.byte (by
     intro w hw
     have he := generator_apart w hw
     omega) (by change 3304+j<2^64; omega)]
   exact bytes j hj
 · unfold tmv
   rw [ua.wordsVal (by decide) (by decide)]
   exact hz
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
