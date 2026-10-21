module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointLoop
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedSource
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointWindow
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixed
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

/-- The generator's digits miss the window method's slots and the cache. -/
theorem generator_apart : ∀w∈winW P384Joint.K ++ PubNaf.cacheW P384Joint.K,
 P384Joint.KG.bits+770≤w.1 ∨ w.1+w.2≤P384Joint.KG.bits := by decide

theorem GBytes.of_unch {base : Addr} {u j : Nat} {s t : State} {W : List (Nat×Nat)}
 (hu : Unch base W s.mem t.mem)
 (hw : ∀w∈W,P384Joint.KG.bits+770≤w.1 ∨ w.1+w.2≤P384Joint.KG.bits)
 (bytes : ∀i<770,s.mem (off base (P384Joint.KG.bits+i))=FastNaf.wbyte u i) (hj : j<385) :
 GBytes base u j t := by
 have hb : P384Joint.KG.bits=3152 := rfl
 have e : ∀i<770,t.mem (off base (P384Joint.KG.bits+i))=FastNaf.wbyte u i := fun i hi => by
  rw [hu.byte (fun w hw' => by have := hw w hw'; omega) (by omega)]
  exact bytes i hi
 exact ⟨e _ (by omega),e _ (by omega)⟩

theorem fixedStep_of_source {C : Curve} {base T : Addr} {P G : Point C} {s₀ : State} {u v : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hC : Law C) (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hG : onCurve C G=true)
 (hF : NafFixed P384Joint.K C base s₀ P v)
 (source : FixedGenerator C base 8192 G T s₀)
 (bytes : ∀j<770,s₀.mem (off base (P384Joint.KG.bits+j))=FastNaf.wbyte u j)
 (one : tmv C P384Joint.K.M.n base s₀ (p384.sl ONEP)=1) :
 FixedStep C base P G s₀ u := by
 intro s j A hj hA sy h
 have src := source.unch h.st.unch (by decide) h.st.keep.rd h.st.keep.wr sy
 have gb : GBytes base u j s :=
  GBytes.of_unch h.st.unch (fun w hw => generator_apart w (List.mem_append_left _ hw)) bytes hj
 have ho : tmv C P384Joint.K.M.n base s (p384.sl ONEP)=1 := by
  unfold tmv
  rw [h.st.unch.wordsVal (by decide) (by decide)]
  exact one
 exact fixedDigit_ok hL hp hC hM3 hone hG hA hF h ho src hj gb

/-- The concrete fixed generator discharges the loop's arithmetic callback. -/
theorem window_source_ok {C : Curve} {base T : Addr} {u v : Nat} (hL : NafLay P384Joint.K 8192)
 (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C) (hM3 : AM3 C)
 (hpn : C.p<2^(64*P384Joint.K.M.n)) (hone : P384Joint.K.one<C.p)
 (h1 : toM C.p (2^(64*P384Joint.K.M.n)) P384Joint.K.one=1) (hO : PrimeOrder C) (hn : 17≤C.n)
 {P G : Point C} (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K)) {s : State}
 (hs : Scr s base 8192) (hm : ModOkA P384Joint.K.M 8192 C.p s.mem base)
 (hf : NafFixed P384Joint.K C base s P v) (hz : tmv C P384Joint.K.M.n base s P384Joint.K.P.z=1)
 (hv : v<2^(64*P384Joint.K.M.n)) (hu : u<2^(64*P384Joint.K.M.n))
 (source : FixedGenerator C base 8192 G T s)
 (bytes : ∀j<770,s.mem (off base (P384Joint.KG.bits+j))=FastNaf.wbyte u j) :
 WP isa P384Joint.window s fun t=>Scr t base 8192 ∧ KeepRegs (nafClob P384Joint.K.M.n) s t ∧
  Unch base (winW P384Joint.K++cacheW P384Joint.K) s.mem t.mem ∧ ModOkA P384Joint.K.M 8192 C.p t.mem base ∧
  (∀x∈[P384Joint.K.R.x,P384Joint.K.R.y,P384Joint.K.R.z],wordsVal t.mem base x P384Joint.K.M.n<C.p) ∧
  Rep C (tmv C P384Joint.K.M.n base t P384Joint.K.R.x) (tmv C P384Joint.K.M.n base t P384Joint.K.R.y)
   (tmv C P384Joint.K.M.n base t P384Joint.K.R.z) (add (mul u G) (mul v P)) := by
 refine window_ok hL hp hC hM3 hpn hone h1 hO hn hP hG hs hm hf hz hv hu hD ?_
 intro a ua rd wr sy
 have ha := hf.rebase hL ua hs.nowrap
 have src := source.unch ua (by decide) rd wr sy
 apply fixedStep_of_source hL hp hC hM3 hone hG ha src
 · intro j hj
   have hb : P384Joint.KG.bits=3152 := rfl
   rw [ua.byte (by
     intro w hw
     have he := generator_apart w hw
     omega) (by omega)]
   exact bytes j hj
 · unfold tmv
   rw [ua.wordsVal (by decide) (by decide)]
   exact hz
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
