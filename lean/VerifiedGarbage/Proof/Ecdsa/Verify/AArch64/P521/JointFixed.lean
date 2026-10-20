module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedSource
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDigit
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointFixedEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Digit
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ed25519.AArch64 (read_x)
private theorem byteTest : ∀b : BitVec 8,(b.setWidth 64 != 0)=decide (nafMagnitude b≠0) := by decide +kernel

theorem fixedDigit_using {s₀ s : State} {base T : Addr} {u v j : Nat} {C : Curve} {P G A : Point C}
 (hL : NafLay P521Joint.K 8192)
 (hm : UnitMod C.p (2^(64*P521Joint.K.M.n)))
 (hC : Law C)
 (mixed : ∀ {s : State} {V : List Nat} {E : Nat → Fe C} {A B : Point C},
 Inv P521Joint.K.M base 8192 C.p (·∈winSlots P521Joint.K) V E s →
 (∀x∈rcbR P521Joint.K.S P521Joint.K.R P521Joint.K.E,x∈V) →
 onCurve C A=true → onCurve C B=true →
 InvJ C (E P521Joint.K.R.x) (E P521Joint.K.R.y) (E P521Joint.K.R.z) A →
 InvJ C (E P521Joint.K.E.x) (E P521Joint.K.E.y) (E P521Joint.K.E.z) B →
 E P521Joint.K.E.z=1 →
 WP isa (Jacobian.jacMixedAdd P521Joint.K P521Joint.K.R P521Joint.K.E P521Joint.K.D) s
 (JacPost P521Joint.K.M P521Joint.K.S base 8192 C (·∈winSlots P521Joint.K) V P521Joint.K.D (add A B) s))
 (hG : onCurve C G=true) (hA : onCurve C A=true)
 (hf : NafFixed P521Joint.K C base s₀ P v)
 (h : JointDigitPost P521Joint.K C base 8192 P s₀ s j A)
 (h1 : tmv C P521Joint.K.M.n base s (p521.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<577) (hbytes : s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j) :
 WP isa P521Joint.fixedDigit s fun t =>
 JointDigitPost P521Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 7 u j)) := by
 let K := P521Joint.K
 let V := winRo K ++ [K.R.x,K.R.y,K.R.z]
 have vs : ∀x∈V,x∈winSlots K := by decide
 have vl : ∀x∈V,wordsVal s.mem base x K.M.n<C.p := by
   intro x hx
   rcases List.mem_append.mp hx with hx | hx
   · exact (h.st.ro hL.win hf).1 x hx
   · exact h.rlt x hx
 have hi := h.st.inv vs vl
 rw [P521Joint.fixedDigit]
 apply WP.seq
 refine WP.mono_syms (nafRead_ok (K:=P521Joint.KG) h.st.scr (by decide)
   (by change 3304+j<8192; omega) h.x19 hbytes .x2) fun a ⟨a2,ka⟩ sa => ?_
 have ia := (hi.of_keeps ka (by decide)).to_tmv
 have kpa : ProgKeep K.M base [] s a := keeps_prog ka (by decide)
 have srca := source.keep kpa sa (by simp) hi.mod.tmp
 have na := h.st.regs hL.win ka (by decide) (by decide)
 have ca := CacheUpTo.ofMem ka.mem h.cache
 have a19 := (ka.gpr .x19 (by decide)).trans h.x19
 have ab : a.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j := by rw [ka.mem,hbytes]
 have a1 : tmv C K.M.n base a (p521.sl ONEP)=1 := by unfold tmv; rw [ka.mem]; exact h1
 have az : tmv C K.M.n base a K.zero=0 := by
   unfold tmv
   rw [(na.ro hL.win hf).2,toM_zero]
 refine WP.ite (decide (FastNaf.magnitude 7 u j≠0)) (by
   change some (a.read .x .x2 != 0)=_
   rw [read_x,a2,byteTest]
   have hbmag : nafMagnitude (FastNaf.byte 7 u j)=FastNaf.magnitude 7 u j := FastNaf.byte_magnitude 7 u j
   rw [hbmag]) (fun hn=>?_) (fun hz=>?_)
 · apply WP.seq
   refine WP.mono (fixedEntry_ok hL hm ia (by decide) az a1 srca hj a19 ab a2 (of_decide_eq_true hn))
     fun b ⟨E,kb,ib,jb,zb⟩=>?_
   have rEq : ∀x∈[K.R.x,K.R.y,K.R.z],E x=tmv C K.M.n base a x := by
     intro x hx
     rw [←ib.val x (by apply List.mem_append_right; exact List.mem_append_right _ hx)]
     unfold tmv
     rw [kb.slot hL.win.lay ia.scr (by decide) (vs x (List.mem_append_right _ hx)) (by
       revert x; decide)]
   have ja : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) A := by
     rw [rEq _ (by simp),rEq _ (by simp),rEq _ (by simp)]
     simpa only [tmv,ka.mem] using h.r
   apply WP.seq
   refine WP.mono (mixed ib (by decide) hA (FastNaf.onCurve_point hC hG 7 u j) ja jb zb)
       fun d ⟨Ed,kd,id,jd⟩=>?_
   have copyApart : RcbApart K.S K.D K.D K.R := by
     obtain ⟨_,a2,_,_,_,_,_,_⟩ := rcbApart_naf hL.win
     exact ⟨a2.nodup,fun x hx=>a2.apart x (rcbR_self_mem _ _ _ hx)⟩
   change WP isa (.block (copyPt K.M.n K.R K.D)) d _
   refine WP.mono (copyPointJ_ok hL.win.lay hL.al.al copyApart (by decide) id (by decide) jd)
     fun t ⟨Et,kt,it,jt⟩=>?_
   have kbt : ProgKeep K.M base (winOther K) a t :=
     (kb.mono (by decide)).trans ((kd.mono (by decide)).trans (kt.mono (by decide)))
   have ut : Unch base (loopW K) a.mem t.mem := kbt.unch
   have nt := na.next hL.win it.scr ((⟨kbt.gpr,kbt.rd,kbt.wr,kbt.sp⟩ : KeepRegs (clob K.M.n) a t).mono clob_nafClob) ut
   exact ⟨nt,(kbt.gpr _ (x19_not_clob _)).trans a19,
     fun x hx=>it.lt x (List.mem_append_left _ hx),
     it.point_tmv (fun x hx=>List.mem_append_left _ hx) jt,
     CacheOk.unch hL.win hL.cache ca ut h.st.scr.nowrap⟩
 · have hm0 : FastNaf.magnitude 7 u j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
   have pt : FastNaf.point C G 7 u j=.infinity := by
     rw [FastNaf.point,hm0]
     have h0 : mul 0 G=.infinity := by rw [Spec.Weierstrass.mul]; rfl
     rw [h0]; split <;> rfl
   apply WP.block_nil
   rw [pt,add_infinity]
   exact ⟨na,a19,(by rw [ka.mem]; exact h.rlt),(by simpa only [tmv,ka.mem] using h.r),ca⟩
theorem fixedDigit_ok {s₀ s : State} {base T : Addr} {u v j : Nat} {C : Curve} {P G A : Point C}
 (hL : NafLay P521Joint.K 8192)
 (hm : UnitMod C.p (2^(64*P521Joint.K.M.n)))
 (hC : Law C) (hA3 : AM3 C) (hone : P521Joint.K.one<C.p)
 (hG : onCurve C G=true) (hA : onCurve C A=true)
 (hf : NafFixed P521Joint.K C base s₀ P v)
 (h : JointDigitPost P521Joint.K C base 8192 P s₀ s j A)
 (h1 : tmv C P521Joint.K.M.n base s (p521.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<577) (hbytes : s.mem (off base (P521Joint.KG.bits+j))=FastNaf.byte 7 u j) :
 WP isa P521Joint.fixedDigit s fun t =>
 JointDigitPost P521Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 7 u j)) := by
 apply fixedDigit_using hL hm hC _ hG hA hf h h1 source hj hbytes
 intro t V E A B it iv a b ja jb z
 obtain ⟨_,_,_,_,_,apart,_,_⟩ := rcbApart_naf hL.win
 exact jacMixedAddB_ok hL.win.lay hL.al.al (by decide) hm hC hA3 apart
   (by decide) (hL.al.low (by decide)) it iv hone a b ja jb z

end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
