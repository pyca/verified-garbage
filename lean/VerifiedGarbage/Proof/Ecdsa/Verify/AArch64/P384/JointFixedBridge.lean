module

public import VerifiedGarbage.Proof.Weierstrass.Joint
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDouble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.State
public import VerifiedGarbage.Proof.Weierstrass.CheckPointContract
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedSource
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointFixedEntry
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointDigit
public import VerifiedGarbage.Proof.Weierstrass.FastNaf
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAddB
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStore
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeArithmetic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead9
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointRead
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.JointFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ

/-! ### `Ecdsa.Verify.AArch64.P384.JointLoop`, which only this module used -/

section

-- Formerly `VerifiedGarbage/Proof/Weierstrass/AArch64/PubNaf/JointDoubleD.lean`, which only this module imported.
section

/-! # The joint loop's shared doubling, by a given doubling

`jointDoubleD_ok`: `jointDouble_ok` with a doubling that does what the field program's does
(`DblSpec`, such as P-384's register-allocated doubling). -/

section
namespace VG.Proof.Weierstrass.AArch64.PubNaf
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Weierstrass.AArch64.PubNaf
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

theorem jointDoubleD_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : NafLay K size)
    (hC : Law C) (hM3 : AM3 C)
    {P : Point C} {s₀ s : State} (hF : NafFixed K C base s₀ P k) {A : Point C} (hA : onCurve C A=true)
    {d : Prog isa} (hd : DblSpec K C base size d K.R K.D (dblVR K)) {j : Nat}
    (hj : j < 64 * K.M.n + 1) (h : JointDigitPost K C base size P s₀ s (j + 1) A) :
    WP isa (.seq (.block [decCounter]) d) s fun t =>
      JointDoublePost K C base size P s₀ t j (Spec.Weierstrass.add A A) := by
  have hW := hL.win
  refine WP.seq (WP.mono (decCounter_ok s (by omega) (by have := hL.n6; omega) h.x19)
    fun s₁ ⟨x₁, k₁⟩ => ?_)
  have S₁ := h.st.regs hW k₁ (fun r hr => nafClob_mem (by
    simp only [List.mem_singleton] at hr; subst hr; simp)) (by decide)
  have t₁ : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₁.mem]
  have V0 : ∀ x ∈ dblVR K, x ∈ winSlots K ∧ wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (R_other K _ (by simp)), by rw [k₁.mem]; exact h.rlt _ (by simp)⟩
    · exact ⟨winOther_mem (R_other K _ (by simp)), by rw [k₁.mem]; exact h.rlt _ (by simp)⟩
    · exact ⟨winOther_mem (R_other K _ (by simp)), by rw [k₁.mem]; exact h.rlt _ (by simp)⟩
    all_goals exact ⟨winRo_slots K _ (by simp [winRo]), (S₁.ro hW hF).1 _ (by simp [winRo])⟩
  have I₁ : Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) (tmv C K.M.n base s₁) s₁ :=
    inv_of S₁.scr S₁.mod (fun x hx => (V0 x hx).1) (fun x hx => (V0 x hx).2)
  have RJ₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y) (tmv C K.M.n base s₁ K.R.z)
      A := by rw [t₁, t₁, t₁]; exact h.r
  refine WP.mono (hd _ s₁ I₁) fun s₂ ⟨k₂, U₂, E₂, I₂, v₂⟩ => ?_
  have dJ := InvJ.dbl' hC hM3 hA RJ₁ (v₂.trans (dblJChoiceN_run (K.M.n == 4) _))
  have S₂ := S₁.next hW I₂.scr (k₂.mono fun _ h => List.mem_cons_of_mem _ (winSaved_combClob h)) U₂
  have x₂ : s₂.gpr .x19 = BitVec.ofNat 64 j := by
    have n19 : Reg.x19 ∉ clob K.M.n ++ winSaved K.M.n := fun h =>
      (List.mem_append.mp h).elim (x19_not_clob _) (not_mem_winSaved (by decide))
    rw [k₂.gpr _ n19, x₁, Nat.add_sub_cancel]
  have Dl : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₂.mem base x K.M.n < C.p :=
    fun x hx => I₂.lt x (List.mem_append_left _ hx)
  have DJ : InvJ C (tmv C K.M.n base s₂ K.D.x) (tmv C K.M.n base s₂ K.D.y) (tmv C K.M.n base s₂ K.D.z)
      (Spec.Weierstrass.add A A) := by
    rw [show tmv C K.M.n base s₂ K.D.x = E₂ K.D.x from I₂.val _ (by simp),
      show tmv C K.M.n base s₂ K.D.y = E₂ K.D.y from I₂.val _ (by simp),
      show tmv C K.M.n base s₂ K.D.z = E₂ K.D.z from I₂.val _ (by simp)]
    exact dJ
  exact ⟨S₂, x₂, Dl, DJ, CacheOk.unch hW hL.cache (CacheUpTo.ofMem k₁.mem h.cache) U₂ S₁.scr.nowrap⟩

end VG.Proof.Weierstrass.AArch64.PubNaf
end

end

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass

/-- Fixed-generator arithmetic is independent of the joint loop's group recurrence. -/
def FixedStep (C : Curve) (base : Addr) (P G : Point C) (s₀ : State) (u : Nat) : Prop :=
 ∀(s : State) (j : Nat) (A : Point C),j<385 → onCurve C A=true →
  s.syms=s₀.syms → JointDigitPost P384Joint.K C base 8192 P s₀ s j A →
  WP isa P384Joint.fixedDigit s fun t=>
   JointDigitPost P384Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 9 u j))

theorem digits_ok {C : Curve} {base : Addr} {P G A : Point C} {s₀ s : State} {u v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true)
 (hA : onCurve C A=true) (hF : NafFixed P384Joint.K C base s₀ P v)
 (fixed : FixedStep C base P G s₀ u) (hj : j<385) (sym : s.syms=s₀.syms)
 (h : JointDoublePost P384Joint.K C base 8192 P s₀ s j A) :
 WP isa P384Joint.digits s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t j
   (add (add A (FastNaf.point C P 5 v j)) (FastNaf.point C G 9 u j)) := by
 rw [P384Joint.digits]
 refine WP.seq (WP.mono_syms (jointDigit_ok hL hp hC hM3 hone hP hA h.st hF h.cache hj h.x19 h.dlt h.d)
  fun a ha sy=>?_) 
 exact fixed a j _ hj (hC.onCurve_add hA (Naf5.onCurve_point hC hP v j)) (sy.trans sym) ha

theorem step_ok {C : Curve} {base : Addr} {P G : Point C} {s₀ s : State} {u v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hF : NafFixed P384Joint.K C base s₀ P v) (fixed : FixedStep C base P G s₀ u)
 (hj : j<384) (sym : s.syms=s₀.syms)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s (j+1) (jointPoint G P u v (j+1) 9)) :
 WP isa P384Joint.step s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t j (jointPoint G P u v j 9) := by
 rw [P384Joint.step]
 apply WP.assoc
 refine WP.seq (WP.mono_syms (jointDoubleD_ok hL hC hM3 hF
  (jointPoint_curve hC hG hP u v (j+1) 9) hD (by change j<385; omega_using [hj]) h) fun a ha sy=>?_)
 refine WP.mono (digits_ok hL hp hC hM3 hone hP
  (hC.onCurve_add (jointPoint_curve hC hG hP u v (j+1) 9) (jointPoint_curve hC hG hP u v (j+1) 9))
  hF fixed (by omega_using [hj]) (sy.trans sym) ha) fun t ht=>?_
 rw [jointPoint_step hC hG hP u v j 9] at ht
 exact ht

/-- The public NAF's iteration with the allocated doubling also works on a joint accumulator. -/
theorem peerStepD_ok {C : Curve} {base : Addr} {P A : Point C} {s₀ s : State} {v j : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hA : onCurve C A=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hF : NafFixed P384Joint.K C base s₀ P v) (hj : j<384)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s (j+1) A) :
 WP isa (PubNaf.stepD P384Joint.K P384Joint.double) s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t j (add (add A A) (Naf5.point C P v j)) := by
 rw [PubNaf.stepD]
 apply WP.assoc
 refine WP.seq (WP.mono (jointDoubleD_ok hL hC hM3 hF hA hD (by change j<385; omega_using [hj]) h) fun a ha=>?_)
 exact jointDigit_ok hL hp hC hM3 hone hP (hC.onCurve_add hA hA) ha.st hF ha.cache
  (by change j<385; omega_using [hj]) ha.x19 ha.dlt ha.d

theorem loop_ok {C : Curve} {base : Addr} {P G : Point C} {s₀ s : State} {u v : Nat}
 (hL : NafLay P384Joint.K 8192) (hp : UnitMod C.p (2^(64*P384Joint.K.M.n))) (hC : Law C)
 (hM3 : AM3 C) (hone : P384Joint.K.one<C.p) (hP : onCurve C P=true) (hG : onCurve C G=true)
 (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
 (hF : NafFixed P384Joint.K C base s₀ P v) (fixed : FixedStep C base P G s₀ u)
 (sym : s.syms=s₀.syms)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s 384 (jointPoint G P u v 384 9)) :
 WP isa (.loop P384Joint.step (.nonzero .x .x19)) s fun t=>
  JointDigitPost P384Joint.K C base 8192 P s₀ t 0 (add (mul u G) (mul v P)) ∧ t.syms=s₀.syms := by
 let I := fun j t=>JointDigitPost P384Joint.K C base 8192 P s₀ t j (jointPoint G P u v j 9) ∧ t.syms=s₀.syms
 apply countLoop_ok (Inv:=I) (n:=384) (by decide)
 · intro j a hj0 hjn hi
   have e : j-1+1=j := by omega_using [hj0]
   refine WP.mono_syms (step_ok (j:=j-1) hL hp hC hM3 hone hP hG hD hF fixed (by omega_using [hjn]) hi.2
    (by rw [e]; exact hi.1)) fun t ht sy=>?_
   exact ⟨⟨ht,sy.trans hi.2⟩,ht.x19⟩
 · intro t ht
   dsimp only [I] at ht
   rw [jointPoint_zero G P u v 9] at ht
   exact ht
 · decide
 · exact ⟨h,sym⟩
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint

end

end

/-! ### `Ecdsa.Verify.AArch64.P384.JointFixed`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Weierstrass.AArch64.PubNaf
open VG.Proof.Ed25519.AArch64 (read_x)

theorem fixedDigit_using {s₀ s : State} {base T : Addr} {u v j : Nat} {C : Curve} {P G A : Point C}
 (hL : NafLay P384Joint.K 8192)
 (hm : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hC : Law C)
 (mixed : ∀ {s : State} {V : List Nat} {E : Nat → Fe C} {A B : Point C},
 Inv P384Joint.K.M base 8192 C.p (·∈winSlots P384Joint.K) V E s →
 (∀x∈rcbR P384Joint.K.S P384Joint.K.R P384Joint.K.E,x∈V) →
 onCurve C A=true → onCurve C B=true →
 InvJ C (E P384Joint.K.R.x) (E P384Joint.K.R.y) (E P384Joint.K.R.z) A →
 InvJ C (E P384Joint.K.E.x) (E P384Joint.K.E.y) (E P384Joint.K.E.z) B →
 E P384Joint.K.E.z=1 →
 WP isa (Jacobian.jacMixedAdd P384Joint.K P384Joint.K.R P384Joint.K.E P384Joint.K.D) s
 (JacPost P384Joint.K.M P384Joint.K.S base 8192 C (·∈winSlots P384Joint.K) V P384Joint.K.D (add A B) s))
 (hG : onCurve C G=true) (hA : onCurve C A=true)
 (hf : NafFixed P384Joint.K C base s₀ P v)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s j A)
 (h1 : tmv C P384Joint.K.M.n base s (p384.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<385) (hbytes : GBytes base u j s) :
 WP isa P384Joint.fixedDigit s fun t =>
 JointDigitPost P384Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 9 u j)) := by
 let K := P384Joint.K
 let V := winRo K ++ [K.R.x,K.R.y,K.R.z]
 have vs : ∀x∈V,x∈winSlots K := by decide
 have vl : ∀x∈V,wordsVal s.mem base x K.M.n<C.p := by
   intro x hx
   rcases List.mem_append.mp hx with hx | hx
   · exact (h.st.ro hL.win hf).1 x hx
   · exact h.rlt x hx
 have hi := h.st.inv vs vl
 rw [P384Joint.fixedDigit]
 apply WP.seq
 refine WP.mono_syms (fixedRead9_ok (c:=P384Joint.cfg) cfg_gw h.st.scr (by decide)
   (by change 3152+2*j+2≤8192; omega_using [hj]) h.x19 hbytes.lo hbytes.hi) fun a ⟨a2,_,a3,ka⟩ sa => ?_
 have ia := (hi.of_keeps ka (by decide)).to_tmv
 have kpa : ProgKeep K.M base [] s a := keeps_prog ka (by decide)
 have srca := source.keep kpa sa (by simp) hi.mod.tmp
 have na := h.st.regs hL.win ka (by decide) (by decide)
 have ca := CacheUpTo.ofMem ka.mem h.cache
 have a19 := (ka.gpr .x19 (by decide)).trans h.x19
 have ab : GBytes base u j a := ⟨by rw [ka.mem]; exact hbytes.lo,by rw [ka.mem]; exact hbytes.hi⟩
 have a1 : tmv C K.M.n base a (p384.sl ONEP)=1 := by unfold tmv; rw [ka.mem]; exact h1
 have az : tmv C K.M.n base a K.zero=0 := by
   unfold tmv
   rw [(na.ro hL.win hf).2,toM_zero]
 refine WP.ite (decide (FastNaf.magnitude 9 u j≠0)) (by
   change some (a.read .x .x2 != 0)=_
   rw [read_x,a2]
   congr 1
   have hz := jointGCell_zero_iff (c:=P384Joint.cfg) (Or.inr rfl) u j
   rw [jointGCell,ite_eq_left cfg_gw,cfg_gw] at hz
   by_cases h0 : FastNaf.magnitude 9 u j=0
   · rw [hz.mpr h0,h0]; rfl
   · rw [bne_iff_ne.mpr (fun he => h0 (hz.mp he)),decide_eq_true h0]) (fun hn=>?_) (fun hz=>?_)
 · apply WP.seq
   refine WP.mono (fixedEntry_ok hL hm ia (by decide) az a1 srca hj a19 ab a2 a3 (of_decide_eq_true hn))
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
   refine WP.mono (mixed ib (by decide) hA (FastNaf.onCurve_point hC hG 9 u j) ja jb zb)
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
 · have hm0 : FastNaf.magnitude 9 u j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
   have pt : FastNaf.point C G 9 u j=.infinity := by
     rw [FastNaf.point,hm0]
     have h0 : mul 0 G=.infinity := by rw [Spec.Weierstrass.mul]; rfl
     rw [h0]; split <;> rfl
   apply WP.block_nil
   rw [pt,add_infinity]
   exact ⟨na,a19,(by rw [ka.mem]; exact h.rlt),(by simpa only [tmv,ka.mem] using h.r),ca⟩
theorem fixedDigit_ok {s₀ s : State} {base T : Addr} {u v j : Nat} {C : Curve} {P G A : Point C}
 (hL : NafLay P384Joint.K 8192)
 (hm : UnitMod C.p (2^(64*P384Joint.K.M.n)))
 (hC : Law C) (hA3 : AM3 C) (hone : P384Joint.K.one<C.p)
 (hG : onCurve C G=true) (hA : onCurve C A=true)
 (hf : NafFixed P384Joint.K C base s₀ P v)
 (h : JointDigitPost P384Joint.K C base 8192 P s₀ s j A)
 (h1 : tmv C P384Joint.K.M.n base s (p384.sl ONEP)=1)
 (source : FixedGenerator C base 8192 G T s)
 (hj : j<385) (hbytes : GBytes base u j s) :
 WP isa P384Joint.fixedDigit s fun t =>
 JointDigitPost P384Joint.K C base 8192 P s₀ t j (add A (FastNaf.point C G 9 u j)) := by
 apply fixedDigit_using hL hm hC _ hG hA hf h h1 source hj hbytes
 intro t V E A B it iv a b ja jb z
 obtain ⟨_,_,_,_,_,apart,_,_⟩ := rcbApart_naf hL.win
 exact jacMixedAddB_ok hL.win.lay hL.al.al (by decide) hm hC hA3 apart
   (by decide) (hL.al.low (by decide)) it iv hone a b ja jb z

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint

end

end


-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/AArch64/P384/JointWindow.lean`, which only this module imported.
section

section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdsa.Verify.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass.AArch64.PubNaf
open Spec.Weierstrass
theorem window_ok {C : Curve} {base : Addr} {u v : Nat} (hL : NafLay P384Joint.K 8192)
    (hp : UnitMod C.p (2 ^ (64 * P384Joint.K.M.n))) (hC : Law C) (hM3 : AM3 C) (hpn : C.p < 2 ^ (64 * P384Joint.K.M.n))
    (hone_lt : P384Joint.K.one < C.p) (hone : toM C.p (2 ^ (64 * P384Joint.K.M.n)) P384Joint.K.one = 1) (hO : PrimeOrder C)
    (hn17 : 17 ≤ C.n) {P G : Point C} (hP : onCurve C P = true) (hG : onCurve C G=true) {s : State} (hs : Scr s base 8192)
    (hM : ModOkA P384Joint.K.M 8192 C.p s.mem base) (hF : NafFixed P384Joint.K C base s P v)
    (hz1 : tmv C P384Joint.K.M.n base s P384Joint.K.P.z = 1) (hv : v < 2 ^ (64 * P384Joint.K.M.n)) (hu : u < 2^(64*P384Joint.K.M.n))
    (hD : DblSpec P384Joint.K C base 8192 P384Joint.double P384Joint.K.R P384Joint.K.D (dblVR P384Joint.K))
    (fixed : ∀t, Unch base (winW P384Joint.K ++ cacheW P384Joint.K) s.mem t.mem → t.rd=s.rd → t.wr=s.wr → t.syms=s.syms → FixedStep C base P G t u) :
    WP isa P384Joint.window s fun t => Scr t base 8192 ∧ KeepRegs (nafClob P384Joint.K.M.n) s t ∧
      Unch base (winW P384Joint.K ++ cacheW P384Joint.K) s.mem t.mem ∧ ModOkA P384Joint.K.M 8192 C.p t.mem base ∧
      (∀ x ∈ [P384Joint.K.R.x, P384Joint.K.R.y, P384Joint.K.R.z], wordsVal t.mem base x P384Joint.K.M.n < C.p) ∧
      Rep C (tmv C P384Joint.K.M.n base t P384Joint.K.R.x) (tmv C P384Joint.K.M.n base t P384Joint.K.R.y) (tmv C P384Joint.K.M.n base t P384Joint.K.R.z)
        (add (mul u G) (mul v P)) := by
  have hn := hs.nowrap
  rw [P384Joint.window]
  refine WP.seq (WP.mono_syms (table_ok hL hp hC hM3 hO hn17 hP hs hM hF hz1) fun s₁ S₁ sy₁ => ?_)
  -- The cache, from which the loop goes on.
  refine WP.seq (WP.mono_syms (cacheTo_ok hL hp S₁.scr S₁.mod S₁.tbl 8 (Nat.le_refl _))
    fun s₂ ⟨sc₂, k₂, U₂, M₂, T₂, C₂⟩ sy₂ => ?_)
  have U₀₂ : Unch base (winW P384Joint.K ++ cacheW P384Joint.K) s.mem s₂.mem := (S₁.unch.trans U₂).mono fun w hw => by
    simp only [List.mem_append] at hw ⊢
    rcases hw with hw | hw | hw
    · exact Or.inl hw
    · exact Or.inr hw
    · exact Or.inl (loopW_sub P384Joint.K w hw)
  have F₂ := hF.rebase hL U₀₂ hn
  have S₂ : NSt P384Joint.K C base 8192 P s₂ s₂ := ⟨sc₂, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, M₂, T₂⟩
  have fixed₂ := fixed s₂ U₀₂ (k₂.rd.trans S₁.keep.rd) (k₂.wr.trans S₁.keep.wr) (sy₂.trans sy₁)
  apply WP.seq
  refine WP.mono_syms (head_ok hL hone_lt F₂ S₂ C₂ hv) fun s₃ ⟨S₃,C₃,x₃,Dl₃,DJ₃⟩ sy₃ => ?_
  have top := jointPoint_topB (B:=64*P384Joint.K.M.n) (u:=u) (v:=v) G P hu hv 9
  change jointPoint G P u v 385 9 = .infinity at top
  have dj : InvJ C (tmv C P384Joint.K.M.n base s₃ P384Joint.K.D.x)
    (tmv C P384Joint.K.M.n base s₃ P384Joint.K.D.y) (tmv C P384Joint.K.M.n base s₃ P384Joint.K.D.z)
    (add (jointPoint G P u v 385 9) (jointPoint G P u v 385 9)) := by
    rw [top]
    have hz := Naf5.residual_zero_top hv
    change Naf5.residual v 385=0 at hz
    change InvJ C _ _ _ (mul (2*Naf5.residual v 385) P) at DJ₃
    rw [hz,Nat.mul_zero,Spec.Weierstrass.mul] at DJ₃
    exact DJ₃
  apply WP.seq
  refine WP.mono_syms (digits_ok hL hp hC hM3 hone_lt hP
    (hC.onCurve_add (jointPoint_curve hC hG hP u v 385 9) (jointPoint_curve hC hG hP u v 385 9))
    F₂ fixed₂ (j:=384) (by decide) sy₃ ⟨S₃,x₃,Dl₃,dj,C₃⟩) fun s₄ I₄ sy₄ => ?_
  rw [jointPoint_step hC hG hP u v 384 9] at I₄
  apply WP.seq
  refine WP.mono (loop_ok hL hp hC hM3 hone_lt hP hG hD F₂ fixed₂ (sy₄.trans sy₃) I₄) fun s₅ ⟨I₅,_⟩=>?_
  refine WP.mono (jointFinish_ok hL hp hC hpn hone_lt hone F₂ I₅.st I₅.rlt I₅.r) fun t ⟨S',l',r'⟩=>?_
  refine ⟨S'.scr,S₁.keep.trans (k₂.trans S'.keep),(U₀₂.trans S'.unch).mono fun w hw=>?_,S'.mod,l',r'⟩
  simp only [List.mem_append] at hw ⊢
  rcases hw with hw | hw
  · exact hw
  · exact Or.inl hw
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
end

end

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
  rw [hu.byte (fun w hw' => by have := hw w hw'; omega_using [hi, this]) (by omega_using [hb, hi])]
  exact bytes i hi
 exact ⟨e _ (by omega_using [hj]),e _ (by omega_using [hj])⟩

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
     omega_using [hj, he]) (by omega_using [hj, hb])]
   exact bytes j hj
 · unfold tmv
   rw [ua.wordsVal (by decide) (by decide)]
   exact hz
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
