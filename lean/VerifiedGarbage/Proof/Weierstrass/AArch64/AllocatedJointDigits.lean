import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedFrame
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigit

/-! Digit selection remains unchanged while point arithmetic uses a wider frame.
The callbacks include the final coordinate copy, so no intermediate scratch
or register agreement is imposed beyond what the next point operation reads.
-/
namespace VG.Proof.Weierstrass.AArch64.CachedField
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

private theorem byteTest : ∀ b : BitVec 8,(b.setWidth 64 != 0)=decide (nafMagnitude b≠0) := by decide +kernel

theorem allocatedCachedDigit_ok {C : Curve} {base : Addr} {size u v j : Nat}
    (hL : JointLayout cfg size) (hsize : 8192≤size)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C)
    {rs : List Reg} {W : List (Nat × Nat)} {code : CachedJac.Ops}
    (hregs : ∀ r∈clob K.M.n,r∈rs)
    (hcover : ∀ w∈(jointWork cfg).map (·,8*K.M.n)++[(K.M.tmp,8*K.M.n)],
      ∃ w'∈W,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2)
    (hj : j<257) {Q A : Point C} (hQ : onCurve C Q=true) (hA : onCurve C A=true)
    {External : State → Prop} (hExt : ExternalFrame base External) {s : State}
    (hsum : ∀ {A B : Point C} {s : State},onCurve C A=true → onCurve C B=true →
      JointCore cfg C base size Q u v External A s →
      Inv K.M base size C.p (·∈jointSlots cfg) (entryLive (jointLive cfg)) (tmv C K.M.n base s) s →
      InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) B →
      tmv C K.M.n base s 5400=tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z →
      tmv C K.M.n base s 5432=tmv C K.M.n base s K.E.z*(tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z) →
      WP isa (.seq (CachedJac.add K code) (.block (copyPt 4 K.R K.D))) s fun t =>
        AllocatedFrame rs base W s t ∧ JointCore cfg C base size Q u v External (add A B) t)
    (h : JointCore cfg C base size Q u v External A s) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (CachedJac.digit K code) s fun t =>
      AllocatedFrame rs base W s t ∧
      JointCore cfg C base size Q u v External (add A (FastNaf.point C Q 5 v j)) t := by
  rw [CachedJac.digit]
  apply WP.seq
  refine WP.mono_syms (nafRead_ok h.field.scr (by decide) (by change 1824+j<size; omega) h19
    (h.stable.peer.bits j hj) .x2) fun b ⟨b2,kb⟩ sy => ?_
  have kp : ProgKeep K.M base (jointWork cfg) s b := keeps_prog kb (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob])
  have cb := h.of_keeps kb (by decide) (hExt kp sy h.external)
  have b19 : b.gpr .x19=BitVec.ofNat 64 j := (kb.gpr _ (by decide)).trans h19
  refine WP.ite (decide (FastNaf.magnitude 5 v j≠0)) (by
    change some (b.read .x .x2 != 0)=_
    rw [read_x,b2,byteTest,magnitude_byte]) (fun hn => ?_) (fun hz => ?_)
  · have hm0 : FastNaf.magnitude 5 v j≠0 := of_decide_eq_true hn
    apply WP.seq
    refine WP.mono (entry_core_ok hL (by omega) hm hj
      (by rw [magnitude_byte]; omega)
      (by rw [magnitude_byte]; exact FastNaf.magnitude_le (Or.inl rfl) v j)
      (by rw [magnitude_byte]; exact (FastNaf.magnitude_odd_or_zero 5 v j).resolve_left hm0)
      hExt cb b19 b2) fun d ⟨⟨kd,id,jd,d2,d3⟩,cd⟩ => ?_
    exact WP.mono (hsum hA (FastNaf.onCurve_point hC hQ 5 v j) cd id jd d2 d3)
      fun t ⟨kt,ct⟩ => ⟨(AllocatedFrame.of_prog (kp.trans (kd.mono entry_work)) hregs hcover).trans kt,ct⟩
  · have hm0 : FastNaf.magnitude 5 v j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
    have hp : FastNaf.point C Q 5 v j=.infinity := by
      unfold FastNaf.point
      rw [hm0,Spec.Weierstrass.mul]
      cases FastNaf.negative 5 v j <;> rfl
    have he : add A (FastNaf.point C Q 5 v j)=A := by rw [hp]; cases A <;> rfl
    apply WP.block_nil
    exact ⟨AllocatedFrame.of_prog kp hregs hcover,he.symm ▸ cb⟩

end VG.Proof.Weierstrass.AArch64.CachedField

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

private theorem jointByteTest : ∀ b : BitVec 8,
    (b.setWidth 64 != 0)=decide (nafMagnitude b≠0) := by decide +kernel

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  jacWinSlots,nafLive,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind))

theorem allocatedJointFixedDigit_ok
    {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {s : State} (hL : JointFixedLayout c size)
    (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C)
    {rs : List Reg} {W : List (Nat × Nat)} {mixed : Prog isa}
    (hregs : ∀ r∈clob c.K.M.n,r∈rs)
    (hcover : ∀ w∈(jointWork c).map (·,8*c.K.M.n)++[(c.K.M.tmp,8*c.K.M.n)],
      ∃ w'∈W,w'.1≤w.1 ∧ w.1+w.2≤w'.1+w'.2)
    (hG : onCurve C G=true) (hA : onCurve C A=true)
    (hsum : ∀ {A B : Point C} {s : State},onCurve C A=true → onCurve C B=true →
      JointCore c C base size Q u v (JointGenerator c C base size G T) A s →
      Inv c.K.M base size C.p (·∈jointSlots c) ([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c)
        (tmv C c.K.M.n base s) s →
      InvJ C (tmv C c.K.M.n base s c.K.E.x) (tmv C c.K.M.n base s c.K.E.y)
        (tmv C c.K.M.n base s c.K.E.z) B → tmv C c.K.M.n base s c.K.E.z=1 →
      WP isa (.seq mixed (.block (copyPt 4 c.K.R c.K.D))) s fun t =>
        AllocatedFrame rs base W s t ∧
        JointCore c C base size Q u v (JointGenerator c C base size G T) (add A B) t)
    (h : JointCore c C base size Q u v (JointGenerator c C base size G T) A s)
    (hj : j<257) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (Joint.fixedDigit c mixed) s fun t =>
      AllocatedFrame rs base W s t ∧
      JointCore c C base size Q u v (JointGenerator c C base size G T)
        (add A (FastNaf.point C G 7 u j)) t := by
  have hbytes : c.gBits+j<size := by
    have := hL.layout.stableBounds (c.gBits,257) (by simp [jointStableRanges]); dsimp only at this; omega
  have wsl : ∀ x∈jointWork c,x∈jointSlots c := by intro x hx; jslots
  have workBound : ∀ x∈jointWork c,x+8*c.K.M.n≤size := fun x hx => hL.layout.lay.le x (wsl x hx)
  rw [Joint.fixedDigit]
  apply WP.seq
  refine WP.mono_syms (nafRead_ok (K:=c.G) h.field.scr hL.gBits hbytes h19 (h.stable.generator j hj) .x2)
    fun a ⟨a2,ka⟩ sa => ?_
  have kp : ProgKeep c.K.M base (jointWork c) s a := keeps_prog ka (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob])
  have ea := h.external.keep kp sa workBound h.field.mod.tmp
  have ca := h.of_keeps ka (by decide) ea
  have a19 := (ka.gpr .x19 (by decide)).trans h19
  refine WP.ite (decide (FastNaf.magnitude 7 u j≠0)) (by
    change some (a.read .x .x2 != 0)=_
    rw [read_x,a2,jointByteTest]
    exact congrArg some (congrArg (fun n => decide (n≠0)) (FastNaf.byte_magnitude 7 u j)))
    (fun hn => ?_) (fun hz => ?_)
  · apply WP.seq
    refine WP.mono (jointEntry_generator_ok hL hm ca hj a2 a19 (of_decide_eq_true hn))
      fun b ⟨kb,cb,ib,jb,zb⟩ => ?_
    exact WP.mono (hsum hA (FastNaf.onCurve_point hC hG 7 u j) cb ib jb zb)
      fun t ⟨kt,ct⟩ => ⟨(AllocatedFrame.of_prog (kp.trans kb) hregs hcover).trans kt,ct⟩
  · have hm0 : FastNaf.magnitude 7 u j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
    have hp : FastNaf.point C G 7 u j=.infinity := by
      rw [FastNaf.point,hm0]
      have h0 : mul 0 G=.infinity := by rw [Spec.Weierstrass.mul]; rfl
      rw [h0]; split <;> rfl
    apply WP.block_nil
    rw [hp,add_infinity]
    exact ⟨AllocatedFrame.of_prog kp hregs hcover,ca⟩

end VG.Proof.Weierstrass.AArch64
