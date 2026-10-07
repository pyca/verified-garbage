import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixed

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

private theorem jointByteTest : ∀ b : BitVec 8,
    (b.setWidth 64 != 0)=decide (nafMagnitude b≠0) := by decide +kernel

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  jacWinSlots,nafLive,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind))

theorem jointFixedDigit_ok (certs : Forward.Arithmetic.Cases)
    {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {s : State} (hL : JointFixedLayout c size)
    (hm : UnitMod C.p (2^(64*c.K.M.n))) (hsize : 8192≤size)
    (hC : Law C) (ha : AM3 C) (hOne : c.K.one<C.p)
    (hG : onCurve C G=true) (hA : onCurve C A=true)
    (h : JointCore c C base size Q u v (JointGenerator c C base size G T) A s)
    (hj : j<257) (h19 : s.gpr .x19=BitVec.ofNat 64 j) :
    WP isa (Joint.fixedDigit c (Joint.mixedAdd c.K c.K.R c.K.E c.K.D)) s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
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
    apply WP.seq
    have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by
      intro x hx; jslots
    have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈[c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c := by
      intro x hx; jslots
    refine WP.mono_syms (jointMixedAdd_ok certs hL.layout.lay hL.layout.aligned hm hsize hC ha hL.addApart sl
      ib vr hOne hA (FastNaf.onCurve_point hC hG 7 u j) cb.point jb zb)
      fun d ⟨Ed,kd,id,jd⟩ sd => ?_
    have wd : ∀ x∈rcbW c.K.S c.K.D,x∈jointWork c := by intro x hx; jslots
    have slcopy : ∀ x∈rcbW c.K.S c.K.R++rcbR c.K.S c.K.D c.K.D,x∈jointSlots c := by
      intro x hx; jslots
    have vcopy : ∀ x∈rcbR c.K.S c.K.D c.K.D,x∈[c.K.D.x,c.K.D.y,c.K.D.z]++([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c) := by
      intro x hx; jslots
    rw [←hL.layout.n]
    refine WP.mono_syms (copyPoint_ok hL.layout.lay hL.layout.aligned hL.copyApart slcopy id vcopy)
      fun t ⟨Et,kt,it,eq⟩ st => ?_
    have wt : ∀ x∈rcbW c.K.S c.K.R,x∈jointWork c := by intro x hx; jslots
    have kdt := (kd.mono wd).trans (kt.mono wt)
    have et := cb.external.keep kdt (st.trans sd) workBound cb.field.mod.tmp
    have jt : InvJ C (Et c.K.R.x) (Et c.K.R.y) (Et c.K.R.z)
        (add A (FastNaf.point C G 7 u j)) := by
      simp only [Prod.mk.injEq] at eq
      rw [eq.1,eq.2.1,eq.2.2]; exact jd
    have live : ∀ x∈jointLive c,x∈[c.K.R.x,c.K.R.y,c.K.R.z]++
        ([c.K.D.x,c.K.D.y,c.K.D.z]++([c.K.E.x,c.K.E.y,c.K.E.z]++jointLive c)) := by
      intro x hx; simp [hx]
    exact ⟨kp.trans (kb.trans kdt),cb.next hL.layout kdt (it.sub live) jt et⟩
  · have hm0 : FastNaf.magnitude 7 u j=0 := by simpa only [ne_eq,not_not] using of_decide_eq_false hz
    have hp : FastNaf.point C G 7 u j=.infinity := by
      rw [FastNaf.point,hm0]
      have h0 : mul 0 G=.infinity := by rw [Spec.Weierstrass.mul]; rfl
      rw [h0]; split <;> rfl
    apply WP.block_nil
    rw [hp,add_infinity]
    exact ⟨kp,ca⟩

end VG.Proof.Weierstrass.AArch64
