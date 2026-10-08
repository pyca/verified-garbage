import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.CachedJacAdd

/-! A public peer digit either leaves the accumulator alone or adds its cached odd multiple. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
  List.not_mem_nil,or_false] at * <;> grind))

structure JointAddLayout (c : Joint.Cfg) (size : Nat) : Prop where
  lookup : JointLookupLayout c size
  addApart : RcbApart c.K.S c.K.R c.K.E c.K.D
  cache2Apart : c.selected∉rcbW c.K.S c.K.D
  cache3Apart : c.selected+8*c.K.M.n∉rcbW c.K.S c.K.D
  accumNodup : (jacCoords c.K.R).Nodup
  copyApart : ∀ x∈jacCoords c.K.D,∀ y∈jacCoords c.K.R,x≠y

theorem jointCachedDigit_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v j : Nat}
    {Q A : Point C} {External : State → Prop} {s : State}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : c.K.one<C.p)
    (hQ : onCurve C Q=true) (hA : onCurve C A=true)
    (h : JointCore c C base size Q u v External A s)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (hj : j<64*c.K.M.n+1) (hb : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (Joint.cachedDigit c).inline s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v External (add A (FastNaf.point C Q 5 v j)) t := by
  have hbytes : c.K.bits+j<size := by
    have hh := hL.lookup.layout.stableBounds (c.K.bits,64*c.K.M.n+1) (by simp [jointStableRanges])
    dsimp only at hh
    omega
  rw [Joint.cachedDigit]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono_syms (nafRead_ok h.field.scr hbytes hb (h.stable.peer j hj)) fun a ⟨a8,az,ka⟩ sa => ?_
  have kp : ProgKeep c.K.M base (jointWork c) s a := jointKeeps_prog ka (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    simp [clob,VG.Impl.Mont.X86_64.acc])
  have ca := h.of_keeps ka (by decide) (hExternal s a kp sa h.external)
  refine WP.ite (decide (FastNaf.byte 5 v j=0)) az (fun hz => ?_) (fun hn => ?_)
  · have hz' := (FastNaf.byte_zero_iff 5 v j).mp (of_decide_eq_true hz)
    have ep : FastNaf.point C Q 5 v j=Point.infinity := by
      unfold FastNaf.point
      have h0 : mul 0 Q=Point.infinity := by rw [Spec.Weierstrass.mul]; rfl
      rw [hz',h0]
      split <;> rfl
    have ea : add A (FastNaf.point C Q 5 v j)=A := by rw [ep]; cases A <;> rfl
    rw [ea]
    exact WP.block_nil ⟨kp,ca⟩
  · have hmag : FastNaf.magnitude 5 v j≠0 := fun he =>
      (of_decide_eq_false hn) ((FastNaf.byte_zero_iff 5 v j).mpr he)
    apply WP.seq
    refine WP.mono (jointCachedEntry_ok hL.lookup hm ca hExternal hmag a8)
      fun b ⟨kb,cb,ib,jb⟩ => ?_
    apply WP.seq
    have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by
      intro x hx; jslots
    have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈cachedSlots c.K.M.n c.K.E c.selected++jointLive c := by
      intro x hx; jslots
    refine WP.mono_syms (cachedJacAdd_ok hL.lookup.layout.lay hm hC ha
      hL.addApart hL.cache2Apart hL.cache3Apart (by constructor <;> simp [jointSlots])
      sl ib vr (by constructor <;> simp [cachedSlots]) jb.2.1 jb.2.2 hOne hA
      (FastNaf.onCurve_point hC hQ 5 v j) cb.point jb.1) fun d ⟨ed,kd,id,jd⟩ sd => ?_
    have wd : ∀ x∈rcbW c.K.S c.K.D,x∈jointWork c := by intro x hx; jslots
    have edExt := hExternal b d (kd.mono wd) sd cb.external
    have rs : ∀ x∈jacCoords c.K.R,x∈jointSlots c := by intro x hx; jslots
    refine WP.mono_syms (copyPointFields_ok hL.lookup.layout.lay hL.accumNodup hL.copyApart rs id
      (fun _ hx => List.mem_append_left _ hx)) fun t ⟨et,kt,it,jt⟩ st => ?_
    have wr : ∀ x∈jacCoords c.K.R,x∈jointWork c := by intro x hx; jslots
    have kt' := kt.mono wr
    have kw := (kp.trans kb).trans ((kd.mono wd).trans kt')
    have ie := it.sub (fun x hx => List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_right _ hx)))
    have jp : InvJ C (et c.K.R.x) (et c.K.R.y) (et c.K.R.z) (add A (FastNaf.point C Q 5 v j)) := by
      simp only [Prod.mk.injEq] at jt
      rw [jt.1,jt.2.1,jt.2.2]
      exact jd
    exact ⟨kw,h.next hL.lookup.layout kw ie jp (hExternal d t kt' st edExt)⟩

end VG.Proof.Weierstrass.X86_64
