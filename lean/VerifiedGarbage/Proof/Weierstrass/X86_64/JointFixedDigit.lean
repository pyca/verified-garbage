import VerifiedGarbage.Proof.Weierstrass.X86_64.JointGenerator
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacMixedForward

/-! A fixed-generator digit updates the same accumulator and preserves the external row. -/
namespace VG.Proof.Weierstrass.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 Spec.Weierstrass

local macro "jslots" : tactic => `(tactic| (simp only [jointSlots,jointLive,jointWork,
  nafSlots,cachedSlots,jacCoords,winRo,winOther,rcbW,rcbR,List.mem_append,List.mem_cons,
  List.not_mem_nil,or_false] at * <;> grind))

/-- `R = R + E` for the affine point `E` (`Joint.fixedAdd`). -/
theorem jointFixedAdd_ok {c : Joint.Cfg} {C : Curve} {base : Addr} {size u v : Nat}
    {Q A P : Point C} {External : State → Prop} {E : Nat → Fe C} {s : State}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : c.K.one<C.p) (hA : onCurve C A=true) (hP : onCurve C P=true)
    (hExternal : ∀ s t,ProgKeep c.K.M base (jointWork c) s t → t.syms=s.syms → External s → External t)
    (h : JointCore c C base size Q u v External A s)
    (hI : Inv c.K.M base size C.p (·∈jointSlots c) (jacCoords c.K.E++jointLive c) E s)
    (hJ : InvJ C (E c.K.R.x) (E c.K.R.y) (E c.K.R.z) A)
    (hJE : InvJ C (E c.K.E.x) (E c.K.E.y) (E c.K.E.z) P) (hz : E c.K.E.z=1) :
    WP isa (Joint.fixedAdd c).inline s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧ JointCore c C base size Q u v External (add A P) t := by
  refine jointAdd_dispatch (body := PointOps.addAffineBody c.K) rfl (fun _ => rfl)
    (fun C' hp => (hL.calls.ok C' hp).2.1) (fun C' hp => (hL.calls.ok C' hp).2.2) hExternal ⟨h, hI⟩
    fun b ⟨cb, ib⟩ => ?_
  rw [PointOps.addAffineBody]
  simp only [Code.inline]
  apply WP.seq
  have sl : ∀ x∈rcbW c.K.S c.K.D++rcbR c.K.S c.K.R c.K.E,x∈jointSlots c := by
    intro x hx; jslots
  have vr : ∀ x∈rcbR c.K.S c.K.R c.K.E,x∈jacCoords c.K.E++jointLive c := by
    intro x hx; jslots
  refine WP.mono_syms (jacMixedForward_ok hL.lookup.layout.lay hm hC ha
    hL.addApart sl ib vr hOne hA hP hJ hJE hz)
    fun d ⟨ed,kd,id,jd⟩ sd => ?_
  have wd : ∀ x∈rcbW c.K.S c.K.D,x∈jointWork c := by intro x hx; jslots
  have edExt := hExternal b d (kd.mono wd) sd cb.external
  have rs : ∀ x∈jacCoords c.K.R,x∈jointSlots c := by intro x hx; jslots
  refine WP.mono_syms (copyPointFields_ok hL.lookup.layout.lay hL.accumNodup hL.copyApart rs id
    (fun _ hx => List.mem_append_left _ hx)) fun t ⟨et,kt,it,jt⟩ st => ?_
  have wr : ∀ x∈jacCoords c.K.R,x∈jointWork c := by intro x hx; jslots
  have kt' := kt.mono wr
  have kw := (kd.mono wd).trans kt'
  have ie := it.sub (fun x hx => List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_right _ hx)))
  have jp : InvJ C (et c.K.R.x) (et c.K.R.y) (et c.K.R.z) (add A P) := by
    simp only [Prod.mk.injEq] at jt
    rw [jt.1,jt.2.1,jt.2.2]
    exact jd
  exact ⟨kw,cb.next hL.lookup.layout kw ie jp (hExternal d t kt' st edExt)⟩

theorem jointFixedDigit_ok {c : Joint.Cfg} {C : Curve} {base T : Addr} {size u v j : Nat}
    {G Q A : Point C} {row : JointGeneratorRow c.K.M.n C G} {s : State}
    (hL : JointAddLayout c size) (hm : UnitMod C.p (2^(64*c.K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : c.K.one<C.p)
    (hOneVal : toM C.p (2^(64*c.K.M.n)) c.K.one=1)
    (hG : onCurve C G=true) (hA : onCurve C A=true)
    (h : JointCore c C base size Q u v (JointGenerator c C base T size row) A s)
    (hj : j<64*c.K.M.n+1) (hb : s.gpr .rbx=BitVec.ofNat 64 j) :
    WP isa (Joint.fixedDigit c).inline s fun t =>
      ProgKeep c.K.M base (jointWork c) s t ∧
      JointCore c C base size Q u v (JointGenerator c C base T size row) (add A (FastNaf.point C G 7 u j)) t := by
  have hExternal := JointGenerator.workKeep (base:=base) (row:=row) (T:=T) hL.lookup.layout h.field.mod.tmp
  have hbytes : c.gBits+j<size := by
    have hh := hL.lookup.layout.stableBounds (c.gBits,64*c.K.M.n+1) (by simp [jointStableRanges])
    dsimp only at hh
    omega
  rw [Joint.fixedDigit]
  simp only [Code.inline]
  apply WP.seq
  refine WP.mono_syms (nafRead_ok (K:={c.K with bits:=c.gBits}) h.field.scr hbytes hb (h.stable.generator j hj)) fun a ⟨a8,az,ka⟩ sa => ?_
  have kp : ProgKeep c.K.M base (jointWork c) s a := jointKeeps_prog ka (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    simp [clob,VG.Impl.Mont.X86_64.acc])
  have ca := h.of_keeps ka (by decide) (hExternal s a kp sa h.external)
  refine WP.ite (decide (FastNaf.byte 7 u j=0)) az (fun hz => ?_) (fun hn => ?_)
  · have hz' := (FastNaf.byte_zero_iff 7 u j).mp (of_decide_eq_true hz)
    have ep : FastNaf.point C G 7 u j=Point.infinity := by
      unfold FastNaf.point
      have h0 : mul 0 G=Point.infinity := by rw [Spec.Weierstrass.mul]; rfl
      rw [hz',h0]
      split <;> rfl
    have ea : add A (FastNaf.point C G 7 u j)=A := by rw [ep]; cases A <;> rfl
    rw [ea]
    exact WP.block_nil ⟨kp,ca⟩
  · have hmag : FastNaf.magnitude 7 u j≠0 := fun he =>
      (of_decide_eq_false hn) ((FastNaf.byte_zero_iff 7 u j).mpr he)
    apply WP.seq
    refine WP.mono (jointFixedEntry_core_ok hL.lookup hm hOne hOneVal ca hmag a8)
      fun b ⟨kb,cb,ib,jb,zb⟩ => ?_
    refine WP.mono (jointFixedAdd_ok hL hm hC ha hOne hA (FastNaf.onCurve_point hC hG 7 u j)
      hExternal cb ib cb.point jb zb) fun t ⟨kt,ct⟩ => ⟨(kp.trans kb).trans kt,ct⟩

end VG.Proof.Weierstrass.X86_64
