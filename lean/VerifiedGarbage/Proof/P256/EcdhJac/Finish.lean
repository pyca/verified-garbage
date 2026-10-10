import VerifiedGarbage.Proof.P256.EcdhJac.Frame
import VerifiedGarbage.Proof.P256.EcdhJac.Extra
import VerifiedGarbage.Proof.P256.EcdhJac.OutCertificate
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJOut

/-! ## `WindowPost` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

/-- The window computation writes only its declared work areas. Its output
is the existing project's homogeneous point representation. Invalid scalars
need no multiplication identity because the public API rejects them. -/
structure WindowPost (base : Addr) (P : Point C) (k : Nat) (s t : State) : Prop where
  frame : Frame base buildWork s t
  field : Inv M base 8192 C.p Sl live (tmv C 4 base t) t
  point : 1≤k → k<C.n → Rep C (tmv C 4 base t K.R.x)
    (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) (mul k P)

end VG.Proof.P256.EcdhJac

end

/-! ## `Wrapped` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

def wrappedWrites : List (Nat×Nat) := buildWork++[(7800,40)]
def wrappedRegs : List Reg := regs.filter fun r=>r∉extraRegs

structure WrappedPost (base : Addr) (P : Point C) (k : Nat) (s t : State) : Prop where
  frame : AllocatedFrame wrappedRegs base wrappedWrites s t
  field : Inv M base 8192 C.p Sl live (tmv C 4 base t) t
  point : 1≤k → k<C.n → Rep C (tmv C 4 base t K.R.x)
    (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) (mul k P)
  restored : ∀ r∈extraRegs,t.gpr r=s.gpr r

theorem wrapped_ok {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hf : Fixed base P k s)
    (hwin : ∀ u,Fixed base P k u → WP isa Impl.P256.EcdhJac.window u (WindowPost base P k u)) :
    WP isa Impl.P256.EcdhJac.wrappedWindow s (WrappedPost base P k s) := by
  unfold Impl.P256.EcdhJac.wrappedWindow
  refine WP.seq (WP.mono (saveExtra_ok hf.field.scr (by decide)) fun a ⟨ka,oa,sa⟩=>?_)
  have fa : AllocatedFrame [] base [(7800,40)] s a := ⟨ka,oa.unch⟩
  refine WP.seq (WP.mono (hwin a (hf.keep_save fa)) fun b hb=>?_)
  have sb := savedExtra_keep sa hb.frame.unch (by decide)
  refine WP.mono (restoreExtra_ok hb.field.scr (by decide) sb) fun t ⟨kt,rt⟩=>?_
  have hu : Unch base wrappedWrites s.mem b.mem := (oa.unch.trans hb.frame.unch).mono (by decide)
  refine ⟨⟨restoreExtra_frame ka hb.frame.regs kt rt,fun x hx=>
    (congrFun kt.mem x).trans (hu x hx)⟩,
    (hb.field.of_keeps kt (by decide)).to_tmv,?_,rt⟩
  intro hk hn
  have ht : ∀ x,tmv C 4 base t x=tmv C 4 base b x := fun x=>by unfold tmv; rw [kt.mem]
  rw [ht,ht,ht]
  exact hb.point hk hn

end VG.Proof.P256.EcdhJac

end

/-! ## `Finish` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

def windowFinish : Prog isa := .seq (.block tc.outFix) (Impl.P256.EcdhJac.arithmetic tc.outOps)

/-- Final conversion preserves a canonical infinity as well as finite points. -/
theorem finish_point_ok (hC : Law C) {base : Addr} {P Q : Point C} {k : Nat} {s : State}
    (hi : RState base P Q k s) :
    WP isa windowFinish s fun t=>Frame base work s t ∧ Fixed base P k t ∧
      Inv M base 8192 C.p Sl live (tmv C 4 base t) t ∧
      Rep C (tmv C 4 base t K.R.x) (tmv C 4 base t K.R.y) (tmv C 4 base t K.R.z) Q := by
  have hm : UnitMod C.p (2^(64*M.n)) := unitMod_pow_two (by decide) _
  rw [windowFinish]
  refine WP.seq (WP.mono (outFix_ok tc hi.field.scr (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hi.fixed.zero) fun u ⟨ey,ku,ou⟩=>?_)
  have fu : Frame base work s u := ⟨ku.mono (by decide),ou.unch.cover (by decide)⟩
  have fx:=hi.fixed.keep (frame_build fu)
  have ex : wordsVal u.mem base K.R.x 4=wordsVal s.mem base K.R.x 4 := ou.wordsVal (by decide) (by decide)
  have ez : wordsVal u.mem base K.R.z 4=wordsVal s.mem base K.R.z 4 := ou.wordsVal (by decide) (by decide)
  have iu : Inv M base 8192 C.p Sl live (tmv C 4 base u) u := by
    refine ⟨fu.scr regs_x0 hi.field.scr,fx.field.mod,hi.field.sl,?_,fun _ _=>rfl⟩
    intro x hx
    change x∈[K.R.x,K.R.y,K.R.z]++ro at hx
    rcases List.mem_append.mp hx with hx|hx
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl
      · change wordsVal u.mem base K.R.x 4<C.p
        rw [ex]; exact hi.field.lt _ (by decide)
      · change wordsVal u.mem base tc.A.y tc.M.n<C.p
        rw [ey]; split
        · decide
        · exact hi.field.lt _ (by decide)
      · change wordsVal u.mem base K.R.z 4<C.p
        rw [ez]; exact hi.field.lt _ (by decide)
    · exact fx.field.lt x hx
  have hsl : ∀ op∈tc.outOps,∀ x∈op.out::op.ins,Sl x := by decide
  have hlo : ∀ op∈tc.outOps,Low M (op.out::op.ins) := fun _ _=>Low.small (by decide) _
  have hreads : readsOk tc.outOps live=true := by decide
  refine WP.mono (field_ok Out.caseProof layout aligned hm iu hsl hlo hreads)
    fun t ⟨kp,it⟩=>?_
  have ft : Frame base work u t := AllocatedFrame.of_prog kp clob_regs (by decide)
  have fr:=fu.trans ft
  have iv := it.sub (fun x (hx : x∈live)=>(mem_validAfter _ _).mpr (Or.inl hx))
  refine ⟨fr,hi.fixed.keep (frame_build fr),iv.to_tmv,?_⟩
  have hv : ∀x∈live,tmv C 4 base t x=runOps tc.outOps (tmv C 4 base u) x :=
    fun x hx=>iv.val x hx
  rw [hv K.R.x (by decide),hv K.R.y (by decide),hv K.R.z (by decide)]
  have hx : tmv C 4 base u K.R.x=tmv C 4 base s K.R.x := by unfold tmv; rw [ex]
  have hz : tmv C 4 base u K.R.z=tmv C 4 base s K.R.z := by unfold tmv; rw [ez]
  have hy : tmv C 4 base u K.R.y=if tmv C 4 base s K.R.z=0 then 1 else tmv C 4 base s K.R.y := by
    change toM C.p (2^(64*tc.M.n)) (wordsVal u.mem base tc.A.y tc.M.n)=_
    rw [ey]
    have hzero : (tmv C 4 base s K.R.z=0)↔wordsVal s.mem base K.R.z 4=0 :=
      toM_eq_zero_iff hm (hi.field.lt _ (by decide))
    change toM C.p (2^(64*4)) (if wordsVal s.mem base K.R.z 4=0 then K.one else wordsVal s.mem base K.R.y 4)=_
    by_cases hz : wordsVal s.mem base K.R.z 4=0
    · simp only [hz,hzero.mpr hz,ite_true]
      exact toM_one (m:=C.p) (R:=2^(64*4)) hm
    · have hv : tmv C 4 base s K.R.z≠0 := fun h=>hz (hzero.mp h)
      simp only [hz,hv,ite_false]
  have outvals (E : Nat→Fe C) : (runOps tc.outOps E K.R.x,
      runOps tc.outOps E K.R.y,runOps tc.outOps E K.R.z)=
      (E K.R.x*E K.R.z,E K.R.y,E K.R.z*E K.R.z*E K.R.z) := by
    simp only [tc,Impl.P256.EcdhJac.tc,TCombCfg.outOps,runOps,List.foldl_cons,List.foldl_nil,
      FOp.run,Function.update_apply,
      show K.R.x≠K.R.z from by decide,show K.R.x≠K.S.t0 from by decide,
      show K.R.y≠K.R.x from by decide,show K.R.y≠K.R.z from by decide,
      show K.R.y≠K.S.t0 from by decide,show K.R.z≠K.R.x from by decide,
      show K.R.z≠K.S.t0 from by decide,show K.S.t0≠K.R.x from by decide,ite_true,ite_false]
  have vals:=outvals (tmv C 4 base u)
  have vx:=congrArg Prod.fst vals
  have vy:=congrArg (fun p=>p.2.1) vals
  have vz:=congrArg (fun p=>p.2.2) vals
  dsimp only at vx vy vz
  rw [vx,vy,vz,hx,hy,hz]
  exact hi.point.out hC

theorem finish_ok (hC : Law C) {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hi : LoopInv base P k 0 s) :
    WP isa windowFinish s (WindowPost base P k s) := by
  obtain ⟨Q,_,he,hq⟩:=hi.state
  refine WP.mono (finish_point_ok hC hq) fun t ⟨fr,_,it,hrep⟩=>?_
  refine ⟨frame_build fr,it,fun _ hk=>?_⟩
  have eq:=he hk
  rw [Window5.winE_zero,offset_eq,Nat.add_sub_cancel] at eq
  rw [←eq]
  exact hrep

end VG.Proof.P256.EcdhJac

end
