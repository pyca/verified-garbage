import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open Spec.Weierstrass

theorem jacComb_finish_exact {K : TCombCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : CombLay K.toComb size) (hA : CombA K.toComb) (hC : Law C)
    (hp : UnitMod C.p (2^(64*K.M.n))) (hn4 : K.M.n=4)
    (hone_lt : K.one < C.p) (hone : toM C.p (2^(64*K.M.n)) K.one=1)
    (hpn : C.p < 2^(64*K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩, wordsVal s.mem base x K.M.n < C.p)
    (hz : wordsVal s.mem base K.zero K.M.n=0) :
    WP isa (Jacobian.jacCombFinish K) s fun t =>
      KeepRegs (tcombClob K.M.n) s t ∧ Unch base (combW K.toComb) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.A.x,K.A.y,K.A.z], wordsVal t.mem base x K.M.n < C.p) ∧
      (tmv C K.M.n base t K.A.x,tmv C K.M.n base t K.A.y,tmv C K.M.n base t K.A.z) =
        (tmv C K.M.n base s K.A.x * tmv C K.M.n base s K.A.z,
         if tmv C K.M.n base s K.A.z=0 then 1 else tmv C K.M.n base s K.A.y,
         tmv C K.M.n base s K.A.z * tmv C K.M.n base s K.A.z * tmv C K.M.n base s K.A.z) := by
  have hn := hs.nowrap
  have hn0 : 0 < K.M.n := by omega
  let W : WinCfg := {Jacobian.combWinCfg K with E := K.A}
  have hy : K.A.y ∈ combSlots K.toComb := by tcomb_mem
  have hz' : K.A.z ∈ combSlots K.toComb := by tcomb_mem
  have hys : K.A.y+8*K.M.n ≤ size := hL.lay.le _ hy
  have hzs : K.A.z+8*K.M.n ≤ size := hL.lay.le _ hz'
  have hya := hA.sl _ hy
  have hza := hA.sl _ hz'
  unfold Jacobian.jacCombFinish
  rw [← hn4]
  refine WP.seq (WP.mono (jacOut_ok hL hA hp hs hM hlt hz) fun u hu => ?_)
  dsimp only [TCombCfg.toComb] at hu
  refine WP.mono (ySel_bounds_ok (K := W) hn0 hys hzs hya hza hu.scr
    (Nat.lt_trans hone_lt hpn)) fun t ⟨vy,ky,uy⟩ => ?_
  change wordsVal t.mem base K.A.y K.M.n = (if wordsVal u.mem base K.A.z K.M.n = 0
    then K.one else wordsVal u.mem base K.A.y K.M.n) at vy
  change Unch base [(K.A.y,8*K.M.n)] u.mem t.mem at uy
  have hval := hu.val
  change (tmv C K.M.n base u K.A.x,tmv C K.M.n base u K.A.y,tmv C K.M.n base u K.A.z) =
    (tmv C K.M.n base s K.A.x * tmv C K.M.n base s K.A.z,tmv C K.M.n base s K.A.y,
    tmv C K.M.n base s K.A.z * tmv C K.M.n base s K.A.z * tmv C K.M.n base s K.A.z) at hval
  simp only [Prod.mk.injEq] at hval
  obtain ⟨vxv,vyv,vzv⟩ := hval
  have hnd := hL.nodup
  simp only [combWs,rcbW,TCombCfg.toComb,List.cons_append,List.nil_append,List.nodup_cons,
    List.mem_cons,List.not_mem_nil,or_false,not_or] at hnd
  have ax : K.A.x ∈ combWs K.toComb := by tcomb_mem
  have ay : K.A.y ∈ combWs K.toComb := by tcomb_mem
  have az : K.A.z ∈ combWs K.toComb := by tcomb_mem
  have xy := hL.apart₂ ax ay (by grind)
  have zy := hL.apart₂ az ay (by grind)
  have ex : wordsVal t.mem base K.A.x K.M.n = wordsVal u.mem base K.A.x K.M.n :=
    uy.wordsVal (by simpa only [List.mem_singleton] using fun w (hw : w=(K.A.y,8*K.M.n)) => hw ▸ xy)
      (by have hxl : K.A.x+8*K.M.n ≤ size := hL.lay.le _ (combWs_slots _ _ ax); omega)
  have ez : wordsVal t.mem base K.A.z K.M.n = wordsVal u.mem base K.A.z K.M.n :=
    uy.wordsVal (by simpa only [List.mem_singleton] using fun w (hw : w=(K.A.y,8*K.M.n)) => hw ▸ zy)
      (by omega)
  have uysub : Unch base (combW K.toComb) u.mem t.mem := uy.mono (by
    intro w hw
    rw [List.mem_singleton.mp hw]
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨K.A.y,ay,rfl⟩)
  have ut := hu.unch.trans uysub
  have ut' : Unch base (combW K.toComb) s.mem t.mem := ut.mono (by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw <;> exact hw)
  refine ⟨?_,ut',hM.unch ut' (combW_mo hL hM) hn,?_,?_⟩
  · exact (hu.keep.mono (fun r hr => combClob_tcombClob _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hr))))).trans
      (ky.mono (fun r hr => tcombClob_sub K.M.n (by omega) r (by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)))
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex]; exact hu.lt _ (by simp)
    · rw [vy]; split
      · exact hone_lt
      · exact hu.lt _ (by simp)
    · rw [ez]; exact hu.lt _ (by simp)
  · have vz : wordsVal u.mem base K.A.z K.M.n = 0 ↔ tmv C K.M.n base s K.A.z = 0 := by
      rw [← toM_eq_zero_iff hp (hu.lt _ (by simp))]
      change tmv C K.M.n base u K.A.z = 0 ↔ _
      rw [vzv]
      constructor
      · intro h
        by_contra hn
        exact cube_ne_zero hC hn h
      · intro h; rw [h]; grind
    have ey : tmv C K.M.n base t K.A.y =
        if tmv C K.M.n base s K.A.z = 0 then 1 else tmv C K.M.n base s K.A.y := by
      show toM _ _ _ = _
      rw [vy]
      split
      next h => rw [hone,ite_eq_left (vz.mp h)]
      next h => rw [ite_eq_right (mt vz.mpr h)]; exact vyv
    change (toM _ _ _,_,toM _ _ _) = _
    rw [ex,ez]
    change (tmv C K.M.n base u K.A.x,_,tmv C K.M.n base u K.A.z) = _
    rw [vxv,ey,vzv]

def jacFinishLive (K : TCombCfg) : List Nat :=
  combRo K.toComb ++ [K.A.x,K.A.y,K.A.z]

/-- Canonical conversion preserves equality of the initialized public coordinates. -/
theorem jacCombFinish_relCT {K : TCombCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : CombLay K.toComb size) (hA : CombA K.toComb) (hC : Law C)
    (hp : UnitMod C.p (2^(64*K.M.n))) (hn4 : K.M.n=4)
    (hone_lt : K.one<C.p) (hone : toM C.p (2^(64*K.M.n)) K.one=1)
    (hpn : C.p<2^(64*K.M.n))
    (hct : ConstantTime isa (fun _ => True) (AArch64.Taint.Agree (Taint.ofRegs [.x0]))
      (Jacobian.jacCombFinish K)) {E : Nat → Fe C} (hz : E K.zero=0) :
    RelCT isa (FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacFinishLive K) E)
      (Jacobian.jacCombFinish K) (fun s t => ∃ E',
        FieldPair K.M base size C.p (·∈combSlots K.toComb) (jacFinishLive K) E' s t) := by
  intro s t ts tt s' t' pair es et
  have sub : ∀ x∈rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩,x∈jacFinishLive K := by
    intro x hx
    simp only [rcbR,jacFinishLive,combRo,TCombCfg.toComb,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hx ⊢
    grind
  have hzmem : ∀ u, Inv K.M base size C.p (·∈combSlots K.toComb) (jacFinishLive K) E u →
      wordsVal u.mem base K.zero K.M.n=0 := by
    intro u hu
    have hzv : K.zero∈jacFinishLive K := by simp [jacFinishLive,combRo,TCombCfg.toComb]
    exact (toM_eq_zero_iff hp (hu.lt _ hzv)).mp ((hu.val _ hzv).trans hz)
  obtain ⟨_,_,xs,ks,us,ms,ls,vs⟩ := jacComb_finish_exact hL hA hC hp hn4 hone_lt hone hpn
    pair.left.scr pair.left.mod (fun x hx => pair.left.lt x (sub x hx)) (hzmem s pair.left)
  obtain ⟨_,_,xt,kt,ut,mt,lt,vt⟩ := jacComb_finish_exact hL hA hC hp hn4 hone_lt hone hpn
    pair.right.scr pair.right.mod (fun x hx => pair.right.lt x (sub x hx)) (hzmem t pair.right)
  obtain ⟨_,rfl⟩ := Exec.det es xs
  obtain ⟨_,rfl⟩ := Exec.det et xt
  have common : ∀ x∈jacFinishLive K,tmv C K.M.n base s x=tmv C K.M.n base t x :=
    fun x hx => (pair.left.val x hx).trans (pair.right.val x hx).symm
  have xyz : ∀ x∈[K.A.x,K.A.y,K.A.z],tmv C K.M.n base s' x=tmv C K.M.n base t' x := by
    have h := common K.A.x (by simp [jacFinishLive])
    have j := common K.A.y (by simp [jacFinishLive])
    have k := common K.A.z (by simp [jacFinishLive])
    rw [h,j,k] at vs
    have he := vs.trans vt.symm
    simp only [Prod.mk.injEq] at he
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact he.1
    · exact he.2.1
    · exact he.2.2
  have ros : ∀ x∈combRo K.toComb,wordsVal s'.mem base x K.M.n=wordsVal s.mem base x K.M.n := by
    intro x hx
    exact us.wordsVal (combW_ro hL hx) (by
      have hb : x+8*K.M.n≤size := hL.lay.le x (combRo_slots x hx)
      have := pair.left.scr.nowrap; omega)
  have rot : ∀ x∈combRo K.toComb,wordsVal t'.mem base x K.M.n=wordsVal t.mem base x K.M.n := by
    intro x hx
    exact ut.wordsVal (combW_ro hL hx) (by
      have hb : x+8*K.M.n≤size := hL.lay.le x (combRo_slots x hx)
      have := pair.right.scr.nowrap; omega)
  have eqout : ∀ x∈jacFinishLive K,tmv C K.M.n base s' x=tmv C K.M.n base t' x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · show toM _ _ _ = toM _ _ _
      rw [ros x hx,rot x hx]
      exact common x (List.mem_append_left _ hx)
    · exact xyz x hx
  have sl : ∀ x∈jacFinishLive K,x∈combSlots K.toComb := pair.left.sl
  have ls' : ∀ x∈jacFinishLive K,wordsVal s'.mem base x K.M.n<C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [ros x hx]; exact pair.left.lt x (List.mem_append_left _ hx)
    · exact ls x hx
  have lt' : ∀ x∈jacFinishLive K,wordsVal t'.mem base x K.M.n<C.p := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [rot x hx]; exact pair.right.lt x (List.mem_append_left _ hx)
    · exact lt x hx
  have nx0 : Reg.x0∉tcombClob K.M.n := by rw [hn4]; decide
  exact ⟨hct _ _ _ _ _ _ trivial trivial pair.public es et,tmv C K.M.n base s',
    ⟨pair.left.scr.of_keepRegs ks nx0,ms,sl,ls',fun _ _ => rfl⟩,
    ⟨pair.right.scr.of_keepRegs kt nx0,mt,sl,lt',fun x hx => (eqout x hx).symm⟩,
    ks.sp.trans (pair.sp.trans kt.sp.symm)⟩

end VG.Proof.Weierstrass.AArch64
