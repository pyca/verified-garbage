import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacComb
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)
open Spec.Weierstrass

structure JacOutPost (K : CombCfg) (C : Curve) (base : Addr) (size : Nat) (s t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (clob K.M.n) s t
  unch : Unch base (combW K) s.mem t.mem
  lt : ∀ x ∈ [K.A.x,K.A.y,K.A.z], wordsVal t.mem base x K.M.n < C.p
  val : (tmv C K.M.n base t K.A.x,tmv C K.M.n base t K.A.y,tmv C K.M.n base t K.A.z) =
    (tmv C K.M.n base s K.A.x * tmv C K.M.n base s K.A.z,
    tmv C K.M.n base s K.A.y,
    tmv C K.M.n base s K.A.z * tmv C K.M.n base s K.A.z * tmv C K.M.n base s K.A.z)

theorem jacOut_ok {K : CombCfg} {C : Curve} {base : Addr} {size : Nat} (hL : CombLay K size)
    (hA : CombA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩, wordsVal s.mem base x K.M.n < C.p)
    (hz : wordsVal s.mem base K.zero K.M.n = 0) :
    WP isa (.seq (fprogB K.M (fromJ K.S K.A ⟨K.zero,K.zero,K.zero⟩ K.E))
      (.block (copyPt K.M.n K.A K.E))) s (JacOutPost K C base size s) := by
  have hn := hs.nowrap
  have hR : ∀ x ∈ rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩, x ∈ combSlots K := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
  have hI : Inv K.M base size C.p (· ∈ combSlots K) (rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩) (tmv C K.M.n base s) s :=
    ⟨hs, hM, hR, hlt, fun _ _ => rfl⟩
  have hSl : ∀ x ∈ rcbW K.S K.E ++ rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩, x ∈ combSlots K := by
    intro x hx
    simp only [rcbW, rcbR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> comb_mem
  have hnd := hL.nodup
  have hro := hL.ro
  simp only [combWs,rcbW,List.cons_append,List.nil_append,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,not_or] at hnd
  have hApart : RcbApart K.S K.A ⟨K.zero,K.zero,K.zero⟩ K.E := by
    constructor
    · simp only [rcbW,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,
        not_or,List.nodup_nil,and_true]
      grind
    · have hwsub : ∀ x ∈ rcbW K.S K.E, x ∈ combWs K := by
        intro x hx
        simp only [rcbW,List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> comb_mem
      intro x hx
      simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact fun hw => hro K.S.a (by simp [combRo]) (hwsub _ hw)
      · exact fun hw => hro K.S.b3 (by simp [combRo]) (hwsub _ hw)
      · simp only [rcbW,List.mem_cons,List.not_mem_nil,or_false,not_or]; grind
      · simp only [rcbW,List.mem_cons,List.not_mem_nil,or_false,not_or]; grind
      · simp only [rcbW,List.mem_cons,List.not_mem_nil,or_false,not_or]; grind
      · exact fun hw => hro K.zero (by simp [combRo]) (hwsub _ hw)
      · exact fun hw => hro K.zero (by simp [combRo]) (hwsub _ hw)
      · exact fun hw => hro K.zero (by simp [combRo]) (hwsub _ hw)
  have W := ofN_ok hL.lay hA.al hp fromJN_ok hApart hSl (hA.low hSl) hI (fun _ hx => hx)
  rw [← fromJ_eq] at W
  refine WP.seq (WP.mono W fun s₁ h₁ => ?_)
  obtain ⟨k₁, I₁, v₁⟩ := h₁
  have vv := v₁.trans (fromJN_run _)
  have vz : tmv C K.M.n base s K.zero = 0 := by
    show toM _ _ _ = _
    rw [hz,toM_zero]
  simp only [rcbσ] at vv
  change (_,_,_) = (tmv C K.M.n base s K.A.x * tmv C K.M.n base s K.A.z,
    tmv C K.M.n base s K.A.y + tmv C K.M.n base s K.zero,
    tmv C K.M.n base s K.A.z * tmv C K.M.n base s K.A.z * tmv C K.M.n base s K.A.z) at vv
  rw [vz,Lean.Grind.Semiring.add_zero] at vv
  have hnd := hL.nodup
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x (combWs_slots K x hx)
  have al : ∀ x ∈ combWs K, x % 8 = 0 := fun x hx => hA.sl x (combWs_slots K x hx)
  have axd := hL.apart₂ (x := K.A.x) (y := K.E.x) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have ayd := hL.apart₂ (x := K.A.y) (y := K.E.y) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have azd := hL.apart₂ (x := K.A.z) (y := K.E.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have axy := hL.apart₂ (x := K.A.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have axz := hL.apart₂ (x := K.A.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have ayz := hL.apart₂ (x := K.A.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have dxay := hL.apart₂ (x := K.E.x) (y := K.A.y) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have dxaz := hL.apart₂ (x := K.E.x) (y := K.A.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have dyaz := hL.apart₂ (x := K.E.y) (y := K.A.z) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have hs₁ := k₁.scr hs
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  have b64 : ∀ x ∈ combWs K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have W2 := copy_ok K.M.n hs₁ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.x) (a := K.E.x) (axd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := copy_ok K.M.n hs₂ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.y) (a := K.E.y) (ayd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have W4 := copy_ok K.M.n hs₃ (le _ (by comb_mem)) (le _ (by comb_mem)) (al _ (by comb_mem))
    (al _ (by comb_mem)) (o := K.A.z) (a := K.E.z) (azd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄, O₄⟩ := h₄
  have dyax := hL.apart₂ (x := K.E.y) (y := K.A.x) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have dzax := hL.apart₂ (x := K.E.z) (y := K.A.x) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have dzay := hL.apart₂ (x := K.E.z) (y := K.A.y) (by comb_mem) (by comb_mem) (by nd_find hnd)
  have hDx : K.E.x ∈ [K.E.x, K.E.y, K.E.z] ++ rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩ := by simp
  have hDy : K.E.y ∈ [K.E.x, K.E.y, K.E.z] ++ rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩ := by simp
  have hDz : K.E.z ∈ [K.E.x, K.E.y, K.E.z] ++ rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩ := by simp
  have bAx := b64 K.A.x (by comb_mem)
  have bAy := b64 K.A.y (by comb_mem)
  have bAz := b64 K.A.z (by comb_mem)
  have bDx := b64 K.E.x (by comb_mem)
  have bDy := b64 K.E.y (by comb_mem)
  have bDz := b64 K.E.z (by comb_mem)
  have wx : wordsVal s₄.mem base K.A.x K.M.n = wordsVal s₁.mem base K.E.x K.M.n := by
    rw [O₄.wordsVal axz bAx, O₃.wordsVal axy bAx, e₂]
  have wy : wordsVal s₄.mem base K.A.y K.M.n = wordsVal s₁.mem base K.E.y K.M.n := by
    rw [O₄.wordsVal ayz bAy, e₃, O₂.wordsVal dyax bDy]
  have wz : wordsVal s₄.mem base K.A.z K.M.n = wordsVal s₁.mem base K.E.z K.M.n := by
    rw [e₄, O₃.wordsVal dzay bDz, O₂.wordsVal dzax bDz]
  refine ⟨hs₃.of_keepRegs k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.x1], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    exact ((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob K.M.n) s s₁).trans
      ((k₂.mono c1).trans ((k₃.mono c1).trans (k₄.mono c1))))
  · refine (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch))).mono ?_
    intro w hw
    simp only [combW, combWs, rcbW, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [wx]; exact I₁.lt _ hDx
    · rw [wy]; exact I₁.lt _ hDy
    · rw [wz]; exact I₁.lt _ hDz
  · rw [← vv]
    show (toM _ _ _, toM _ _ _, toM _ _ _) = _
    rw [wx, wy, wz, I₁.val _ hDx, I₁.val _ hDy, I₁.val _ hDz]

theorem ySel_bounds_ok {K : WinCfg} {base : Addr} {size : Nat} (hn0 : 0 < K.M.n)
    (hyl : K.R.y + 8*K.M.n ≤ size) (hzl : K.E.z + 8*K.M.n ≤ size)
    (hya : K.R.y % 8 = 0) (hza : K.E.z % 8 = 0)
    {s : State} (hs : Scr s base size) (h1 : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block (WinCfg.ySel K)) s fun t =>
      wordsVal t.mem base K.R.y K.M.n = (if wordsVal s.mem base K.E.z K.M.n = 0 then K.one
        else wordsVal s.mem base K.R.y K.M.n) ∧
      KeepRegs [.x1, .x2, .x4, .x5, .x7, .x9, .x16] s t ∧
      Unch base [(K.R.y, 8 * K.M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  rw [WinCfg.ySel, WP.block_append_iff]
  refine WP.mono (zeroMask_ok hs hn0 hzl hza) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (ySelWords_ok hs₁ K _ m₁ hya K.M.n hyl)
    fun t ⟨e, kt, O⟩ => ⟨?_, ?_, ?_⟩
  · by_cases hz0 : wordsVal s.mem base K.E.z K.M.n = 0
    · simp only [hz0, ↓reduceIte]
      exact wordsVal_of_shifts _ _ _ _ _ h1 fun j hj => by simp only [e j hj, hz0, ↓reduceIte]; rfl
    · simp only [hz0, ↓reduceIte]
      rw [← k₁.mem]
      exact wordsVal_of_words _ _ _ _ _ _ fun j hj => by simp only [e j hj, hz0, ↓reduceIte]
  · exact ((Keeps.regs k₁).mono (by decide)).trans (kt.mono (by decide))
  · rw [← k₁.mem]; exact O.unch.mono (by simp)



/-- Conversion of the final Jacobian accumulator, including canonical infinity. -/
theorem jacComb_finish_ok {K : TCombCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : CombLay K.toComb size) (hA : CombA K.toComb) (hC : Law C)
    (hp : UnitMod C.p (2^(64*K.M.n))) (hn4 : K.M.n=4)
    (hone_lt : K.one < C.p) (hone : toM C.p (2^(64*K.M.n)) K.one=1)
    (hpn : C.p < 2^(64*K.M.n)) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩, wordsVal s.mem base x K.M.n < C.p)
    (hz : wordsVal s.mem base K.zero K.M.n=0) {P : Point C}
    (hR : InvJ C (tmv C K.M.n base s K.A.x) (tmv C K.M.n base s K.A.y)
      (tmv C K.M.n base s K.A.z) P) :
    WP isa (Jacobian.jacCombFinish K) s fun t =>
      KeepRegs (tcombClob K.M.n) s t ∧ Unch base (combW K.toComb) s.mem t.mem ∧
      ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.A.x,K.A.y,K.A.z], wordsVal t.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base t K.A.x) (tmv C K.M.n base t K.A.y)
        (tmv C K.M.n base t K.A.z) P := by
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
  have xy := hL.apart₂ ax ay (by nd_find hnd)
  have zy := hL.apart₂ az ay (by nd_find hnd)
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
    change Rep C (toM _ _ _) _ (toM _ _ _) _
    rw [ex,ez]
    change Rep C (tmv C K.M.n base u K.A.x) _ (tmv C K.M.n base u K.A.z) _
    rw [vxv,ey,vzv]
    exact hR.out hC


/-- The public Jacobian comb returns the existing homogeneous representation. -/
theorem jacComb_ok {K : TCombCfg} {C : Curve} {base : Addr} {size k : Nat} {T : Addr}
    {tbl : List (List (Nat × Nat))} (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C)
    (hG : onCurve C (G C) = true) (hV : TCombVals K C tbl)
    (hpn : C.p < 2^(64*K.M.n)) (hn4 : K.M.n=4)
    (hSum : JacCombSumCorrect K C base size) {s : State} (hs : Scr s base size)
    (hM : ModOkA K.M size C.p s.mem base)
    (hF : TCombFixed K C base size s k T (tcombWords K.M.n (2^(64*K.M.n)) C.p tbl)) :
    WP isa (Jacobian.jacComb K) s fun t => KeepRegs (tcombClob K.M.n) s t ∧
      Unch base (tcombW K) s.mem t.mem ∧ ModOkA K.M size C.p t.mem base ∧
      (∀ x ∈ [K.A.x,K.A.y,K.A.z], wordsVal t.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base t K.A.x) (tmv C K.M.n base t K.A.y)
        (tmv C K.M.n base t K.A.z) (mul k (G C)) := by
  unfold Jacobian.jacComb
  refine WP.seq (WP.mono (jacComb_loop_ok hL hA hC hG hV hpn hSum hs hM hF)
    fun u ⟨ku,uu,mu,lu,ru⟩ => ?_)
  have su := hs.of_keepRegs ku (by rw [hn4]; decide)
  have hro : ∀ x ∈ combRo K.toComb, wordsVal u.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    exact uu.wordsVal (tcombW_ro hL hx) (by
      have he : x+8*K.M.n ≤ size := hL.comb.lay.le _ (combRo_slots _ hx)
      have := hs.nowrap
      omega)
  have hlt : ∀ x ∈ rcbR K.S K.A ⟨K.zero,K.zero,K.zero⟩,
      wordsVal u.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hro _ (by simp [combRo,TCombCfg.toComb])]
      exact hF.ro_lt _ (by simp [combRo,TCombCfg.toComb])
    · rw [hro _ (by simp [combRo,TCombCfg.toComb])]
      exact hF.ro_lt _ (by simp [combRo,TCombCfg.toComb])
    · exact lu _ (by simp)
    · exact lu _ (by simp)
    · exact lu _ (by simp)
    · rw [hro _ (by simp [combRo,TCombCfg.toComb])]
      exact hF.ro_lt _ (by simp [combRo,TCombCfg.toComb])
    · rw [hro _ (by simp [combRo,TCombCfg.toComb])]
      exact hF.ro_lt _ (by simp [combRo,TCombCfg.toComb])
    · rw [hro _ (by simp [combRo,TCombCfg.toComb])]
      exact hF.ro_lt _ (by simp [combRo,TCombCfg.toComb])
  have hz : wordsVal u.mem base K.zero K.M.n=0 := by
    rw [hro _ (by simp [combRo,TCombCfg.toComb]),hF.zero]
  refine WP.mono (jacComb_finish_ok hL.comb hA hC hV.unit hn4 hV.one_lt hV.one hpn su mu hlt hz ru)
    fun t ⟨kt,ut,mt,lt,rt⟩ => ⟨ku.trans kt,?_,mt,lt,rt⟩
  exact (uu.trans ut).mono (fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact List.mem_append_left _ hw)


end VG.Proof.Weierstrass.AArch64
