import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacMixedAdd

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps)
open Spec.Weierstrass

/-- Move the verified mixed-addition result into the comb accumulator. -/
theorem jacComb_sum_copy_ok {K : TCombCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : CombLay K.toComb size) (hA : CombA K.toComb) (hn4 : K.M.n=4)
    {s : State} (hs : Scr s base size) {P Q : Point C}
    (hMixed : WP isa (Jacobian.jacMixedAdd (Jacobian.combWinCfg K) K.A K.E K.D) s
      (JacPost K.M K.S base size C (· ∈ combSlots K.toComb) (rcbR K.S K.A K.E)
        K.D (Spec.Weierstrass.add P Q) s)) :
    WP isa (Jacobian.jacCombSum K) s (JacCombSumPost K C base size P Q s) := by
  unfold Jacobian.jacCombSum
  have hn := hs.nowrap
  refine WP.seq (WP.mono hMixed fun s₁ ⟨E₁,k₁,I₁,j₁⟩ => ?_)
  have hnd := hL.nodup
  dsimp only [TCombCfg.toComb] at hnd
  simp only [combWs, rcbW, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hnd
  have le : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ size := fun x hx => hL.lay.le x (combWs_slots K.toComb x hx)
  have al : ∀ x ∈ combWs K.toComb, x % 8 = 0 := fun x hx => hA.sl x (combWs_slots K.toComb x hx)
  have axd : K.A.x+8*K.M.n ≤ K.D.x ∨ K.D.x+8*K.M.n ≤ K.A.x := hL.apart₂ (x := K.A.x) (y := K.D.x) (by tcomb_mem) (by tcomb_mem) (by grind)
  have ayd : K.A.y+8*K.M.n ≤ K.D.y ∨ K.D.y+8*K.M.n ≤ K.A.y := hL.apart₂ (x := K.A.y) (y := K.D.y) (by tcomb_mem) (by tcomb_mem) (by grind)
  have azd : K.A.z+8*K.M.n ≤ K.D.z ∨ K.D.z+8*K.M.n ≤ K.A.z := hL.apart₂ (x := K.A.z) (y := K.D.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have axy : K.A.x+8*K.M.n ≤ K.A.y ∨ K.A.y+8*K.M.n ≤ K.A.x := hL.apart₂ (x := K.A.x) (y := K.A.y) (by tcomb_mem) (by tcomb_mem) (by grind)
  have axz : K.A.x+8*K.M.n ≤ K.A.z ∨ K.A.z+8*K.M.n ≤ K.A.x := hL.apart₂ (x := K.A.x) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have ayz : K.A.y+8*K.M.n ≤ K.A.z ∨ K.A.z+8*K.M.n ≤ K.A.y := hL.apart₂ (x := K.A.y) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have dxay : K.D.x+8*K.M.n ≤ K.A.y ∨ K.A.y+8*K.M.n ≤ K.D.x := hL.apart₂ (x := K.D.x) (y := K.A.y) (by tcomb_mem) (by tcomb_mem) (by grind)
  have dxaz : K.D.x+8*K.M.n ≤ K.A.z ∨ K.A.z+8*K.M.n ≤ K.D.x := hL.apart₂ (x := K.D.x) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have dyaz : K.D.y+8*K.M.n ≤ K.A.z ∨ K.A.z+8*K.M.n ≤ K.D.y := hL.apart₂ (x := K.D.y) (y := K.A.z) (by tcomb_mem) (by tcomb_mem) (by grind)
  have hs₁ := k₁.scr hs
  rw [← hn4]
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  have b64 : ∀ x ∈ combWs K.toComb, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [this, hn]
  have W2 := copy_ok K.M.n hs₁ (le _ (by tcomb_mem)) (le _ (by tcomb_mem)) (al _ (by tcomb_mem))
    (al _ (by tcomb_mem)) (o := K.A.x) (a := K.D.x) (axd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W2 fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W3 := copy_ok K.M.n hs₂ (le _ (by tcomb_mem)) (le _ (by tcomb_mem)) (al _ (by tcomb_mem))
    (al _ (by tcomb_mem)) (o := K.A.y) (a := K.D.y) (ayd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W3 fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have W4 := copy_ok K.M.n hs₃ (le _ (by tcomb_mem)) (le _ (by tcomb_mem)) (al _ (by tcomb_mem))
    (al _ (by tcomb_mem)) (o := K.A.z) (a := K.D.z) (azd.imp (fun h => by omega_using [h]) id)
  refine WP.mono W4 fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄, O₄⟩ := h₄
  have dyax : K.D.y+8*K.M.n ≤ K.A.x ∨ K.A.x+8*K.M.n ≤ K.D.y := hL.apart₂ (x := K.D.y) (y := K.A.x) (by tcomb_mem) (by tcomb_mem) (by grind)
  have dzax : K.D.z+8*K.M.n ≤ K.A.x ∨ K.A.x+8*K.M.n ≤ K.D.z := hL.apart₂ (x := K.D.z) (y := K.A.x) (by tcomb_mem) (by tcomb_mem) (by grind)
  have dzay : K.D.z+8*K.M.n ≤ K.A.y ∨ K.A.y+8*K.M.n ≤ K.D.z := hL.apart₂ (x := K.D.z) (y := K.A.y) (by tcomb_mem) (by tcomb_mem) (by grind)
  have hDx : K.D.x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E := by simp
  have hDy : K.D.y ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E := by simp
  have hDz : K.D.z ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.A K.E := by simp
  have bAx := b64 K.A.x (by tcomb_mem)
  have bAy := b64 K.A.y (by tcomb_mem)
  have bAz := b64 K.A.z (by tcomb_mem)
  have bDx := b64 K.D.x (by tcomb_mem)
  have bDy := b64 K.D.y (by tcomb_mem)
  have bDz := b64 K.D.z (by tcomb_mem)
  have wx : wordsVal s₄.mem base K.A.x K.M.n = wordsVal s₁.mem base K.D.x K.M.n := by
    rw [O₄.wordsVal axz bAx, O₃.wordsVal axy bAx, e₂]
  have wy : wordsVal s₄.mem base K.A.y K.M.n = wordsVal s₁.mem base K.D.y K.M.n := by
    rw [O₄.wordsVal ayz bAy, e₃, O₂.wordsVal dyax bDy]
  have wz : wordsVal s₄.mem base K.A.z K.M.n = wordsVal s₁.mem base K.D.z K.M.n := by
    rw [e₄, O₃.wordsVal dzay bDz, O₂.wordsVal dzax bDz]
  refine ⟨hs₃.of_keepRegs k₄ (by decide), ?_, ?_, ?_, ?_⟩
  · have c1 : ∀ r ∈ [Reg.x1], r ∈ clob K.M.n := by intro r hr; simp at hr; subst hr; simp [clob]
    exact ((⟨k₁.gpr, k₁.rd, k₁.wr, k₁.sp⟩ : KeepRegs (clob K.M.n) s s₁).trans
      ((k₂.mono c1).trans ((k₃.mono c1).trans (k₄.mono c1))))
  · refine (k₁.unch.trans (O₂.unch.trans (O₃.unch.trans O₄.unch))).mono ?_
    intro w hw
    simp only [combW, combWs, rcbW, TCombCfg.toComb, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [wx]; exact I₁.lt _ hDx
    · rw [wy]; exact I₁.lt _ hDy
    · rw [wz]; exact I₁.lt _ hDz
  · change InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [wx,wy,wz,I₁.val _ hDx,I₁.val _ hDy,I₁.val _ hDz]
    exact j₁


/-- The mixed arithmetic supplies the comb loop's addition contract. -/
theorem jacComb_sum_ok {K : TCombCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : TCombLay K size) (hA : CombA K.toComb) (hC : Law C) (ha : AM3 C)
    (hp : UnitMod C.p (2^(64*K.M.n))) (hn4 : K.M.n=4) (hone : K.one<C.p) :
    JacCombSumCorrect K C base size := by
  intro s P Q hs hm hlt _ hP hQ hJP hRQ hz
  have hSl : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.A K.E, x ∈ combSlots K.toComb := by
    intro x hx
    simp only [rcbW,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx | hx
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tcomb_mem
  have hI : Inv K.M base size C.p (· ∈ combSlots K.toComb) (rcbR K.S K.A K.E)
      (tmv C K.M.n base s) s :=
    ⟨hs,hm,fun x hx => hSl x (List.mem_append_right _ hx),hlt,fun _ _ => rfl⟩
  have hJQ : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y)
      (tmv C K.M.n base s K.E.z) Q := by
    right
    rw [hz]
    simpa only [hz,Lean.Grind.Semiring.mul_one] using hRQ
  apply jacComb_sum_copy_ok hL.comb hA hn4 hs
  exact jacMixedAdd_ok (K := Jacobian.combWinCfg K) hL.comb.lay hA.al (callOf_small (Nat.le_of_eq hn4)) hp hC ha
    hL.comb.add hSl hI (fun _ hx => hx) hone hP hQ hJP hJQ hz


end VG.Proof.Weierstrass.AArch64
