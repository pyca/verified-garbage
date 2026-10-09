import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Hoisted

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem outerGroup_ok (r : Ren) (gap group index : Nat) (hv : ValidGroup gap group)
    (hi : 1 ≤ index) (hi' : index ≤ 8)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    {z : Nat → Int} (hr : GoodRen r) (hbank : Bank s r.data values) (hconst : Hoisted s z)
    (k : ∀ t, VChg outerRegs s t → Hoisted t z →
      Bank t (renGroup r gap group (hoistedRoot index)).data
        (coreValues values gap group (fun _ => z index)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (hoistedRoot index ++ coreCode r gap group ++ rest)) s Q := by
  rw [List.append_assoc]
  refine hoistedRoot_ok index hi hi' hconst fun s₁ hc₁ hz₁ hb₁ => ?_
  have hrange : 0 ≤ z index ∧ z index < 8380417 := by
    have h := hconst.range (index-1) (by omega)
    rwa [Nat.sub_add_cancel hi] at h
  have hp : ∀ v ∈ liveRegs, v ∉ prodTemps ∧ v ≠ VReg.v18 ∧ v ≠ VReg.v16 := by decide
  have hq₁ : ∀ e < 4, vword (s₁.v .v16) e = 8380417#32 := by
    intro e he
    rw [hc₁.get .v16]
    exact hconst.q e he
  refine coreCode_ok r gap group hv (hr.root_keep hbank hc₁) hr.injective hr.apart
    (fun i => (hp _ (hr.data i)).1) (fun i => (hp _ (hr.data i)).2.1)
    (fun i => (hp _ (hr.data i)).2.2) (fun _ _ => hrange) hz₁ hb₁ hq₁
    fun s₂ hc₂ h₂ _ _ => ?_
  have hc : VChg outerRegs s s₂ := hc₁.trans (hc₂.mono (hr.coreClobs_mem gap group hv))
  refine k s₂ hc (hconst.keep hc) ?_
  rw [renGroup_data r gap group hv (hoistedRoot index)]
  exact h₂

end VG.Proof.MlDsa.AArch64.Optimized
