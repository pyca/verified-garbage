import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalRoots

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop)

def scalePairs : List (VReg × VReg) := (List.finRange 4).map fun j => ((regs 7)[j.val],VG.Impl.MlDsa.AArch64.Optimized.Inverse.qt j.val)
def scaleLoad : List Instr := [.vop (.dupE .s4 .v20 .v30 0),.vop (.dupE .s4 .v21 .v30 1)]
def scaleCode : List Instr := scaleLoad ++ multiplyCode scalePairs

def scaleValues (v : Vector (BitVec 128) 8) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => if j.val<4 then fastVector v[j.val] (fun _ => 16382) else v[j.val]

def ScaleRoots (s : State) : Prop :=
  vword (s.v .v30) 0=BitVec.ofInt 32 16382 ∧
  vword (s.v .v30) 1=BitVec.ofInt 32 (reciprocal 16382)

theorem scaleLoad_ok {s : State} {rest : List Instr} {Q : State → Prop} (h : ScaleRoots s)
    (k : ∀ t, VChg [.v20,.v21] s t →
      (∀ e<4, vword (t.v .v20) e=BitVec.ofInt 32 16382) →
      (∀ e<4, vword (t.v .v21) e=BitVec.ofInt 32 (reciprocal 16382)) → WP isa (.block rest) t Q) :
    WP isa (.block (scaleLoad ++ rest)) s Q := by
  refine wp_vop (d := .v20) rfl fun s₁ h₁ => wp_vop (d := .v21) rfl fun t h₂ => ?_
  refine k t (h₁.chg.trans h₂.chg) ?_ ?_
  · intro e he
    rw [h₂.get .v20,h₁.v,VG.AArch64.vword_map2 _ _ _ he]
    exact h.1
  · intro e he
    rw [h₂.v,VG.AArch64.vword_map2 _ _ _ he,h₁.get .v30]
    exact h.2

theorem scale_geometry :
    (scalePairs.map Prod.fst).Nodup ∧ (scalePairs.map Prod.snd).Nodup ∧
    (∀ p∈scalePairs, p.1∉scalePairs.map Prod.snd) ∧
    (∀ p∈scalePairs, p.2∉scalePairs.map Prod.fst) ∧
    .v20∉scalePairs.map Prod.fst ∧ .v20∉scalePairs.map Prod.snd ∧
    .v21∉scalePairs.map Prod.snd ∧ .v31∉scalePairs.map Prod.fst ∧ .v31∉scalePairs.map Prod.snd := by decide +kernel

theorem scale_index (j : Fin 8) :
    (j.val<4 → ∃ tmp, ((regs 7)[j.val],tmp)∈scalePairs) ∧
    (¬j.val<4 → (regs 7)[j.val]∉scalePairs.map Prod.snd++scalePairs.map Prod.fst) := by
  have h : ∀ j : Fin 8,
      (j.val<4 → ((regs 7)[j.val],VG.Impl.MlDsa.AArch64.Optimized.Inverse.qt j.val)∈scalePairs) ∧
      (¬j.val<4 → (regs 7)[j.val]∉scalePairs.map Prod.snd++scalePairs.map Prod.fst) := by decide +kernel
  exact ⟨fun hj => ⟨_,(h j).1 hj⟩,(h j).2⟩

theorem scale_ok {s : State} {rest : List Instr} {Q : State → Prop} {v : Vector (BitVec 128) 8}
    (hb : Bank s (regs 7) v) (hs : ScaleRoots s)
    (hq : ∀ e<4, vword (s.v .v31) e=8380417#32)
    (k : ∀ t, VChg runRegs s t → Bank t (regs 7) (scaleValues v) → WP isa (.block rest) t Q) :
    WP isa (.block (scaleCode ++ rest)) s Q := by
  unfold scaleCode
  rw [List.append_assoc]
  refine scaleLoad_ok hs fun s₁ hc₁ hz₁ hb₁ => ?_
  obtain ⟨hd,ht,hdt,htd,hzd,hzt,hbt,hqd,hqt⟩ := scale_geometry
  have bank₁ : Bank s₁ (regs 7) v := by
    intro j
    rw [hc₁.get _ ((show ∀ j : Fin 8, (regs 7)[j.val]∉[.v20,.v21] by decide +kernel) j)]
    exact hb j
  have hq₁ : ∀ e<4, vword (s₁.v .v31) e=8380417#32 := by
    intro e he
    rw [hc₁.get .v31 (by decide)]
    exact hq e he
  have heq : multiplyCode scalePairs=
      scalePairs.map (fun p => Instr.vop (.sqdmulh p.2 p.1 .v21)) ++
      (scalePairs.map Prod.fst).map (fun d => Instr.vop (.mul d d .v20)) ++
      scalePairs.map (fun p => Instr.vop (.mls p.1 p.2 .v31)) := by
    simp only [multiplyCode,List.map_map,Function.comp_def]
  rw [heq]
  refine multiply_batch_ok scalePairs .v20 .v21 .v31 hd ht hdt htd hzd hzt hbt hqd hqt
    (z := fun _ => 16382) (by intro e he; decide) hz₁ hb₁ hq₁ fun t hc₂ hv => ?_
  refine k t (VChg.mono (hc₁.trans hc₂) (by decide +kernel)) ?_
  intro j
  simp only [scaleValues,Vector.getElem_ofFn]
  by_cases hj : j.val<4
  · rw [ite_eq_left hj]
    obtain ⟨tmp,htmp⟩ := (scale_index j).1 hj
    apply VG.AArch64.vec_ext
    intro e he
    rw [hv _ htmp e he,bank₁ j,fastVector_word _ _ he]
  · rw [ite_eq_right hj,hc₂.get _ ((scale_index j).2 hj)]
    exact bank₁ j

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
