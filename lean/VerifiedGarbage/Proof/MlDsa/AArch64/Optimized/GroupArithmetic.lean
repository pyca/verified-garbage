import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Group
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Indexed

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def coreCode (r : Ren) (gap group : Nat) : List Instr :=
  multiplyCode (groupProducts r gap group) ++ pairOps r (groupSteps gap group)

theorem renGroup_factor (r : Ren) (gap group : Nat) (hv : ValidGroup gap group)
    (roots : List Instr) :
    (renGroup r gap group roots).code = r.code ++ roots ++ coreCode r gap group := by
  rw [renGroup_code r gap group hv roots,
    pairOps_same (r := groupStart r gap group roots) (r' := r) rfl rfl]
  simp only [coreCode, List.append_assoc]

def coreClobs (r : Ren) (gap group : Nat) : List VReg :=
  ((groupIndexedProducts gap group).map Prod.snd ++
    ((groupIndexedProducts gap group).map Prod.fst).map (fun i => r.data[i.val])) ++
      pairClobs r (groupSteps gap group)

def coreValues (v : Vector (BitVec 128) 8) (gap group : Nat) (z : Nat → Int) :
    Vector (BitVec 128) 8 :=
  afterValues (productValues v ((groupIndexedProducts gap group).map Prod.fst) z)
    (groupSteps gap group)

/-- A complete selected butterfly group: scheduled products followed by
renamed sums and differences. -/
theorem coreCode_ok (r : Ren) (gap group : Nat) (hv : ValidGroup gap group)
    {s : State} {rest : List Instr} {Q : State → Prop} {values : Vector (BitVec 128) 8}
    {z : Nat → Int} (hbank : Bank s r.data values)
    (hinj : Function.Injective (fun i : Fin 8 => r.data[i.val]))
    (hf : ∀ i : Fin 8, r.data[i.val] ≠ r.free)
    (hclear : ∀ i : Fin 8, r.data[i.val] ∉ prodTemps)
    (h18 : ∀ i : Fin 8, r.data[i.val] ≠ .v18) (h16 : ∀ i : Fin 8, r.data[i.val] ≠ .v16)
    (hz : ∀ e < 4, 0 ≤ z e ∧ z e < 8380417)
    (hzw : ∀ e < 4, vword (s.v .v18) e = BitVec.ofInt 32 (z e))
    (hbw : ∀ e < 4, vword (s.v .v19) e = BitVec.ofInt 32 (reciprocal (z e)))
    (hqw : ∀ e < 4, vword (s.v .v16) e = 8380417#32)
    (k : ∀ t, VChg (coreClobs r gap group) s t →
      Bank t (afterPairs r (groupSteps gap group)).data (coreValues values gap group z) →
      Function.Injective (fun i : Fin 8 => (afterPairs r (groupSteps gap group)).data[i.val]) →
      (∀ i : Fin 8, (afterPairs r (groupSteps gap group)).data[i.val] ≠
        (afterPairs r (groupSteps gap group)).free) → WP isa (.block rest) t Q) :
    WP isa (.block (coreCode r gap group ++ rest)) s Q := by
  have shape := groupIndices_shape gap group hv
  have hnot (v : VReg) (hn : v ∉ prodTemps) :
      v ∉ (groupIndexedProducts gap group).map Prod.snd := by
    intro h
    rcases List.mem_map.mp h with ⟨p,hp,he⟩
    exact hn (he ▸ shape.2.2.2 p hp)
  have hc : ∀ i : Fin 8, r.data[i.val] ∉ (groupIndexedProducts gap group).map Prod.snd :=
    fun i => hnot _ (hclear i)
  have hi : ((groupIndexedProducts gap group).map Prod.fst).Nodup := by
    rw [shape.1]
    exact shape.2.1
  simp only [coreCode, List.append_assoc, multiplyCode, groupProducts_indexed r gap group hv]
  have run := indexed_multiply_ok (groupIndexedProducts gap group) r.data .v18 .v19 .v16
    (rest := pairOps r (groupSteps gap group) ++ rest) (Q := Q)
    hi shape.2.2.1 hinj hc h18 h16 (hnot _ (by decide)) (hnot _ (by decide))
    (hnot _ (by decide)) hbank hz hzw hbw hqw
  have result := run (fun s₁ hc₁ h₁ => by
    refine pairOps_ok r (groupSteps gap group) h₁ hinj hf fun s₂ hc₂ h₂ hi₂ hf₂ => ?_
    exact k s₂ (hc₁.trans hc₂) h₂ hi₂ hf₂)
  simpa only [List.append_assoc] using result

end VG.Proof.MlDsa.AArch64.Optimized
