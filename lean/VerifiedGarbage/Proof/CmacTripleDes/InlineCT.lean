module

public import VerifiedGarbage.Proof.Framework.RelCT

/-!
# Two runs of inlined verified code, on any ISA

The streaming functions of 32-bit targets run the code of TDEA-CMAC's
primitives inline in a frame, which the taint analysis does not analyse: two
runs of the code inlined leak the same trace when its contract holds in both
(narrowed to regions their states' regions cover, as `WP.inline` does) and
its public data agree, since each run is the run from the narrowed state
(`RegionModel.trace_narrow`), which is constant time. (The same as
`Proof/Framework/X86_64/InlineCalls.lean`'s, which other targets may not
import.)
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes

open VG

theorem relCT_inline {M : ISA} (R : RegionModel M) {c : Prog M} {Pre : M.State → Prop}
    {Post : M.State → M.State → Prop} {Pub : M.State → M.State → Prop}
    (hv : ∀ s, Pre s → ∃ t s', Exec M c s t s' ∧ Post s s')
    (hct : ConstantTime M Pre Pub c) {P : M.State → M.State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ →
      ∃ r₁ w₁ r₂ w₂ : List Region,
        Pre (R.withRegions s₁ r₁ w₁) ∧ Pre (R.withRegions s₂ r₂ w₂) ∧
        Pub (R.withRegions s₁ r₁ w₁) (R.withRegions s₂ r₂ w₂) ∧
        Covers (r₁ ++ w₁) (R.rd s₁ ++ R.wr s₁) ∧ Covers w₁ (R.wr s₁) ∧
        Covers (r₂ ++ w₂) (R.rd s₂ ++ R.wr s₂) ∧ Covers w₂ (R.wr s₂)) :
    RelCT M P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨_, _, _, _, p₁, p₂, hpub, c₁, w₁, c₂, w₂⟩ := hP _ _ hp
  obtain ⟨_, n₁⟩ := R.trace_narrow hv p₁ c₁ w₁ e₁
  obtain ⟨_, n₂⟩ := R.trace_narrow hv p₂ c₂ w₂ e₂
  exact ⟨hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂, trivial⟩

end VG.Proof.CmacTripleDes
