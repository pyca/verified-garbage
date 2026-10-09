import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourReady

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

def samplerSetup : List Instr := samplerInit++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.initCounts++
 Impl.MlDsa.AArch64.Optimized.BoundedFour.tableInit true

theorem samplerSetup_ok {σ : State} (hp : SamplerPre σ) :
    WP isa (.block samplerSetup) σ (Ready σ) := by
  unfold samplerSetup
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (initFour_ok hp) fun s ⟨he,h0,h1⟩=>?_
  have hs : InitialPairs σ s := ⟨he,fun p h=>by
    rcases (show p=0∨p=1 by omega) with rfl|rfl
    · exact h0
    · exact h1⟩
  rw [WP.block_append_iff]
  refine WP.mono (initCounts_pairs hp hs) fun t ⟨ht,hc⟩=>?_
  exact tableInit_ready hp ht hc

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
