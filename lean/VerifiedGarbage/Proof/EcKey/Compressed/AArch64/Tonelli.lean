module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Candidate
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.TonelliPowers
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.TonelliSetup
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DescentLoop
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DescentRound
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.Root

/-! # P-224's machine candidate refines the shared root algorithm -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (W2)
open VG.Impl.EcKey.Compressed.AArch64 (rootQ rootChain)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 theorem candidateTonelli_correct {c : Cfg} (hc : BaseCfgOk c) (hp : c.C.p % 4 ≠ 3)
    (hq : 0 < rootQ c)
    (hR : ChainOk (rootChain c ((rootQ c + 1) / 2)) ((rootQ c + 1) / 2))
    (hQ : ChainOk (rootChain c (rootQ c)) (rootQ c))
    (hV : ∀ i ∈ instrs (Impl.EcKey.Compressed.AArch64.descentBody c), vdstOf i ≠ some .v27) :
    CandidateCorrect c (fun a => Impl.EcKey.Compressed.rootTonelli a (rootQ c) 96 (Fin.ofNat c.C.p 11)) := by
  intro base s hs hM hB hO
  have h7 := hc.n10
  have hn := hs.nowrap
  simp only [Impl.EcKey.Compressed.AArch64.rootCandidate, hp, ↓reduceIte]
  change WP isa (.seq (Impl.EcKey.Compressed.AArch64.tonelliPowers c)
    (.seq (.block (Impl.EcKey.Compressed.AArch64.tonelliSetup c))
      (.loop (Impl.EcKey.Compressed.AArch64.descentRound c) (.nonzero .x .x19)))) s _
  refine WP.seq (WP.mono (tonelliPowers_ok hc hR hQ hs hM hB)
    fun s₁ ⟨k₁, U₁, lt₁, ltR₁, t₁, r₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (x0_not_powClob _)
  refine WP.seq (WP.mono (tonelliSetup_ok hc hs₁ ltR₁ lt₁)
    fun s₂ ⟨k₂, U₂, lt₂, counter₂, r₂, t₂, c₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₁₂ : Unch base (candidateWrites c) s.mem s₂.mem := by
    apply unch_same (U₁.mono ?_) (U₂.mono ?_)
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_left _ hw
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          exact List.mem_append_right _ (List.mem_map_of_mem
            ((by decide : ∀ i ∈ [T5], i ∈ candidateSlots) i hi))
      · exact List.mem_append_left _ hw
    · intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_right _ (List.mem_map_of_mem
        ((by decide : ∀ i ∈ [T0, ACC, T1], i ∈ candidateSlots) i hi))
  have M₂ : ModOkA c.MP' size c.C.p s₂.mem base := modP_of hc (by
    rw [sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact hM.val)
  have one₂ : sv c base s₂ ONEP = 2 ^ (64 * c.n) % c.C.p := by
    rw [sv, sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact hO
  refine WP.mono (descentLoop_ok hc hV hs₂ M₂ one₂ lt₂ (by decide : 1 ≤ 95)
    (by decide : 95 < 2 ^ 31) counter₂) fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  refine ⟨(k₁.trans (k₂.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [powClob, clob]))).trans kt,
    unch_same U₁₂ (Ut.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_right _ (List.mem_map_of_mem
        ((by decide : ∀ i ∈ roundSlots, i ∈ candidateSlots) i hi)))), ltt, ?_⟩
  change fieldAt c base t ACC = _
  rw [vt]
  change Impl.EcKey.Compressed.rootDescent 95
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ ACC))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T0))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T1)) = _
  rw [r₂, t₂, c₂, r₁, t₁, rootTonelli_eq_descent _ _ _ _ hq]
  simp only [pow_eq_npow]

end VG.Proof.EcKey.Compressed.AArch64
