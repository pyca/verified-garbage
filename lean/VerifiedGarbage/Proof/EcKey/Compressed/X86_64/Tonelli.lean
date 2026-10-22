module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Candidate
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.TonelliPowers
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.TonelliSetup
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DescentLoop
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DescentRound
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Frame
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Impl.EcKey.Compressed.Root

/-! # P-224's machine candidate refines its functional root algorithm -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (W2)
open VG.Impl.EcKey.Compressed.X86_64 (rootQ)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

private theorem power_writes_subset (c : Cfg) {j : Nat} (hj : j = 1 ∨ j = 2) :
    ∀ w ∈ rootPowerWrites c j, w ∈ candidateWrites c := by
  intro w hw
  change w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++ slW c [ACC, PT, TMP] at hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (rfl | rfl) | hw
  · simp [candidateWrites, candidateSlots, slW]
  · rcases hj with rfl | rfl <;> simp [candidateWrites]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    apply List.mem_append_left
    exact List.mem_map_of_mem ((by decide : ∀ i ∈ [ACC, PT, TMP], i ∈ candidateSlots) i hi)

theorem candidateTonelli_correct {c : Cfg} (hc : BaseCfgOk c) (hp : c.C.p % 4 ≠ 3)
    (hn9 : c.n ≠ 9) (hq : 0 < rootQ c) :
    CandidateCorrect c (fun a => Impl.EcKey.Compressed.rootTonelli a (rootQ c) 96 (Fin.ofNat c.C.p 11)) := by
  intro base s hs hM hB hO
  have h7 := hc.n10
  have hn := hs.nowrap
  simp only [Impl.EcKey.Compressed.X86_64.rootCandidate, hp, ↓reduceIte]
  change WP isa (.seq (Impl.EcKey.Compressed.X86_64.tonelliPowers c).inline
    (.seq (.block (Impl.EcKey.Compressed.X86_64.tonelliSetup c))
      (.loop (Impl.EcKey.Compressed.X86_64.descentRound c).inline .ne))) s _
  refine WP.seq (WP.mono (tonelliPowers_ok hc hn9 hs hM hB hO)
    fun s₁ ⟨k₁, U₁, lt₁, ltR₁, t₁, r₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (rdi_not_powClob _)
  refine WP.seq (WP.mono (tonelliSetup_ok hc hs₁ ltR₁ lt₁)
    fun s₂ ⟨k₂, U₂, lt₂, counter₂, r₂, t₂, c₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have U₁₂ : Unch base (candidateWrites c) s.mem s₂.mem :=
    unch_same (U₁.mono (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact power_writes_subset c (.inl rfl) w hw
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          exact List.mem_append_left _ (List.mem_map_of_mem
            ((by decide : ∀ i ∈ [T5], i ∈ candidateSlots) i hi))
      · exact power_writes_subset c (.inr rfl) w hw))
      (U₂.mono (by
        intro w hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_left _ (List.mem_map_of_mem
          ((by decide : ∀ i ∈ [T0, ACC, T1, T2], i ∈ candidateSlots) i hi))))
  have M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    rw [sv_unch U₁₂ h7 hn (by decide) (candidate_apart (by decide) (by decide))]
    exact hM.val)
  have one₂ : sv c base s₂ ONEP = 2 ^ (64 * c.n) % c.C.p := by
    rw [sv, sv_unch U₁₂ h7 hn (by decide) (candidate_apart (by decide) (by decide))]
    exact hO
  refine WP.mono (descentLoop_ok hc hs₂ M₂ one₂ lt₂ (by decide : 1 ≤ 95)
    (by decide : 95 < 2 ^ 31) counter₂) fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  refine ⟨(k₁.trans (k₂.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [powClob, clob]))).trans kt,
    unch_same U₁₂ (Ut.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem
        ((by decide : ∀ i ∈ roundSlots, i ∈ candidateSlots) i hi)))), ltt, ?_⟩
  change fieldAt c base t ACC = _
  rw [vt]
  change Impl.EcKey.Compressed.rootDescent 95
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ ACC))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T0))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T1)) = _
  rw [r₂, t₂, c₂, r₁, t₁, rootTonelli_eq_descent _ _ _ _ hq]
  simp only [pow_eq_npow]

end VG.Proof.EcKey.Compressed.X86_64
