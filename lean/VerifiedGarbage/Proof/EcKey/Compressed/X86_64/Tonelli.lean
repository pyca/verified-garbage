module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Candidate
public import VerifiedGarbage.Impl.EcKey.Compressed.Root

import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.TonelliSetup
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DescentRound
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Frame
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.RootPow
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
/-! # P-224's machine candidate refines its functional root algorithm -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/TonelliPowers.lean`, which only this module imported.
section

/-! # The two initial powers in P-224's root recovery -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdh.X86_64 (W2)
open VG.Impl.EcKey.Compressed.X86_64 (rootQ)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

abbrev tonelliPowerWrites (c : Cfg) :=
  rootPowerWrites c 1 ++ slW c [T5] ++ rootPowerWrites c 2

theorem tonelliPowers_ok {c : Cfg} (hc : BaseCfgOk c) (hn9 : c.n ≠ 9)
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86_64.tonelliPowers c).inline s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (tonelliPowerWrites c) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ sv c base t T5 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ rootQ c ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T5) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((rootQ c + 1) / 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hq : rootQ c ≤ c.C.p - 1 := Nat.div_le_self _ _
  have hp := hc.p_ge
  have he : (rootQ c + 1) / 2 < 2 ^ (64 * c.n) := by have := hc.p_lt; omega
  have hqR : rootQ c < 2 ^ (64 * c.n) := by have := hc.p_lt; omega
  change WP isa (.seq (Impl.EcKey.Compressed.X86_64.rootPower c ((rootQ c + 1) / 2) 1).inline
    (.seq (.block (copy c.n (c.sl T5) (c.sl ACC)))
      (Impl.EcKey.Compressed.X86_64.rootPower c (rootQ c) 2).inline)) s _
  refine WP.seq (WP.mono (rootPower_ok hc (by decide) (.inr hn9) he hs hM hB hO)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (rdi_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [EXPP, ACC, PT, TMP]) :
      sv c base s₁ i = sv c base s i := sv_unch U₁ h7 hn hi (rootPower_apart hi hw)
  refine WP.seq (WP.mono (copy_ok c.n hs₁ (sl_le c h7 (by decide)) (sl_le c h7 (by decide))
    (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ≠ T5) : sv c base s₂ i = sv c base s₁ i :=
    O₂.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  have M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.mono (rootPower_ok hc (by decide) (.inl (by decide)) hqR hs₂ M₂
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hB)
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hO))
    fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  have et : sv c base t T5 = sv c base s₂ T5 :=
    sv_unch Ut h7 hn (by decide) (rootPower_apart (by decide) (by decide))
  refine ⟨(k₁.trans (k₂.mono (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [powClob, clob]))).trans kt,
    (U₁.trans O₂.unch).trans Ut, ltt, ?_, ?_, ?_⟩
  · rw [et]
    change wordsVal s₂.mem base (c.sl T5) c.n < _
    rw [v₂]; exact lt₁
  · rw [vt, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
  · rw [et]
    change toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl T5) c.n) = _
    rw [v₂]; exact v₁

end VG.Proof.EcKey.Compressed.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/DescentLoop.lean`, which only this module imported.
section

/-! # The P-224 machine loop computes the functional root descent -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Impl.EcKey.Compressed (rootDescent)

structure DescentInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  counter : word s.mem base (c.sl T2) = BitVec.ofNat 64 j
  keep : KeepRegs (powClob c.n) s₀ s
  unch : Unch base (slW c roundSlots) s₀.mem s.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  val : rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) =
    rootDescent count (fieldAt c base s₀ ACC) (fieldAt c base s₀ T0) (fieldAt c base s₀ T1)

theorem descentLoop_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {count : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hword : word s.mem base (c.sl T2) = BitVec.ofNat 64 count) :
    WP isa (.loop (Impl.EcKey.Compressed.X86_64.descentRound c).inline .ne) s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (slW c roundSlots) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ fieldAt c base t ACC =
        rootDescent count (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  apply countLoop_ok (Inv := fun j t => DescentInv c base count s t j) (n := count)
  · intro j t hj hjc I
    refine WP.mono (descentRound_ok hc I.scr I.mod I.lt I.one hj (by omega) I.counter)
      fun u R => ?_
    have M : ModOkW c.MP' size c.C.p u.mem base := modP_of hc (by
      rw [sv_unch R.unch h7 hn (by decide) (apart_slW (by decide : MP ∉ roundSlots))]
      exact I.mod.val)
    have one : sv c base u ONEP = 2 ^ (64 * c.n) % c.C.p := by
      rw [sv]
      rw [sv_unch R.unch h7 hn (by decide) (apart_slW (by decide : ONEP ∉ roundSlots))]
      exact I.one
    exact ⟨⟨R.scr, M, one, R.counter, I.keep.trans R.keep, unch_same I.unch R.unch,
      R.lt, R.descent.trans I.val⟩, R.zf⟩
  · intro t I
    exact ⟨I.keep, I.unch, I.lt _ (by simp), I.val⟩
  · exact hcount
  · exact ⟨hs, hM, hOne, hword, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, hlt, rfl⟩

end VG.Proof.EcKey.Compressed.X86_64
end

end

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
