module

public import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Candidate
public import VerifiedGarbage.Impl.EcKey.Compressed.Root

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DescentRound
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.RootPow
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
/-! # P-224's machine candidate refines the shared root algorithm -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/TonelliPowers.lean`, which only this module imported.
section

/-! # The two fixed powers that initialize P-224's descent -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (W2)
open VG.Impl.EcKey.Compressed.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

 abbrev tonelliPowerWrites (c : Cfg) := rootWrites c ++ slW c [T5] ++ rootWrites c

 theorem tonelliPowers_ok {c : Cfg} (hc : BaseCfgOk c)
    (hR : ChainOk (rootChain c ((rootQ c + 1) / 2)) ((rootQ c + 1) / 2))
    (hQ : ChainOk (rootChain c (rootQ c)) (rootQ c))
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p) :
    WP isa (tonelliPowers c) s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (tonelliPowerWrites c) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ sv c base t T5 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ rootQ c ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T5) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((rootQ c + 1) / 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  change WP isa (.seq (rootPower c ((rootQ c + 1) / 2))
    (.seq (.block (copy c.n (c.sl T5) (c.sl ACC))) (rootPower c (rootQ c)))) s _
  refine WP.seq (WP.mono (rootPower_ok hc hR hs hM hB)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (x0_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ rootSlots) :
      sv c base s₁ i = sv c base s i := sv_unch U₁ h7 hn hi (apart_rootWrites hc hi hw)
  refine WP.seq (WP.mono (copy_ok c.n hs₁ (sl_le c h7 (by decide)) (sl_le c h7 (by decide))
    (sl_mod8 c T5) (sl_mod8 c ACC)
    (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ≠ T5) : sv c base s₂ i = sv c base s₁ i :=
    O₂.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  have M₂ : ModOkA c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.mono (rootPower_ok hc hQ hs₂ M₂
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hB))
    fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  have et : sv c base t T5 = sv c base s₂ T5 :=
    sv_unch Ut h7 hn (by decide) (apart_rootWrites hc (by decide) (by decide))
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

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/TonelliSetup.lean`, which only this module imported.
section

/-! # Initialize P-224's descent from its two computed powers -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed.AArch64 (rootQ)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem tonelliSetup_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hr : sv c base s T5 < c.C.p) (ht : sv c base s ACC < c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.tonelliSetup c)) s fun t =>
      KeepRegs [.x1, .x19] s t ∧ Unch base (slW c [T0, ACC, T1]) s.mem t.mem ∧
      (∀ i ∈ [ACC, T0, T1], sv c base t i < c.C.p) ∧
      t.gpr .x19 = BitVec.ofNat 64 95 ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T5) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T0) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T1) =
        Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  have hT0 := sl_le c h7 (i := T0) (by decide)
  have hACC := sl_le c h7 (i := ACC) (by decide)
  have hT5 := sl_le c h7 (i := T5) (by decide)
  have hT1 := sl_le c h7 (i := T1) (by decide)
  rw [Impl.EcKey.Compressed.AArch64.tonelliSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs hT0 hACC (sl_mod8 c T0) (sl_mod8 c ACC)
    (by have := sl_apart c (i := T0) (j := ACC) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n hs₁ hACC hT5 (sl_mod8 c ACC) (sl_mod8 c T5)
    (by have := sl_apart c (i := ACC) (j := T5) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have r₂ : sv c base s₂ ACC = sv c base s T5 := by
    rw [sv, v₂, O₁.wordsVal (sl_apart c (i := T5) (j := T0) (by decide)) (by omega)]
  have t₂ : sv c base s₂ T0 = sv c base s ACC := by
    rw [sv, O₂.wordsVal (sl_apart c (i := T0) (j := ACC) (by decide)) (by omega), v₁]
  let z := Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)
  have zR : c.mont z.val < 2 ^ (64 * c.n) := Nat.lt_trans
    (Nat.mod_lt _ (by have := hc.p_ge; omega)) hc.p_lt
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ hT1 (sl_mod8 c T1) zR) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (setCounter_ok s₃ (j := 95) (by decide)) fun t ⟨v₄, k₄⟩ => ?_
  have e₃ {i : Nat} (hi : i < 45) (hw : i ≠ T1) : sv c base s₃ i = sv c base s₂ i :=
    O₃.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega)
  have e₄ (i : Nat) : sv c base t i = sv c base s₃ i := by rw [sv, k₄.mem]
  have r₄ : sv c base t ACC = sv c base s T5 := by
    rw [e₄, e₃ (by decide) (by decide), r₂]
  have t₄ : sv c base t T0 = sv c base s ACC := by
    rw [e₄, e₃ (by decide) (by decide), t₂]
  have c₄ : sv c base t T1 = c.mont z.val := by
    rw [e₄]; exact v₃
  refine ⟨(((k₁.trans k₂).trans k₃).mono (by sub_regs)).trans
      ((Keeps.regs k₄).mono (by sub_regs)), ?_, ?_, ?_, by rw [r₄], by rw [t₄], ?_⟩
  · rw [k₄.mem]
    exact unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₃)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [r₄]; exact hr
    · rw [t₄]; exact ht
    · rw [c₄]; exact Nat.mod_lt _ (by have := hc.p_ge; omega)
  · exact v₄
  · rw [c₄, toM_cmont hc]
    exact Fin.ext (Nat.mod_eq_of_lt z.isLt)

end VG.Proof.EcKey.Compressed.AArch64
end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/AArch64/DescentLoop.lean`, which only this module imported.
section

/-! # The P-224 machine loop computes the functional root descent -/

section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed (rootDescent)

structure DescentInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  mod : ModOkA c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  keep : KeepRegs (powClob c.n) s₀ s
  unch : Unch base (slW c roundSlots) s₀.mem s.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  val : rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) =
    rootDescent count (fieldAt c base s₀ ACC) (fieldAt c base s₀ T0) (fieldAt c base s₀ T1)

theorem descentLoop_ok {c : Cfg} (hc : BaseCfgOk c)
    (hV : ∀ i ∈ instrs (Impl.EcKey.Compressed.AArch64.descentBody c), vdstOf i ≠ some .v27) {base : Addr} {s : State} {count : Nat}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hword : s.gpr .x19 = BitVec.ofNat 64 count) :
    WP isa (.loop (Impl.EcKey.Compressed.AArch64.descentRound c) (.nonzero .x .x19)) s fun t =>
      KeepRegs (powClob c.n) s t ∧ Unch base (slW c roundSlots) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ fieldAt c base t ACC =
        rootDescent count (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  apply countLoop_ok (Inv := fun j t => DescentInv c base count s t j) (by omega) (n := count)
  · intro j t hj hjc I
    refine WP.mono (descentRound_ok hc hV I.scr I.mod I.lt I.one hj (by omega) I.counter)
      fun u R => ?_
    have M : ModOkA c.MP' size c.C.p u.mem base := modP_of hc (by
      rw [sv_unch R.unch h7 hn (by decide) (apart_slW (by decide : MP ∉ roundSlots))]
      exact I.mod.val)
    have one : sv c base u ONEP = 2 ^ (64 * c.n) % c.C.p := by
      rw [sv]
      rw [sv_unch R.unch h7 hn (by decide) (apart_slW (by decide : ONEP ∉ roundSlots))]
      exact I.one
    exact ⟨⟨R.scr, M, one, R.counter, I.keep.trans R.keep, unch_same I.unch R.unch,
      R.lt, R.descent.trans I.val⟩, R.counter⟩
  · intro t I
    exact ⟨I.keep, I.unch, I.lt _ (by simp), I.val⟩
  · exact hcount
  · exact ⟨hs, hM, hOne, hword, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Unch.refl _ _ _, hlt, rfl⟩

end VG.Proof.EcKey.Compressed.AArch64
end

end

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
