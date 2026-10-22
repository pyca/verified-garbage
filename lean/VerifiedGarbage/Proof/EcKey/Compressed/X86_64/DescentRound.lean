module

import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DescentPower
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DescentChoose
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.DescentUpdate
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Counter
import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Frame
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed

/-! # One machine round refines the functional P-224 root descent -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (W0)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Impl.EcKey.Compressed (rootDescent)

def roundSlots : List Nat := [T3, W0, T4, TMP, ACC, T0, T1, T2]

abbrev fieldAt (c : Cfg) (base : Addr) (s : State) (i : Nat) :=
  toM c.C.p (2 ^ (64 * c.n)) (sv c base s i)

structure DescentRoundPost (c : Cfg) (base : Addr) (j : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (powClob c.n) s s'
  unch : Unch base (slW c roundSlots) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  counter : word s'.mem base (c.sl T2) = BitVec.ofNat 64 (j - 1)
  zf : s'.zf = some (decide (j - 1 = 0))
  descent : rootDescent (j - 1) (fieldAt c base s' ACC) (fieldAt c base s' T0) (fieldAt c base s' T1) =
    rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1)

theorem descentRound_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : word s.mem base (c.sl T2) = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.X86_64.descentRound c).inline s (DescentRoundPost c base j s) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  change WP isa (.seq (Impl.EcKey.Compressed.X86_64.descentPower c).inline
    (.seq (.block (Impl.EcKey.Compressed.X86_64.descentChoose c))
      (.seq (Impl.Weierstrass.X86_64.fprogB c.MP' (Impl.EcKey.Compressed.X86_64.descentOps c)).inline
        (.block (Impl.EcKey.Compressed.X86_64.descentCounter c))))) s _
  refine WP.seq (WP.mono (descentPower_ok hc hs hM (hlt _ (by simp)) hj hj' hword)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (rdi_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [T3, TMP]) : sv c base s₁ i = sv c base s i :=
    sv_unch U₁ h7 hn hi (apart_slW hw)
  have M₁ : ModOkW c.MP' size c.C.p s₁.mem base := modP_of hc (by
    change sv c base s₁ MP = _
    rw [e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.seq (WP.mono (descentChoose_ok hc hs₁ M₁ lt₁
    (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hOne)) fun s₂ ⟨k₂, U₂, lt₂, v₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (rdi_not_clob _)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ∉ [W0, T4, TMP]) : sv c base s₂ i = sv c base s₁ i :=
    sv_unch U₂ h7 hn hi (apart_slW hw)
  have M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide)]; exact M₁.val)
  have b₂ : fieldAt c base s₂ T4 =
      if fieldAt c base s T0 ^ (2 ^ (j - 1)) = 1 then 1 else fieldAt c base s T1 := by
    unfold fieldAt
    rw [v₂, v₁, e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (descentUpdate_ok hc hs₂ M₂ (by
    intro i hi
    have sub : ∀ i ∈ descentFields, i ∈ [ACC, T0, T1] ∨ i = T4 := by decide
    rcases sub i hi with h | rfl
    · have hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i h
      have hn₁ : i ∉ [T3, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [T3, TMP]) i h
      have hn₂ : i ∉ [W0, T4, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [W0, T4, TMP]) i h
      rw [e₂ hi45 hn₂, e₁ hi45 hn₁]; exact hlt i h
    · exact lt₂)) fun s₃ V => ?_)
  have U₁₂ := unch_same (slots_widen U₁ (by decide : ∀ i ∈ [T3, TMP], i ∈ roundSlots))
    (slots_widen U₂ (by decide : ∀ i ∈ [W0, T4, TMP], i ∈ roundSlots))
  have U₁₂₃ := unch_same U₁₂ (slots_widen V.unch (by decide : ∀ i ∈ descentWritten, i ∈ roundSlots))
  have w₃ : word s₃.mem base (c.sl T2) = BitVec.ofNat 64 j := by
    have U : Unch base (slW c [T3, W0, T4, TMP, ACC, T0, T1]) s.mem s₃.mem :=
      unch_same (unch_same (slots_widen U₁ (by decide)) (slots_widen U₂ (by decide)))
        (slots_widen V.unch (by decide))
    rw [U.word (fun w hw => by
      have := apart_slW (c := c) (by decide : T2 ∉ [T3, W0, T4, TMP, ACC, T0, T1]) w hw
      omega) (by have := sl_le c h7 (i := T2) (by decide); omega), hword]
  refine WP.mono (descentCounter_ok V.scr (by have := sl_le c h7 (i := T2) (by decide); omega)
    hj (by omega) w₃) fun s₄ ⟨word₄, zf₄, k₄, O₄⟩ => ?_
  have e₄ {i : Nat} (hi : i < 45) (hw : i ≠ T2) : sv c base s₄ i = sv c base s₃ i :=
    O₄.wordsVal (by have := sl_apart c hw; omega) (by have := sl_le c h7 hi; omega)
  refine ⟨V.scr.of_keepRegs k₄ (by decide), ?_,
    unch_same U₁₂₃ (slot_frame (by decide : T2 ∈ roundSlots) (by omega) O₄), ?_, word₄, zf₄, ?_⟩
  · exact ((k₁.trans (k₂.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (V.keep.mono (fun _ h => List.mem_cons_of_mem _ h))).trans (k₄.mono (by simp [powClob]))
  · intro i hi
    have hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i hi
    have hn₂ : i ≠ T2 := (by decide : ∀ i ∈ [ACC, T0, T1], i ≠ T2) i hi
    rw [e₄ hi45 hn₂]; exact V.lt i hi
  · have r₄ : fieldAt c base s₄ ACC = fieldAt c base s ACC * fieldAt c base s₂ T4 := by
      rw [fieldAt, e₄ (by decide) (by decide), V.r, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    have t₄ : fieldAt c base s₄ T0 = fieldAt c base s T0 * (fieldAt c base s₂ T4 * fieldAt c base s₂ T4) := by
      rw [fieldAt, e₄ (by decide) (by decide), V.t, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    have c₄ : fieldAt c base s₄ T1 = fieldAt c base s T1 * fieldAt c base s T1 := by
      rw [fieldAt, e₄ (by decide) (by decide), V.c, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    conv_rhs => rw [show j = j - 1 + 1 by omega, rootDescent]
    simp only [pow_eq_npow]
    rw [r₄, t₄, c₄, b₂]

end VG.Proof.EcKey.Compressed.X86_64
