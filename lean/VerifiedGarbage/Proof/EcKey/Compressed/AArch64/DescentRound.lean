module

import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DescentPower
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DescentChoose
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.DescentUpdate
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Counter
import VerifiedGarbage.Proof.EcKey.Compressed.AArch64.Frame
import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdh.AArch64.Validate
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed

/-! # One machine round refines the functional P-224 root descent -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Impl.Ecdh.AArch64 (W0)
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.EcKey.Compressed (rootDescent)

def roundSlots : List Nat := [T3, W0, T4, TMP, ACC, T0, T1]

abbrev fieldAt (c : Cfg) (base : Addr) (s : State) (i : Nat) :=
  toM c.C.p (2 ^ (64 * c.n)) (sv c base s i)

structure DescentBodyPost (c : Cfg) (base : Addr) (j : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (powClob c.n) s s'
  unch : Unch base (slW c roundSlots) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  descent : rootDescent (j - 1) (fieldAt c base s' ACC) (fieldAt c base s' T0) (fieldAt c base s' T1) =
    rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1)

theorem descentBody_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.AArch64.descentBody c) s (DescentBodyPost c base j s) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  change WP isa (.seq (Impl.EcKey.Compressed.AArch64.descentPower c)
    (.seq (.block (Impl.EcKey.Compressed.AArch64.descentChoose c))
      (Impl.Weierstrass.AArch64.fprogB c.MP' (Impl.EcKey.Compressed.AArch64.descentOps c)))) s _
  refine WP.seq (WP.mono (descentPower_ok hc hs hM (hlt _ (by simp)) hj hj' hword)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (x0_not_powClob _)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [T3, TMP]) : sv c base s₁ i = sv c base s i :=
    sv_unch U₁ h7 hn hi (apart_slW hw)
  have M₁ : ModOkA c.MP' size c.C.p s₁.mem base := modP_of hc (by
    change sv c base s₁ MP = _
    rw [e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.seq (WP.mono (descentChoose_ok hc hs₁ M₁ lt₁
    (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hOne)) fun s₂ ⟨k₂, U₂, lt₂, v₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by intro h; exact (by decide : VG.AArch64.Reg.x0 ∉ VG.Proof.Mont.AArch64.clobAll) (VG.Proof.Mont.AArch64.mem_clobAll h))
  have e₂ {i : Nat} (hi : i < 45) (hw : i ∉ [W0, T4, TMP]) : sv c base s₂ i = sv c base s₁ i :=
    sv_unch U₂ h7 hn hi (apart_slW hw)
  have M₂ : ModOkA c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide)]; exact M₁.val)
  have b₂ : fieldAt c base s₂ T4 =
      if fieldAt c base s T0 ^ (2 ^ (j - 1)) = 1 then 1 else fieldAt c base s T1 := by
    unfold fieldAt
    rw [v₂, v₁, e₁ (by decide) (by decide)]
  refine WP.mono (descentUpdate_ok hc hs₂ M₂ (by
    intro i hi
    have sub : ∀ i ∈ descentFields, i ∈ [ACC, T0, T1] ∨ i = T4 := by decide
    rcases sub i hi with h | rfl
    · have hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i h
      have hn₁ : i ∉ [T3, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [T3, TMP]) i h
      have hn₂ : i ∉ [W0, T4, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [W0, T4, TMP]) i h
      rw [e₂ hi45 hn₂, e₁ hi45 hn₁]; exact hlt i h
    · exact lt₂)) fun s₃ V => ?_
  have U₁₂ := unch_same (slots_widen U₁ (by decide : ∀ i ∈ [T3, TMP], i ∈ roundSlots))
    (slots_widen U₂ (by decide : ∀ i ∈ [W0, T4, TMP], i ∈ roundSlots))
  have U₁₂₃ := unch_same U₁₂ (slots_widen V.unch (by decide : ∀ i ∈ descentWritten, i ∈ roundSlots))
  refine ⟨V.scr, ?_, U₁₂₃, V.lt, ?_⟩
  · exact (k₁.trans (k₂.mono (fun _ h => List.mem_cons_of_mem _ h))).trans
      (V.keep.mono (fun _ h => List.mem_cons_of_mem _ h))
  · have r₄ : fieldAt c base s₃ ACC = fieldAt c base s ACC * fieldAt c base s₂ T4 := by
      rw [fieldAt, V.r, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    have t₄ : fieldAt c base s₃ T0 = fieldAt c base s T0 * (fieldAt c base s₂ T4 * fieldAt c base s₂ T4) := by
      rw [fieldAt, V.t, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    have c₄ : fieldAt c base s₃ T1 = fieldAt c base s T1 * fieldAt c base s T1 := by
      rw [fieldAt, V.c, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    conv_rhs => rw [show j = j - 1 + 1 by omega, rootDescent]
    simp only [pow_eq_npow]
    rw [r₄, t₄, c₄, b₂]

 structure DescentRoundPost (c : Cfg) (base : Addr) (j : Nat) (s t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (powClob c.n) s t
  unch : Unch base (slW c roundSlots) s.mem t.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base t i < c.C.p
  counter : t.gpr .x19 = BitVec.ofNat 64 (j - 1)
  descent : rootDescent (j - 1) (fieldAt c base t ACC) (fieldAt c base t T0) (fieldAt c base t T1) =
    rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1)

 theorem descentRound_ok {c : Cfg} (hc : BaseCfgOk c)
    (hV : ∀ i ∈ instrs (Impl.EcKey.Compressed.AArch64.descentBody c), vdstOf i ≠ some .v27)
    {base : Addr} {s : State} {j : Nat} (hs : Scr s base size)
    (hM : ModOkA c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31) (hcounter : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (Impl.EcKey.Compressed.AArch64.descentRound c) s (DescentRoundPost c base j s) := by
  refine WP.seq (WP.mono (saveCounter_ok s) fun u ⟨g, m, rd, wr, sp, saved⟩ => ?_)
  have hs₁ : Scr u base size := ⟨by rw [g]; exact hs.x0, by rw [wr]; exact hs.wr, hs.nowrap, hs.enc⟩
  have e (i : Nat) : sv c base u i = sv c base s i := by rw [sv, m]
  have M₁ : ModOkA c.MP' size c.C.p u.mem base := by rw [m]; exact hM
  refine WP.seq (WP.mono (VG.Proof.Ecdh.AArch64.WP.keepV hV
    (descentBody_ok hc hs₁ M₁ (by intro i hi; rw [e]; exact hlt i hi)
      (by rw [e]; exact hOne) hj hj' (by rw [g]; exact hcounter)))
    fun v ⟨R, hv⟩ => ?_)
  have counter : laneOf v .v27 0 = BitVec.ofNat 64 j := by
    change (v.v .v27).extractLsb' (64 * 0) 64 = _
    rw [hv]
    exact saved.trans hcounter
  refine WP.mono (descentCounter_ok hj (by omega) counter) fun t ⟨ct, K⟩ => ?_
  refine ⟨R.scr.of_keeps K (by decide), ?_, ?_, ?_, ct, ?_⟩
  · have K₁ : KeepRegs (powClob c.n) s u := ⟨fun r _ => congrFun g r, rd, wr, sp⟩
    exact (K₁.trans R.keep).trans ((Keeps.regs K).mono (by simp [powClob]))
  · simpa only [K.mem, m] using R.unch
  · intro i hi
    change wordsVal t.mem _ _ _ < _
    rw [K.mem]
    exact R.lt i hi
  · simpa only [fieldAt, sv, K.mem, m] using R.descent

end VG.Proof.EcKey.Compressed.AArch64
