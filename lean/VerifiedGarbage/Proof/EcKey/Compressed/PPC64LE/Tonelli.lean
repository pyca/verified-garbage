module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DescentLoop
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.RootPow
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# SEC 1 point decompression on PPC64LE: P-224's candidate

`candidateTonelli_correct`: for `p ≢ 3 mod 4` (P-224), the candidate is
Tonelli and Shanks's root (`rootTonelli`, with `p - 1 = q 2⁹⁶` and the
nonresidue 11): `W2^((q+1)/2)` and `W2^q` (`tonelliPowers_ok`), the
descent's start (`tonelliSetup_ok`), and its 95 rounds (`descentLoop_ok`).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (W0 W2)
open VG.Impl.EcKey.Compressed.PPC64LE (rootQ)

variable {c : Cfg}

/-- `T5 = W2^((q+1)/2)` and `ACC = W2^q`. -/
theorem tonelliPowers_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hB : sv c base s W2 < c.C.p) (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.tonelliPowers c) s fun s' =>
      WsReg s' base ∧ Rk powClob s s' ∧ Unch base (candW c) s.mem s'.mem ∧
      sv c base s' T5 < c.C.p ∧ sv c base s' ACC < c.C.p ∧
      fieldAt c base s' T5 = fieldAt c base s W2 ^ ((rootQ c + 1) / 2) ∧
      fieldAt c base s' ACC = fieldAt c base s W2 ^ rootQ c := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hpl := hc.p_lt
  have hq : rootQ c < 2 ^ (64 * c.n) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hq' : (rootQ c + 1) / 2 < 2 ^ (64 * c.n) := by omega
  have hT5 := sl_le c h7 (i := T5) (by decide)
  have hA := sl_le c h7 (i := ACC) (by decide)
  change WP isa (.seq (Impl.EcKey.Compressed.PPC64LE.rootPower c ((rootQ c + 1) / 2) 1)
    (.seq (.block (copy c.n (c.sl T5) (c.sl ACC))) (Impl.EcKey.Compressed.PPC64LE.rootPower c (rootQ c) 2))) s _
  have ap : ∀ {i j}, i < 45 → i ∉ [EXPP, ACC, PT] → j < 3 →
      ∀ w ∈ rootPowerW c j, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hl hj w hw' => by
    simp only [rootPowerW, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact apart_slW (c := c) (l := [EXPP]) (by simp at hl ⊢; exact hl.1) _ (List.mem_singleton_self _)
    · exact apart_tbl h7 hi _ _ (List.mem_singleton_self _)
    · exact apart_slW (c := c) (l := [ACC]) (by simp at hl ⊢; exact hl.2.1) _ (List.mem_singleton_self _)
    · exact apart_slW (c := c) (l := [PT]) (by simp at hl ⊢; exact hl.2.2) _ (List.mem_singleton_self _)
    · exact apart_own h7 hi _ (List.mem_singleton_self _)
  refine WP.seq (WP.mono (rootPower_ok hc (by decide) hq' hw hB hO) fun s₁ ⟨hw₁, k₁, U₁, lt₁, v₁⟩ => ?_)
  have e₁ : ∀ {i}, i < 45 → i ∉ [EXPP, ACC, PT] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁ h7 hn hi (ap hi hl (by decide))
  refine WP.seq (WP.mono (copy_ok c.n hw₁.ws hw₁.at3 (o := c.sl T5) (a := c.sl ACC) (sl_al c _) (sl_al c _)
    (by omega) (by omega) (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have hw₂ := hw₁.of_kp k₂
  have f₂ : ∀ {i}, i < 45 → i ≠ T5 → sv c base s₂ i = sv c base s₁ i := fun hi h =>
    O₂.wordsVal (sl_apart c h) (by have := sl_le c h7 hi; omega)
  refine WP.mono (rootPower_ok hc (by decide) hq hw₂
    (by rw [f₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hB)
    (by rw [f₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hO)) fun s₃ ⟨hw₃, k₃, U₃, lt₃, v₃⟩ => ?_
  have t5₃ : sv c base s₃ T5 = sv c base s₁ ACC := by
    exact (sv_unch U₃ h7 hn (i := T5) (by decide) (ap (by decide) (by decide) (by decide))).trans e₂
  refine ⟨hw₃, (k₁.trans (k₂.rk (rs' := powClob))).trans k₃, ?_, by rw [t5₃]; exact lt₁, lt₃, ?_, ?_⟩
  · refine ((U₁.trans O₂.unch).trans U₃).mono fun w hw' => ?_
    simp only [rootPowerW, candW, slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw' ⊢
    grind
  · show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ T5) = _; rw [t5₃]; exact v₁
  · show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) = _
    rw [v₃, f₂ (by decide) (by decide), e₁ (by decide) (by decide)]

/-- `T0 = ACC`, `ACC = T5`, `T1 = 11^q` (in Montgomery form) and the round
counter 95. -/
theorem tonelliSetup_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (h5 : sv c base s T5 < c.C.p) (hA : sv c base s ACC < c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.tonelliSetup c)) s fun t =>
      WsReg t base ∧ t.gpr .r31 = ctr 95 0 ∧ Kp [.r4, .r11, .r31] s t ∧
      Unch base (slW c [T0, ACC, T1]) s.mem t.mem ∧
      (∀ i ∈ [ACC, T0, T1], sv c base t i < c.C.p) ∧
      fieldAt c base t ACC = fieldAt c base s T5 ∧ fieldAt c base t T0 = fieldAt c base s ACC ∧
      fieldAt c base t T1 = Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c) := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hp3 := hc.p_ge
  have hT0 := sl_le c h7 (i := T0) (by decide)
  have hA' := sl_le c h7 (i := ACC) (by decide)
  have hT5 := sl_le c h7 (i := T5) (by decide)
  have hT1 := sl_le c h7 (i := T1) (by decide)
  rw [Impl.EcKey.Compressed.PPC64LE.tonelliSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok c.n hw.ws hw.at3 (o := c.sl T0) (a := c.sl ACC) (sl_al c _) (sl_al c _)
    (by omega) (by omega) (by have := sl_apart c (i := T0) (j := ACC) (by decide); omega)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n (k₁.ws hw.ws) (k₁.at hw.at3) (o := c.sl ACC) (a := c.sl T5) (sl_al c _) (sl_al c _)
    (by omega) (by omega) (by have := sl_apart c (i := ACC) (j := T5) (by decide); omega)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  let z := Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)
  have zR : c.mont z.val < 2 ^ (64 * c.n) := Nat.lt_trans (Nat.mod_lt _ (by omega)) hc.p_lt
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok ((k₁.trans k₂).ws hw.ws) ((k₁.trans k₂).at hw.at3) (o := c.sl T1) (by omega) zR)
    fun s₃ ⟨O₃, v₃, k₃⟩ => ?_
  rw [← wordsVal_eq_val32] at v₃
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step (exec_lsl (by decide)) (WP.block_nil ?_)
  have K : Kp [.r4, .r11, .r31] s ((s₃.write .r31 (BitVec.ofNat 64 95)).write .r31
      ((s₃.write .r31 (BitVec.ofNat 64 95)).gpr .r31 <<< 32)) :=
    (((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans
      ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))
  have e₃ : ∀ {i}, i < 45 → i ≠ T1 → sv c base s₃ i = sv c base s₂ i := fun hi h =>
    O₃.wordsVal (sl_apart c h) (by have := sl_le c h7 hi; omega)
  have r₃ : sv c base s₃ ACC = sv c base s T5 := by
    rw [e₃ (by decide) (by decide)]; show wordsVal s₂.mem base (c.sl ACC) c.n = _; rw [v₂]
    exact O₁.wordsVal (sl_apart c (i := T5) (j := T0) (by decide)) (by omega)
  have t₃ : sv c base s₃ T0 = sv c base s ACC := by
    rw [e₃ (by decide) (by decide)]
    show wordsVal s₂.mem base (c.sl T0) c.n = _
    rw [O₂.wordsVal (sl_apart c (i := T0) (j := ACC) (by decide)) (by omega), v₁]
  have c₃ : sv c base s₃ T1 = c.mont z.val := v₃
  refine ⟨hw.of_kp K, ?_, K, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [write_gpr, ite_true]; exact ctr_init 95
  · simp only [write_mem]
    refine ((O₁.unch.trans O₂.unch).trans O₃.unch).mono fun w hw' => ?_
    simp only [slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw' ⊢
    grind
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show wordsVal s₃.mem base (c.sl i) c.n < _
    rcases hi with rfl | rfl | rfl
    · rw [show wordsVal s₃.mem base (c.sl ACC) c.n = sv c base s₃ ACC from rfl, r₃]; exact h5
    · rw [show wordsVal s₃.mem base (c.sl T0) c.n = sv c base s₃ T0 from rfl, t₃]; exact hA
    · rw [show wordsVal s₃.mem base (c.sl T1) c.n = sv c base s₃ T1 from rfl, c₃]; exact Nat.mod_lt _ (by omega)
  · show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) = _; rw [r₃]
  · show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ T0) = _; rw [t₃]
  · show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ T1) = _
    rw [c₃, toM_cmont hc]
    exact Fin.ext (Nat.mod_eq_of_lt z.isLt)

/-- For `p ≢ 3 mod 4`, the candidate is Tonelli and Shanks's root, for
`p - 1 = q 2⁹⁶` and the nonresidue 11. -/
theorem candidateTonelli_correct (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3) (hq : 0 < rootQ c) :
    CandidateCorrect c (fun a => Impl.EcKey.Compressed.rootTonelli a (rootQ c) 96 (Fin.ofNat c.C.p 11)) := by
  intro base s hw hB hO
  have h7 := hc.n10
  have hn := hw.nowrap
  simp only [Impl.EcKey.Compressed.PPC64LE.rootCandidate, hp, ↓reduceIte]
  change WP isa (.seq (Impl.EcKey.Compressed.PPC64LE.tonelliPowers c)
    (.seq (.block (Impl.EcKey.Compressed.PPC64LE.tonelliSetup c))
      (.loop (Impl.EcKey.Compressed.PPC64LE.descentRound c) (.nonzero .d .r31)))) s _
  refine WP.seq (WP.mono (tonelliPowers_ok hc hw hB hO) fun s₁ ⟨hw₁, k₁, U₁, lt5₁, ltA₁, r₁, t₁⟩ => ?_)
  refine WP.seq (WP.mono (tonelliSetup_ok hc hw₁ lt5₁ ltA₁) fun s₂ ⟨hw₂, r31₂, k₂, U₂, lt₂, r₂, t₂, c₂⟩ => ?_)
  have U₁₂ : Unch base (candW c) s.mem s₂.mem := (U₁.trans U₂).mono fun w hw' => by
    simp only [candW, slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw' ⊢
    grind
  have one₂ : sv c base s₂ ONEP = 2 ^ (64 * c.n) % c.C.p := by
    exact (sv_unch U₁₂ h7 hn (i := ONEP) (by decide) (apart_candW h7 (by decide) (by decide))).trans hO
  refine WP.mono (descentLoop_ok hc hw₂ (count := 95) (by decide) (by decide) r31₂ lt₂ one₂)
    fun t ⟨hwt, kt, Ut, ltt, vt⟩ => ⟨hwt, (k₁.trans (k₂.rk (rs' := powClob))).trans kt, ?_, ltt, ?_⟩
  · refine (U₁₂.trans Ut).mono fun w hw' => ?_
    simp only [roundW, candW, slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw' ⊢
    grind
  · change fieldAt c base t ACC = _
    rw [vt, r₂, t₂, c₂, r₁, t₁, rootTonelli_eq_descent _ _ _ _ hq]
    simp only [pow_eq_npow]

end VG.Proof.EcKey.Compressed.PPC64LE
