module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Main
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Descent
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Poly
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
import VerifiedGarbage.Proof.Mont.PPC64LE.Const
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.P224.Sqrt
public import VerifiedGarbage.Impl.EcKey.Compressed.P224.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Main
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.DecompressMain
meta import VerifiedGarbage.Impl.EcKey.Compressed.P224.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.P224.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
public import VerifiedGarbage.Spec.P224

/-! ### `EcKey.Compressed.PPC64LE.Tonelli`, which only this module used -/

section

/-! ### `EcKey.Compressed.PPC64LE.DescentLoop`, which only this module used -/

section

/-!
# SEC 1 point decompression on PPC64LE: P-224's descent, its rounds

`descentUpdate_ok`: `r = r b`, `t = t b²`, `c = c²`; `descentRound_ok`: a
round, as `rootDescent`'s step; `descentLoop_ok`: the rounds, from `count`
in `r31`'s high word down to 0, compute `rootDescent count`.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (W0)
open VG.Impl.EcKey.Compressed (rootDescent)

variable {c : Cfg}

/-! ## `r = r b`, `t = t b²`, `c = c²` -/

/-- `descentOps` on slot numbers. -/
def descentN : List FOp := [.mul ACC ACC T4, .mul T4 T4 T4, .mul T0 T0 T4, .mul T1 T1 T1]

theorem descentOps_eq (c : Cfg) :
    fprog c.SP (Impl.EcKey.Compressed.PPC64LE.descentOps c) = Point.fprogR c.sl c.SP descentN := rfl

theorem descentN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps descentN e ACC = e ACC * e T4 ∧
    runOps descentN e T0 = e T0 * (e T4 * e T4) ∧
    runOps descentN e T1 = e T1 * e T1 := by
  simp only [descentN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [ACC, T0, T1, T4, Nat.reduceEqDiff, ↓reduceIte, and_self]

theorem descentN_reads : readsOk descentN [ACC, T0, T1, T4] = true := by decide

theorem descentN_ids : ∀ op ∈ descentN, op.out ∈ [ACC, T4, T0, T1] ∧ ∀ x ∈ op.out :: op.ins, x < 45 := by
  decide

/-- What `descentOps` writes. -/
abbrev descentW (c : Cfg) : List (Nat × Nat) := slW c [ACC, T4, T0, T1] ++ [(own c.n, 64 * c.n)]

theorem descentUpdate_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hlt : ∀ i ∈ [ACC, T0, T1, T4], sv c base s i < c.C.p) :
    WP isa (fprog c.SP (Impl.EcKey.Compressed.PPC64LE.descentOps c)) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (descentW c) s.mem s'.mem ∧
      (∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p) ∧
      fieldAt c base s' ACC = fieldAt c base s ACC * fieldAt c base s T4 ∧
      fieldAt c base s' T0 = fieldAt c base s T0 * (fieldAt c base s T4 * fieldAt c base s T4) ∧
      fieldAt c base s' T1 = fieldAt c base s T1 * fieldAt c base s T1 := by
  rw [descentOps_eq]
  refine WP.mono (ops_core hc hw descentN_ids (by decide) hlt descentN_reads) fun s' ⟨K, I⟩ => ?_
  obtain hv : ∀ i ∈ [ACC, T0, T1], i ∈ validAfter descentN [ACC, T0, T1, T4] := by decide
  obtain ⟨R, U⟩ := keepR_unch K
  have ⟨r, t, cc⟩ := descentN_run (fun x => toM c.C.p (2 ^ (64 * c.n)) (sv c base s x))
  refine ⟨I.ws, R, U.mono fun w hw' => by
    simp only [descentN, List.map_cons, List.map_nil, FOp.out, slW, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw' ⊢
    grind, fun i hi => I.lt i (hv i hi), ?_, ?_, ?_⟩
  · rw [fieldAt, I.val _ (hv _ (by simp)), r]
  · rw [fieldAt, I.val _ (hv _ (by simp)), t]
  · rw [fieldAt, I.val _ (hv _ (by simp)), cc]

/-! ## A round -/

/-- `j - 1` to `r31`'s high word, through `r4`. -/
theorem descentCounter_ok {s : State} {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 32) (h31 : s.gpr .r31 = ctr j 0) :
    WP isa (.block Impl.EcKey.Compressed.PPC64LE.descentCounter) s fun t =>
      Kp [.r4, .r31] s t ∧ t.gpr .r31 = ctr (j - 1) 0 ∧ t.mem = s.mem := by
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step (exec_lsl (by decide)) ?_
  refine wp_step exec_sub (WP.block_nil ⟨((Kp.write _ _ (rs := [.r4, .r31]) (by decide)).trans
    (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide)), ?_, by simp only [write_mem]⟩)
  simp only [write_gpr, ite_true, reduceCtorEq, ite_false, h31]
  exact ctr_next hj hj'

/-- What a round writes. -/
abbrev roundW (c : Cfg) : List (Nat × Nat) := slW c [T3, W0, T4, ACC, T0, T1] ++ [(own c.n, 64 * c.n)]

theorem roundW_cover {W : List (Nat × Nat)} (h : ∀ w ∈ W, w ∈ roundW c) {base : Addr} {m m' : Mem}
    (U : Unch base W m m') : Unch base (roundW c) m m' := U.mono h

theorem descentRound_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {j : Nat}
    (hj : 1 ≤ j) (hj' : j < 2 ^ 32) (h31 : s.gpr .r31 = ctr j 0)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p) (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.descentRound c) s fun s' =>
      WsReg s' base ∧ s'.gpr .r31 = ctr (j - 1) 0 ∧ Rk powClob s s' ∧ Unch base (roundW c) s.mem s'.mem ∧
      (∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p) ∧
      rootDescent (j - 1) (fieldAt c base s' ACC) (fieldAt c base s' T0) (fieldAt c base s' T1) =
        rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) := by
  have h7 := hc.n10
  have hn := hw.nowrap
  change WP isa (.seq (Impl.EcKey.Compressed.PPC64LE.descentPower c)
    (.seq (Impl.EcKey.Compressed.PPC64LE.descentChoose c)
      (.seq (fprog c.SP (Impl.EcKey.Compressed.PPC64LE.descentOps c))
        (.block Impl.EcKey.Compressed.PPC64LE.descentCounter)))) s _
  refine WP.seq (WP.mono (descentPower_ok hc hw hj hj' h31 (hlt _ (by simp)))
    fun s₁ ⟨hw₁, r31₁, k₁, U₁, lt₁, v₁⟩ => ?_)
  obtain e₁ : ∀ {i}, i < 45 → i ≠ T3 → sv c base s₁ i = sv c base s i := fun hi h =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h)
  refine WP.seq (WP.mono (descentChoose_ok hc hw₁ lt₁ (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hO)) fun s₂ ⟨hw₂, k₂, U₂, lt₂, v₂⟩ => ?_)
  obtain e₂ : ∀ {i}, i < 45 → i ∉ [W0, T4] → sv c base s₂ i = sv c base s₁ i := fun hi h => by
    refine sv_unch U₂ h7 hn hi (apart_append (apart_callW h7 hi (fun h' => h (by simp [h']))) ?_)
    exact apart_slW (c := c) (l := [T4]) (fun h' => h (by simp at h'; simp [h']))
  obtain r31₂ : s₂.gpr .r31 = ctr j 0 := by rw [k₂.gpr _ (by decide), r31₁]
  obtain f₂ : ∀ {i}, i ∈ [ACC, T0, T1] → sv c base s₂ i = sv c base s i := fun hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (descentUpdate_ok hc hw₂ (fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · rw [f₂ (by simp)]; exact hlt _ (by simp)
    · rw [f₂ (by simp)]; exact hlt _ (by simp)
    · rw [f₂ (by simp)]; exact hlt _ (by simp)
    · exact lt₂)) fun s₃ ⟨hw₃, k₃, U₃, lt₃, r₃, t₃, c₃⟩ => ?_)
  obtain r31₃ : s₃.gpr .r31 = ctr j 0 := by rw [k₃.gpr _ (by decide), r31₂]
  refine WP.mono (descentCounter_ok hj hj' r31₃) fun s₄ ⟨K₄, r31₄, m₄⟩ => ?_
  obtain ev : ∀ i, sv c base s₄ i = sv c base s₃ i := fun i => by simp only [sv, m₄]
  refine ⟨hw₃.of_kp K₄, r31₄, ((k₁.trans (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans
    (K₄.rk (rs' := powClob)), ?_, fun i hi => by rw [ev]; exact lt₃ i hi, ?_⟩
  · rw [m₄]
    refine roundW_cover (fun w hw' => ?_) ((U₁.trans U₂).trans U₃)
    simp only [callW, descentW, slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw' ⊢
    grind
  · have b₂ : fieldAt c base s₂ T4 =
        if fieldAt c base s T0 ^ (2 ^ (j - 1)) = 1 then 1 else fieldAt c base s T1 := by
      rw [v₂, v₁, fieldAt, fieldAt, e₁ (by decide) (by decide)]
    obtain ev' : ∀ i, fieldAt c base s₄ i = fieldAt c base s₃ i := fun i => by simp only [fieldAt, ev]
    obtain ff₂ : ∀ {i}, i ∈ [ACC, T0, T1] → fieldAt c base s₂ i = fieldAt c base s i := fun hi => by
      simp only [fieldAt, f₂ hi]
    rw [ev', ev', ev', r₃, t₃, c₃, ff₂ (show ACC ∈ [ACC, T0, T1] by simp), ff₂ (show T0 ∈ [ACC, T0, T1] by simp),
      ff₂ (show T1 ∈ [ACC, T0, T1] by simp)]
    conv => rhs; rw [show j = j - 1 + 1 by omega_arith, rootDescent]
    simp only [pow_eq_npow]
    rw [← b₂]

/-! ## The rounds -/

/-- The rounds' invariant, with `k` rounds left of `count`. -/
structure DescentInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (k : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = ctr k 0
  le : k ≤ count
  rk : Rk powClob s₀ s
  unch : Unch base (roundW c) s₀.mem s.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  val : rootDescent k (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) =
    rootDescent count (fieldAt c base s₀ ACC) (fieldAt c base s₀ T0) (fieldAt c base s₀ T1)

theorem descentLoop_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {count : Nat}
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 32) (h31 : s.gpr .r31 = ctr count 0)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p) (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (.loop (Impl.EcKey.Compressed.PPC64LE.descentRound c) (.nonzero .d .r31)) s fun t =>
      WsReg t base ∧ Rk powClob s t ∧ Unch base (roundW c) s.mem t.mem ∧ sv c base t ACC < c.C.p ∧
      fieldAt c base t ACC =
        rootDescent count (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) := by
  have h7 := hc.n10
  have hn := hw.nowrap
  refine loopBy_ok (Inv := fun k t => DescentInv c base count s t k) (n := count)
    (fun k t I => eval_hi_nonzero (by have := I.le; omega_arith) I.r31) (fun k t hk hkc I => ?_)
    (fun t I => ⟨I.ws, I.rk, I.unch, I.lt _ (by simp), by rw [← I.val]; rfl⟩) hcount
    ⟨hw, h31, Nat.le_refl _, Rk.refl _ _, Unch.refl _ _ _, hlt, hO, rfl⟩
  refine WP.mono (descentRound_ok hc I.ws hk (by omega_arith) I.r31 I.lt I.one)
    fun u ⟨hwu, r31u, ku, Uu, ltu, vu⟩ => ⟨hwu, r31u, by omega_arith, I.rk.trans ku,
      (I.unch.trans Uu).mono fun w hw' => (List.mem_append.mp hw').elim id id, ltu, ?_, vu.trans I.val⟩
  exact (sv_unch Uu h7 hn (i := ONEP) (by decide)
    (apart_append (apart_slW (by decide)) (apart_own h7 (by decide)))).trans I.one

end VG.Proof.EcKey.Compressed.PPC64LE

end

end


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
  obtain hq : rootQ c < 2 ^ (64 * c.n) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith)
  obtain hq' : (rootQ c + 1) / 2 < 2 ^ (64 * c.n) := by omega_arith
  obtain hT5 := sl_le c h7 (i := T5) (by decide)
  obtain hA := sl_le c h7 (i := ACC) (by decide)
  change WP isa (.seq (Impl.EcKey.Compressed.PPC64LE.rootPower c ((rootQ c + 1) / 2) 1)
    (.seq (.block (copy c.n (c.sl T5) (c.sl ACC))) (Impl.EcKey.Compressed.PPC64LE.rootPower c (rootQ c) 2))) s _
  obtain ap : ∀ {i j}, i < 45 → i ∉ [EXPP, ACC, PT] → j < 3 →
      ∀ w ∈ rootPowerW c j, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hl hj w hw' => by
    simp only [rootPowerW, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl
    · exact apart_slW (c := c) (l := [EXPP]) (by simp at hl ⊢; exact hl.1) _ (List.mem_singleton_self _)
    · exact apart_tbl h7 hi _ _ (List.mem_singleton_self _)
    · exact apart_slW (c := c) (l := [ACC]) (by simp at hl ⊢; exact hl.2.1) _ (List.mem_singleton_self _)
    · exact apart_slW (c := c) (l := [PT]) (by simp at hl ⊢; exact hl.2.2) _ (List.mem_singleton_self _)
    · exact apart_own h7 hi _ (List.mem_singleton_self _)
  refine WP.seq (WP.mono (rootPower_ok hc (by decide) hq' hw hB hO) fun s₁ ⟨hw₁, k₁, U₁, lt₁, v₁⟩ => ?_)
  obtain e₁ : ∀ {i}, i < 45 → i ∉ [EXPP, ACC, PT] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁ h7 hn hi (ap hi hl (by decide))
  refine WP.seq (WP.mono (copy_ok c.n hw₁.ws hw₁.at3 (o := c.sl T5) (a := c.sl ACC) (sl_al c _) (sl_al c _)
    (by omega_arith) (by omega_arith) (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega_arith)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_kp k₂
  obtain f₂ : ∀ {i}, i < 45 → i ≠ T5 → sv c base s₂ i = sv c base s₁ i := fun hi h =>
    O₂.wordsVal (sl_apart c h) (by have := sl_le c h7 hi; omega_arith)
  refine WP.mono (rootPower_ok hc (by decide) hq hw₂
    (by rw [f₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hB)
    (by rw [f₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hO)) fun s₃ ⟨hw₃, k₃, U₃, lt₃, v₃⟩ => ?_
  obtain t5₃ : sv c base s₃ T5 = sv c base s₁ ACC := by
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
  obtain hT0 := sl_le c h7 (i := T0) (by decide)
  obtain hA' := sl_le c h7 (i := ACC) (by decide)
  obtain hT5 := sl_le c h7 (i := T5) (by decide)
  obtain hT1 := sl_le c h7 (i := T1) (by decide)
  rw [Impl.EcKey.Compressed.PPC64LE.tonelliSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok c.n hw.ws hw.at3 (o := c.sl T0) (a := c.sl ACC) (sl_al c _) (sl_al c _)
    (by omega_arith) (by omega_arith) (by have := sl_apart c (i := T0) (j := ACC) (by decide); omega_arith)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok c.n (k₁.ws hw.ws) (k₁.at hw.at3) (o := c.sl ACC) (a := c.sl T5) (sl_al c _) (sl_al c _)
    (by omega_arith) (by omega_arith) (by have := sl_apart c (i := ACC) (j := T5) (by decide); omega_arith)) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  let z := Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)
  obtain zR : c.mont z.val < 2 ^ (64 * c.n) := Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hc.p_lt
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok ((k₁.trans k₂).ws hw.ws) ((k₁.trans k₂).at hw.at3) (o := c.sl T1) (by omega_arith) zR)
    fun s₃ ⟨O₃, v₃, k₃⟩ => ?_
  rw [← wordsVal_eq_val32] at v₃
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step (exec_lsl (by decide)) (WP.block_nil ?_)
  obtain K : Kp [.r4, .r11, .r31] s ((s₃.write .r31 (BitVec.ofNat 64 95)).write .r31
      ((s₃.write .r31 (BitVec.ofNat 64 95)).gpr .r31 <<< 32)) :=
    (((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))).trans
      ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))
  obtain e₃ : ∀ {i}, i < 45 → i ≠ T1 → sv c base s₃ i = sv c base s₂ i := fun hi h =>
    O₃.wordsVal (sl_apart c h) (by have := sl_le c h7 hi; omega_arith)
  obtain r₃ : sv c base s₃ ACC = sv c base s T5 := by
    rw [e₃ (by decide) (by decide)]; show wordsVal s₂.mem base (c.sl ACC) c.n = _; rw [v₂]
    exact O₁.wordsVal (sl_apart c (i := T5) (j := T0) (by decide)) (by omega_arith)
  obtain t₃ : sv c base s₃ T0 = sv c base s ACC := by
    rw [e₃ (by decide) (by decide)]
    show wordsVal s₂.mem base (c.sl T0) c.n = _
    rw [O₂.wordsVal (sl_apart c (i := T0) (j := ACC) (by decide)) (by omega_arith), v₁]
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
    · rw [show wordsVal s₃.mem base (c.sl T1) c.n = sv c base s₃ T1 from rfl, c₃]; exact Nat.mod_lt _ (by omega_arith)
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
  obtain U₁₂ : Unch base (candW c) s.mem s₂.mem := (U₁.trans U₂).mono fun w hw' => by
    simp only [candW, slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw' ⊢
    grind
  obtain one₂ : sv c base s₂ ONEP = 2 ^ (64 * c.n) % c.C.p := by
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

end

end


/-!
# SEC 1 point conversion over P-224 on PPC64LE: `Verified`

`compress_verified` and `decompress_verified`: from `compress_correct` and
`decompress_correct` (with Tonelli and Shanks's root, as `p ≡ 1 mod 4`), for P-224's configuration, and
the times depending only on `out`, `public` and `scratch` (`taint_decide` on
the code's literal).
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE.P224

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Proof.Ecdsa.PPC64LE

theorem compress_ct : ConstantTime isa (compressContract Spec.P224.curve).pre
    (compressContract Spec.P224.curve).pub Impl.EcKey.Compressed.PPC64LE.compressP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩) (by taint_decide)

theorem compress_sat : ∃ s, (Spec.EcKey.P224.inst.compressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.compressPublicKeyContract,
    Spec.EcKey.Instance.compressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, satState] [satState] using (satState 28)

theorem compress_verified :
    Verified target Impl.EcKey.Compressed.PPC64LE.compressP224 (Spec.EcKey.P224.inst.compressPublicKeyContract abi 0) :=
  Verified.of_correct (compress_correct p224 p224_ok) compress_ct (compress_implies _ compress_sat)

/-- P-224's square root: Tonelli and Shanks's, for `p - 1 = q 2⁹⁶` and the
nonresidue 11. -/
abbrev root (a : Spec.Weierstrass.Fe Spec.P224.curve) : Spec.Weierstrass.Fe Spec.P224.curve :=
  Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)

theorem decompress_ct : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub Impl.EcKey.Compressed.PPC64LE.decompressP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5⟩) (by taint_decide)

theorem decompress_sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, decompressSatState] [decompressSatState] using (decompressSatState 28)

theorem decompress_verified (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    Verified target Impl.EcKey.Compressed.PPC64LE.decompressP224
      (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct p224 p224_ok root
      (candidateTonelli_correct p224_ok (by decide +kernel) (by decide +kernel)))
    decompress_ct (decompress_implies _ _ (Proof.P224.rootFacts hL) decompress_sat)

end VG.Proof.EcKey.Compressed.PPC64LE.P224
