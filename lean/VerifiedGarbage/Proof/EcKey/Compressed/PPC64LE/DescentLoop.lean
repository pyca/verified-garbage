module

public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Descent
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Poly
public import VerifiedGarbage.Impl.EcKey.Compressed.Root

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
  have hv : ∀ i ∈ [ACC, T0, T1], i ∈ validAfter descentN [ACC, T0, T1, T4] := by decide
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
  have e₁ : ∀ {i}, i < 45 → i ≠ T3 → sv c base s₁ i = sv c base s i := fun hi h =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h)
  refine WP.seq (WP.mono (descentChoose_ok hc hw₁ lt₁ (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hO)) fun s₂ ⟨hw₂, k₂, U₂, lt₂, v₂⟩ => ?_)
  have e₂ : ∀ {i}, i < 45 → i ∉ [W0, T4] → sv c base s₂ i = sv c base s₁ i := fun hi h => by
    refine sv_unch U₂ h7 hn hi (apart_append (apart_callW h7 hi (fun h' => h (by simp [h']))) ?_)
    exact apart_slW (c := c) (l := [T4]) (fun h' => h (by simp at h'; simp [h']))
  have r31₂ : s₂.gpr .r31 = ctr j 0 := by rw [k₂.gpr _ (by decide), r31₁]
  have f₂ : ∀ {i}, i ∈ [ACC, T0, T1] → sv c base s₂ i = sv c base s i := fun hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (descentUpdate_ok hc hw₂ (fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · rw [f₂ (by simp)]; exact hlt _ (by simp)
    · rw [f₂ (by simp)]; exact hlt _ (by simp)
    · rw [f₂ (by simp)]; exact hlt _ (by simp)
    · exact lt₂)) fun s₃ ⟨hw₃, k₃, U₃, lt₃, r₃, t₃, c₃⟩ => ?_)
  have r31₃ : s₃.gpr .r31 = ctr j 0 := by rw [k₃.gpr _ (by decide), r31₂]
  refine WP.mono (descentCounter_ok hj hj' r31₃) fun s₄ ⟨K₄, r31₄, m₄⟩ => ?_
  have ev : ∀ i, sv c base s₄ i = sv c base s₃ i := fun i => by simp only [sv, m₄]
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
    have ev' : ∀ i, fieldAt c base s₄ i = fieldAt c base s₃ i := fun i => by simp only [fieldAt, ev]
    have ff₂ : ∀ {i}, i ∈ [ACC, T0, T1] → fieldAt c base s₂ i = fieldAt c base s i := fun hi => by
      simp only [fieldAt, f₂ hi]
    rw [ev', ev', ev', r₃, t₃, c₃, ff₂ (show ACC ∈ [ACC, T0, T1] by simp), ff₂ (show T0 ∈ [ACC, T0, T1] by simp),
      ff₂ (show T1 ∈ [ACC, T0, T1] by simp)]
    conv => rhs; rw [show j = j - 1 + 1 by omega, rootDescent]
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
    (fun k t I => eval_hi_nonzero (by have := I.le; omega) I.r31) (fun k t hk hkc I => ?_)
    (fun t I => ⟨I.ws, I.rk, I.unch, I.lt _ (by simp), by rw [← I.val]; rfl⟩) hcount
    ⟨hw, h31, Nat.le_refl _, Rk.refl _ _, Unch.refl _ _ _, hlt, hO, rfl⟩
  refine WP.mono (descentRound_ok hc I.ws hk (by omega) I.r31 I.lt I.one)
    fun u ⟨hwu, r31u, ku, Uu, ltu, vu⟩ => ⟨hwu, r31u, by omega, I.rk.trans ku,
      (I.unch.trans Uu).mono fun w hw' => (List.mem_append.mp hw').elim id id, ltu, ?_, vu.trans I.val⟩
  exact (sv_unch Uu h7 hn (i := ONEP) (by decide)
    (apart_append (apart_slW (by decide)) (apart_own h7 (by decide)))).trans I.one

end VG.Proof.EcKey.Compressed.PPC64LE
