module

public import VerifiedGarbage.Impl.EcKey.Compressed.PPC64LE.Decompress
public import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Counter
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
public import VerifiedGarbage.Spec.Weierstrass

import VerifiedGarbage.Proof.EcKey.Compressed.PPC64LE.Poly
import VerifiedGarbage.Impl.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Ecdh.PPC64LE.Peer
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Loop
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
/-!
# SEC 1 point decompression on PPC64LE: P-224's descent

A round of Tonelli and Shanks's descent (`rootDescent`) for the round's `j`
in `r31`'s high word: `T3 = T0^(2^(j-1))` (`descentPower_ok`), `T4 = 1` if
it is 1, else `T1` (`descentChoose_ok`), `r = r b`, `t = t b²`, `c = c²`
(`descentUpdate_ok`), and `j - 1` (`descentRound_ok`); `descentLoop_ok`:
the rounds from `j`, down to 0.
-/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/PPC64LE/Square.lean`, which only this module imported.
section

/-!
# SEC 1 point decompression on PPC64LE: repeated squarings

`squarePower_ok`: `squarePower` squares `T3` as many times as `r31`'s low
word `i`, which it takes to zero: `T3 = T3^(2^i)`.
-/

section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass

variable {c : Cfg}

/-- The squarings' invariant, with `k` squarings left of `i`. -/
structure SqInv (c : Cfg) (base : Addr) (s₀ : State) (j i : Nat) (s : State) (k : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = ctr j k
  le : k ≤ i
  rk : Rk powClob s₀ s
  unch : Unch base (callW c T3) s₀.mem s.mem
  lt : sv c base s T3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s₀ T3) ^ (2 ^ (i - k))

theorem sq_pow {α : Type _} [Lean.Grind.CommRing α] (x : α) (m : Nat) :
    x ^ (2 ^ m) * x ^ (2 ^ m) = x ^ (2 ^ (m + 1)) := by
  rw [← Lean.Grind.Semiring.pow_add, Nat.pow_succ, Nat.mul_two]

/-- `T3 = T3^(2^i)`, for the low word `i` of `r31`, which ends zero. -/
theorem squarePower_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {j i : Nat}
    (hi : i < 2 ^ 32) (h31 : s.gpr .r31 = ctr j i) (hlt : sv c base s T3 < c.C.p) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.squarePower c) s fun s' =>
      WsReg s' base ∧ s'.gpr .r31 = ctr j 0 ∧ Rk powClob s s' ∧ Unch base (callW c T3) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) = toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ i) := by
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine WP.ite (decide (i = 0)) (eval_lo_zero hi h31) (fun h => ?_) (fun h => ?_)
  · have hi0 : i = 0 := of_decide_eq_true h
    subst hi0
    exact WP.block_nil ⟨hw, h31, Rk.refl _ _, Unch.refl _ _ _, hlt, by
      rw [Nat.pow_zero, Lean.Grind.Semiring.pow_one]⟩
  · have hi0 : i ≠ 0 := of_decide_eq_false h
    refine loopBy_ok (Inv := fun k s' => SqInv c base s j i s' k) (n := i)
      (fun k s' I => eval_lo_nonzero (by have := I.le; omega) I.r31) (fun k t hk hki I => ?_)
      (fun t I => ⟨I.ws, I.r31, I.rk, I.unch, I.lt, by rw [I.val, Nat.sub_zero]⟩) (by omega)
      ⟨hw, h31, Nat.le_refl _, Rk.refl _ _, Unch.refl _ _ _, hlt, by
        rw [Nat.sub_self, Nat.pow_zero, Lean.Grind.Semiring.pow_one]⟩
    refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 I.ws (o := T3) (a := T3) (b := T3) (by decide)
      (by decide) (by decide) I.lt) fun t₁ ⟨k₁, U₁, lt₁, e₁⟩ => ?_)
    have r31₁ : t₁.gpr .r31 = ctr j k := by rw [k₁.gpr _ (by decide), I.r31]
    refine wp_step (exec_subi (by decide) (by decide)) (WP.block_nil ⟨I.ws.of_rk k₁ |>.of_kp
      (Kp.write _ _ (rs := [.r31]) (by decide)), ?_, by omega, ?_, ?_, lt₁, ?_⟩)
    · simp only [write_gpr, ite_true, r31₁]; exact ctr_dec hk (by omega)
    · exact (I.rk.trans (k₁.mono (by decide))).trans ((Kp.write _ _ (rs := [.r31]) (by decide)).rk)
    · simp only [write_mem]
      exact (I.unch.trans U₁).mono fun w hw' => (List.mem_append.mp hw').elim id id
    · show toM c.C.p (2 ^ (64 * c.n)) (sv c base t₁ T3) = _
      rw [toM_mul hpR e₁, I.val, sq_pow, show i - k + 1 = i - (k - 1) by omega]

end VG.Proof.EcKey.Compressed.PPC64LE
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (W0)
open VG.Impl.EcKey.Compressed (rootDescent)

variable {c : Cfg}

/-- A slot's number, in `Fin p`. -/
abbrev fieldAt (c : Cfg) (base : Addr) (s : State) (i : Nat) : Fe c.C :=
  toM c.C.p (2 ^ (64 * c.n)) (sv c base s i)

/-! ## `T3 = T0^(2^(j-1))` -/

theorem descentStart_eq (c : Cfg) : Impl.EcKey.Compressed.PPC64LE.descentStart c =
    copy c.n (c.sl T3) (c.sl T0) ++ ([.lsr .d .r4 .r31 32, .subi .r4 .r4 1, .logic .or .r31 .r31 .r4] : List Instr) := rfl

/-- `j - 1` to the low word of `r31`, through `r4`. -/
theorem startCtr_ok {s : State} {j : Nat} (hj : 1 ≤ j) (hj' : j < 2 ^ 32) (h31 : s.gpr .r31 = ctr j 0) :
    WP isa (.block [.lsr .d .r4 .r31 32, .subi .r4 .r4 1, .logic .or .r31 .r31 .r4]) s fun t =>
      Kp [.r4, .r31] s t ∧ t.gpr .r31 = ctr j (j - 1) ∧ t.mem = s.mem := by
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_step exec_logic (WP.block_nil ⟨((Kp.write _ _ (rs := [.r4, .r31]) (by decide)).trans
    (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide)), ?_, by simp only [write_mem]⟩)
  simp only [write_gpr, ite_true, reduceCtorEq, ite_false, h31]
  rw [ctr_hi hj' (by decide), ofNat_pred64 hj, ctr_or hj' (by omega_arith)]

theorem descentPower_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {j : Nat}
    (hj : 1 ≤ j) (hj' : j < 2 ^ 32) (h31 : s.gpr .r31 = ctr j 0) (hlt : sv c base s T0 < c.C.p) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.descentPower c) s fun s' =>
      WsReg s' base ∧ s'.gpr .r31 = ctr j 0 ∧ Rk powClob s s' ∧ Unch base (callW c T3) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧ fieldAt c base s' T3 = fieldAt c base s T0 ^ (2 ^ (j - 1)) := by
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have h3 := sl_le c h7 (i := T3) (by decide)
  have h0' := sl_le c h7 (i := T0) (by decide)
  refine WP.seq ?_
  rw [descentStart_eq]
  refine wp_append (WP.mono (copy_ok c.n hw.ws hw.at3 (o := c.sl T3) (a := c.sl T0) (sl_al c _) (sl_al c _)
    (by omega_arith) (by omega_arith) (by have := sl_apart c (i := T3) (j := T0) (by decide); omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have r31₁ : s₁.gpr .r31 = ctr j 0 := by rw [k₁.gpr _ (by decide), h31]
  refine WP.mono (startCtr_ok hj hj' r31₁) fun s₂ ⟨K₂, r31₂, m₂⟩ => ?_
  have hw₂ := (hw.of_kp k₁).of_kp K₂
  refine WP.mono (squarePower_ok hc hw₂ (j := j) (i := j - 1) (by omega_arith) r31₂ (by
    show wordsVal s₂.mem base (c.sl T3) c.n < c.C.p; rw [m₂, e₁]; exact hlt)) fun s' ⟨hw', r31', k', U', lt', v'⟩ =>
    ⟨hw', r31', ((k₁.rk (rs' := powClob)).trans (K₂.rk (rs' := powClob))).trans k', ?_, lt', ?_⟩
  · have U₁ : Unch base [(c.sl T3, 8 * c.n)] s.mem s₂.mem := by rw [m₂]; exact O₁.unch
    exact (U₁.trans U').mono fun w hw'' => by
      simp only [callW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw'' ⊢
      rcases hw'' with h | h | h <;> simp [h]
  · show toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) = _
    rw [v']
    show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl T3) c.n) ^ _ = _
    rw [m₂, e₁]

/-! ## `T4 = 1` if `T3 = 1`, else `T1` -/

/-- The mask `r10` of `[a] = 0`, through `r4` and `r5`. -/
theorem zeroMov_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {a : Nat} (ha4 : a % 4 = 0) (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.PPC64LE.zeroMask c a ++ [mov .r10 .r5])) s fun t =>
      Kp [.r4, .r5, .r10] s t ∧ t.mem = s.mem ∧ t.gpr .r10 = mask64 (wordsVal s.mem base a c.n = 0) := by
  rw [show Impl.EcKey.Compressed.PPC64LE.zeroMask c a ++ [mov .r10 .r5] =
    c.nonzero a ++ ([.li .r4 0, .sub .r5 .r4 .r5, .subi .r5 .r5 1, mov .r10 .r5] : List Instr) by
      simp only [Impl.EcKey.Compressed.PPC64LE.zeroMask, List.append_assoc, List.cons_append, List.nil_append]]
  refine wp_append (WP.mono (nonzero_ok c hs h3 ha4 hn ha) fun s₂ ⟨m₂, k₂, mem₂⟩ => ?_)
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_step exec_mov (WP.block_nil ⟨(k₂.mono (by decide)).trans ((((Kp.write _ _ (by decide)).trans
    (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))),
    by simp only [write_mem, mem₂], ?_⟩)
  simp only [write_gpr, ite_true, reduceCtorEq, ite_false, m₂]
  rw [Proof.Ecdh.PPC64LE.mask_not]
  by_cases h : wordsVal s.mem base a c.n = 0 <;> simp [h]

theorem descentChoose_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (h3 : sv c base s T3 < c.C.p) (h1 : sv c base s T1 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.PPC64LE.descentChoose c) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (callW c W0 ++ [(c.sl T4, 8 * c.n)]) s.mem s'.mem ∧
      sv c base s' T4 < c.C.p ∧
      fieldAt c base s' T4 = if fieldAt c base s T3 = 1 then 1 else fieldAt c base s T1 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hOlt : sv c base s ONEP < c.C.p := by rw [hO]; exact Nat.mod_lt _ (by omega_arith)
  refine WP.seq (WP.mono (slSub_ok hc.fp hc.fpk hc.fpm h7 hw (o := W0) (a := T3) (b := ONEP) (by decide)
    (by decide) (by decide) h3 hOlt) fun s₁ ⟨k₁, U₁, e₁⟩ => ?_)
  have hw₁ := hw.of_rk k₁
  have v₁ : ∀ {i}, i < 45 → i ≠ W0 → sv c base s₁ i = sv c base s i := fun hi h₁ =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h₁)
  have hz : sv c base s₁ W0 = 0 ↔ fieldAt c base s T3 = 1 := by
    rw [← toM_eq_zero_iff hpR (by rw [e₁]; exact Nat.mod_lt _ (by omega_arith)), e₁, toM_sub (by omega_arith), hO,
      toM_one hpR]
    constructor <;> intro h <;> grind
  have hW0 := sl_le c h7 (i := W0) (by decide)
  have hT4 := sl_le c h7 (i := T4) (by decide)
  have hT1 := sl_le c h7 (i := T1) (by decide)
  have hON := sl_le c h7 (i := ONEP) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeroMov_ok c hw₁.ws hw₁.at3 (sl_al c W0) h0 (by omega_arith)) fun s₂ ⟨K₂, mem₂, m₂⟩ => ?_
  have hw₂ := hw₁.of_kp K₂
  refine WP.mono (sel_ok (decide (wordsVal s₁.mem base (c.sl W0) c.n = 0)) c.n hw₂.ws hw₂.at3
    (by rw [m₂]; simp only [mask64, decide_eq_true_eq])
    (sl_al c _) (sl_al c _) (sl_al c _) (by omega_arith) (by omega_arith) (by omega_arith)
    (by have := sl_apart c (i := T4) (j := T1) (by decide); omega_arith)
    (by have := sl_apart c (i := T4) (j := ONEP) (by decide); omega_arith)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [mem₂] at e₄
  have K : Rk fnClob s s₄ := k₁.trans ((K₂.rk (rs' := fnClob)).trans (k₄.rk (rs' := fnClob)))
  refine ⟨hw₂.of_kp k₄, K, ?_, ?_, ?_⟩
  · have U₂ : Unch base [(c.sl T4, 8 * c.n)] s₁.mem s₄.mem := by rw [← mem₂]; exact O₄.unch
    exact U₁.trans U₂
  · show wordsVal s₄.mem base (c.sl T4) c.n < c.C.p
    rw [e₄]
    split
    · show sv c base s₁ ONEP < _; rw [v₁ (i := ONEP) (by decide) (by decide)]; exact hOlt
    · show sv c base s₁ T1 < _; rw [v₁ (i := T1) (by decide) (by decide)]; exact h1
  · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem base (c.sl T4) c.n) = _
    rw [e₄]
    by_cases h : fieldAt c base s T3 = 1
    · have hd : decide (wordsVal s₁.mem base (c.sl W0) c.n = 0) = true := decide_eq_true (hz.mpr h)
      simp only [hd, ite_true, h]
      rw [show wordsVal s₁.mem base (c.sl ONEP) c.n = sv c base s₁ ONEP from rfl,
        v₁ (by decide) (by decide), hO, toM_one hpR]
    · have hd : decide (wordsVal s₁.mem base (c.sl W0) c.n = 0) = false :=
        decide_eq_false fun h' => h (hz.mp h')
      simp only [hd, Bool.false_eq_true, ite_false, h]
      rw [show wordsVal s₁.mem base (c.sl T1) c.n = sv c base s₁ T1 from rfl, v₁ (by decide) (by decide)]

end VG.Proof.EcKey.Compressed.PPC64LE
