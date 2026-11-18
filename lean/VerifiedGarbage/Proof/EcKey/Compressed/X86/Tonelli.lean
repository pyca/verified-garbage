module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.SlotOps
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Ecdsa.X86.Main
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Weierstrass.X86.Pow
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Ecdh.X86.Peer
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Impl.Ecdsa.X86
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Impl.Weierstrass.X86
import VerifiedGarbage.Proof.Ecdsa.X86.Stages

/-! ### `EcKey.Compressed.X86.TonelliSetup`, which this module and modules that import it used -/

section

/-! # Initialize P-224's descent from its two computed powers -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG.X86.Wp
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Impl.EcKey.Compressed.X86 (rootQ)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

theorem tonelliSetup_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hr : sv c base s T5 < c.C.p) (ht : sv c base s ACC < c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.X86.tonelliSetup c)) s fun t =>
      Keeps [.eax] s t ∧ Unch base (slW c [T0, ACC, T1, T2]) s.mem t.mem ∧
      (∀ i ∈ [ACC, T0, T1], sv c base t i < c.C.p) ∧
      t.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 95 ∧
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
  have hT2 := sl_le c h7 (i := T2) (by decide)
  rw [Impl.EcKey.Compressed.X86.tonelliSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs (by omega_using [hT0]) (by omega_using [hACC])
    (by have := sl_apart c (i := T0) (j := ACC) (by decide); omega_using [this])) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  simp only [← wordsVal_eq_val32] at v₁
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs₁ (by omega_using [hACC]) (by omega_using [hT5])
    (by have := sl_apart c (i := ACC) (j := T5) (by decide); omega_using [this])) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  simp only [← wordsVal_eq_val32] at v₂
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have r₂ : sv c base s₂ ACC = sv c base s T5 := by
    rw [sv, v₂, O₁.wordsVal (sl_apart c (i := T5) (j := T0) (by decide)) (by omega_using [hn, hT5])]
  have t₂ : sv c base s₂ T0 = sv c base s ACC := by
    rw [sv, O₂.wordsVal (sl_apart c (i := T0) (j := ACC) (by decide)) (by omega_using [hn, hT0]), v₁]
  let z := Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)
  have zR : c.mont z.val < 2 ^ (64 * c.n) := Nat.lt_trans
    (Nat.mod_lt _ (by have := hc.p_ge; omega_using [hr])) hc.p_lt
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ hT1 zR) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine wp_movi fun s₄ u₄ => ?_
  have hs₄ := hs₃.of_keeps u₄.keeps (by decide)
  refine wp_storeS (hs₄.ea (by omega_using [h0, hT2])) (hs₄.write (by omega_using [h0, hT2] : c.sl T2 + 4 ≤ size))
    fun t m₄ => WP.block_nil ?_
  have O₄ : Outside base (c.sl T2) 4 s₃.mem t.mem := by
    rw [m₄.mem, u₄.mem]
    exact writeW32_outside _ _ _ (by omega_using [hn, hT2])
  have v₄ : t.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 95 := by
    rw [m₄.mem, Mem.readW_writeW_self32, u₄.gpr]; rfl
  have k₄ : Keeps [.eax] s₃ t := u₄.keeps.trans (m₄.keeps _)
  have e₃ {i : Nat} (hi : i < 45) (hw : i ≠ T1) : sv c base s₃ i = sv c base s₂ i :=
    O₃.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega_using [hn, this])
  have e₄ {i : Nat} (hi : i < 45) (hw : i ≠ T2) : sv c base t i = sv c base s₃ i :=
    O₄.wordsVal (by have := sl_apart c hw; omega_using [h0, this]) (by have := sl_le c h7 hi; omega_using [hn, this])
  have r₄ : sv c base t ACC = sv c base s T5 := by
    rw [e₄ (by decide) (by decide), e₃ (by decide) (by decide), r₂]
  have t₄ : sv c base t T0 = sv c base s ACC := by
    rw [e₄ (by decide) (by decide), e₃ (by decide) (by decide), t₂]
  have c₄ : sv c base t T1 = c.mont z.val := by
    rw [e₄ (by decide) (by decide)]; exact v₃
  refine ⟨((k₁.trans k₂).trans k₃).trans k₄, ?_, ?_, ?_, by rw [r₄], by rw [t₄], ?_⟩
  · exact unch_same (unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₃))
      (slot_frame (by simp) (by omega_using [h0]) O₄)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [r₄]; exact hr
    · rw [t₄]; exact ht
    · rw [c₄]; exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [hr])
  · exact v₄
  · rw [c₄, toM_cmont hc]
    exact Fin.ext (Nat.mod_eq_of_lt z.isLt)

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.TonelliPowers`, which this module and modules that import it used -/

section

/-! # The two initial powers in P-224's root recovery -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Impl.Ecdh.X86 (W2)
open VG.Impl.EcKey.Compressed.X86 (rootQ)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

abbrev tonelliPowerWrites (c : Cfg) :=
  rootPowerWrites c 1 ++ slW c [T5] ++ rootPowerWrites c 2

theorem tonelliPowers_ok {c : Cfg} (hc : CfgOk c)
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86.tonelliPowers c) s fun t =>
      Keeps powClob s t ∧ Unch base (tonelliPowerWrites c) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ sv c base t T5 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ rootQ c ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T5) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((rootQ c + 1) / 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hq : rootQ c ≤ c.C.p - 1 := Nat.div_le_self _ _
  have hp := hc.p_ge
  have he : (rootQ c + 1) / 2 < 2 ^ (64 * c.n) := by have := hc.p_lt; omega_using [hq, this]
  have hqR : rootQ c < 2 ^ (64 * c.n) := by have := hc.p_lt; omega_using [hq, this]
  change WP isa (.seq (Impl.EcKey.Compressed.X86.rootPower c ((rootQ c + 1) / 2) 1)
    (.seq (.block (copy (2 * c.n) (c.sl T5) (c.sl ACC)))
      (Impl.EcKey.Compressed.X86.rootPower c (rootQ c) 2))) s _
  refine WP.seq (WP.mono (rootPower_ok hc (by decide) he hs hM hB hO)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [EXPP, ACC, PT, TMP]) :
      sv c base s₁ i = sv c base s i := sv_unch U₁ h7 hn hi (rootPower_apart hc hi hw)
  refine WP.seq (WP.mono (copy_ok (2 * c.n) hs₁ (by have := sl_le c h7 (i := T5) (by decide); omega_using [this]) (by have := sl_le c h7 (i := ACC) (by decide); omega_using [this])
    (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega_using [this])) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  simp only [← wordsVal_eq_val32] at v₂
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ≠ T5) : sv c base s₂ i = sv c base s₁ i :=
    O₂.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega_using [hn, this])
  have M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.mono (rootPower_ok hc (by decide) hqR hs₂ M₂
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hB)
    (by rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hO))
    fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  have et : sv c base t T5 = sv c base s₂ T5 :=
    sv_unch Ut h7 hn (by decide) (rootPower_apart hc (by decide) (by decide))
  refine ⟨(k₁.trans (k₂.mono (by decide))).trans kt,
    (U₁.trans O₂.unch).trans Ut, ltt, ?_, ?_, ?_⟩
  · rw [et]
    change wordsVal s₂.mem base (c.sl T5) c.n < _
    rw [v₂]; exact lt₁
  · rw [vt, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
  · rw [et]
    change toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl T5) c.n) = _
    rw [v₂]; exact v₁

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.DescentRound`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.X86.DescentPower`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.X86.Counter`, which this module and modules that import it used -/

section

/-! # Public loop counters for P-224 coordinate recovery -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

theorem testCounter_ok {j : Nat} (s : State) (hj : j < 2 ^ 32)
    (hb : s.gpr .esi = BitVec.ofNat 32 j) :
    WP isa (.block [testCounter]) s fun t =>
      t.zf = some (decide (j = 0)) ∧ Keeps [] s t ∧ t.mem = s.mem :=
  wp_testCounter hj hb fun _ f hz => WP.block_nil ⟨hz, ⟨fun r _ => congrFun f.gpr r, f.rd, f.wr⟩, f.mem⟩

theorem descentCounter_ok {c : Cfg} {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hd : c.sl T2 + 4 ≤ size) (hj : 1 ≤ j) (hj' : j < 2 ^ 32)
    (hw : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (.block (Impl.EcKey.Compressed.X86.descentCounter c)) s fun t =>
      t.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 (j - 1) ∧
      t.zf = some (decide (j - 1 = 0)) ∧ Keeps [.esi] s t ∧
      Outside base (c.sl T2) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.X86.descentCounter
  refine wp_movS (show readSrc s (.mem (Impl.Mont.X86.sc (c.sl T2))) = some (s.mem.readW (off base (c.sl T2)) 32) by
    simp only [readSrc, State.load32, hs.ea (d := c.sl T2) (by omega_using [hd]), hs.read hd, ite_true]) fun s₁ u₁ _ => ?_
  refine wp_decCounter hj (by rw [u₁.gpr, hw]) fun s₂ hb₂ k₂ m₂ => ?_
  have K : Keeps [.esi] s s₂ := u₁.keeps.trans k₂
  have hs₂ := hs.of_keeps K (by decide)
  refine wp_storeS (hs₂.ea (by omega_using [hd])) (hs₂.write hd) fun s₃ m₃ => ?_
  refine wp_testCounter (j := j - 1) (by omega_using [hj']) (by rw [m₃.gpr, hb₂]) fun t f hz => WP.block_nil ?_
  refine ⟨?_, hz, K.trans ((m₃.keeps _).trans ⟨fun r _ => congrFun f.gpr r, f.rd, f.wr⟩), ?_⟩
  · rw [f.mem, m₃.mem, Mem.readW_writeW_self32, hb₂]
  · rw [f.mem, m₃.mem, m₂, u₁.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega_using [hd, this])

end VG.Proof.EcKey.Compressed.X86

end

end

/-! # The tested power in a P-224 descent round -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/Square.lean`, which only this module imported.
section

/-! # Repeated squaring for the P-224 root descent

The backwards invariant `current^(2^remaining) = original^(2^count)`
avoids any assumption about the input being a square or nonzero.
-/

section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

structure SquareInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  counter : s.gpr .esi = BitVec.ofNat 32 j
  keep : Keeps powClob s₀ s
  unch : Unch base (slWk c [T3, TMP]) s₀.mem s.mem
  lt : sv c base s T3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ j) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s₀ T3) ^ (2 ^ count)

theorem squareStep_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {count j : Nat}
    (hj : 1 ≤ j) (hcount : count < 2 ^ 31) (hjc : j ≤ count) {s₀ s : State}
    (I : SquareInv c base count s₀ s j) :
    WP isa (Impl.EcKey.Compressed.X86.squareStep c) s fun s' =>
      SquareInv c base count s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  rw [Impl.EcKey.Compressed.X86.squareStep]
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) hc.fp h7 I.scr
    (o := T3) (a := T3) (b := T3) (by decide) (by decide) (by decide) I.lt)
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr I.scr
  have hm₁ := I.mod.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have hb₁ : s₁.gpr .esi = BitVec.ofNat 32 j :=
    (k₁.keeps.1 _ (by decide)).trans I.counter
  have U₁ : Unch base (slWk c [T3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  have v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ 2 := by
    rw [toM_mul (unitMod_pow_two hc.p_odd (64 * c.n)) e₁, Lean.Grind.Semiring.pow_two]
  refine wp_decCounter hj hb₁ fun s₂ hb₂ k₂ m₂ => ?_
  refine wp_testCounter (j := j - 1) (by omega) (by rw [hb₂]) fun s₃ f₃ hz₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s₁.mem := f₃.mem.trans m₂
  have K : Keeps powClob s₁ s₃ := (k₂.mono (by decide)).trans ⟨fun r _ => congrFun f₃.gpr r, f₃.rd, f₃.wr⟩
  refine ⟨⟨hs₁.of_keeps K (by decide),
    by rw [m₃]; exact hm₁, by rw [f₃.gpr, hb₂],
    (I.keep.trans (k₁.keeps.mono (by decide))).trans K, ?_,
    by rw [sv, m₃]; exact lt₁, ?_⟩, hz₃⟩
  · rw [m₃]
    exact (I.unch.trans U₁).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw)
  · rw [sv, m₃]
    change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) ^ (2 ^ (j - 1)) = _
    rw [v₁, pow_mul_exponents,
      show 2 * 2 ^ (j - 1) = 2 ^ j by
        calc
          2 * 2 ^ (j - 1) = 2 ^ (j - 1) * 2 := Nat.mul_comm _ _
          _ = 2 ^ (j - 1 + 1) := (Nat.pow_succ _ _).symm
          _ = 2 ^ j := by rw [Nat.sub_add_cancel hj]]
    exact I.val

theorem squareLoop_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {count : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .esi = BitVec.ofNat 32 count)
    (hcount : count < 2 ^ 31) (hpos : 1 ≤ count) :
    WP isa (.loop (Impl.EcKey.Compressed.X86.squareStep c) .ne) s fun s' =>
      Keeps powClob s s' ∧ Unch base (slWk c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  apply countLoop_ok (Inv := fun j t => SquareInv c base count s t j)
    (fun j t hj hjc hi => squareStep_ok hc hj hcount hjc hi) (n := count)
  · intro t I
    refine ⟨I.keep, I.unch, I.lt, ?_⟩
    simpa only [Nat.pow_zero, Lean.Grind.Semiring.pow_one] using I.val
  · exact hpos
  · exact ⟨hs, hM, hb, Keeps.refl _ _, Unch.refl _ _ _, hlt, rfl⟩

theorem squarePower_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {count : Nat} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .esi = BitVec.ofNat 32 count)
    (hcount : count < 2 ^ 31) :
    WP isa (Impl.EcKey.Compressed.X86.squarePower c) s fun s' =>
      Keeps powClob s s' ∧ Unch base (slWk c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  rw [Impl.EcKey.Compressed.X86.squarePower]
  refine WP.seq (WP.mono (testCounter_ok s (by omega) hb) fun s₁ ⟨hz₁, k₁, m₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.ite (decide (count = 0)) (by simp only [VG.X86.eval, hz₁]) (fun hz => ?_) (fun hn => ?_)
  · have hn : count = 0 := of_decide_eq_true hz
    apply WP.block_nil
    refine ⟨k₁.mono (by simp), ?_, ?_, ?_⟩
    · rw [m₁]
      exact Unch.refl _ _ _
    · rw [sv, m₁]
      exact hlt
    · rw [sv, m₁, hn, Nat.pow_zero, Lean.Grind.Semiring.pow_one]
  · have hn : count ≠ 0 := of_decide_eq_false hn
    refine WP.mono (squareLoop_ok hc hs₁ (m₁ ▸ hM) (by rw [sv, m₁]; exact hlt)
      (by rw [k₁.1 _ (by decide), hb]) hcount (by omega)) fun t ⟨kt, Ut, lt, vt⟩ => ?_
    refine ⟨(k₁.mono (by simp)).trans kt, ?_, lt, ?_⟩
    · rw [← m₁]
      exact Ut
    · simpa only [sv, m₁] using vt

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.X86.Wp

theorem descentPower_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T0 < c.C.p) (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (Impl.EcKey.Compressed.X86.descentPower c) s fun t =>
      Keeps powClob s t ∧ Unch base (slWk c [T3, TMP]) s.mem t.mem ∧
      sv c base t T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T0) ^ (2 ^ (j - 1)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  have h3 := sl_le c h7 (i := T3) (by decide)
  have h2 := sl_le c h7 (i := T2) (by decide)
  change WP isa (.seq (.block (copy (2 * c.n) (c.sl T3) (c.sl T0) ++
    [.mov .esi (.mem (sc (c.sl T2))), decCounter])) (Impl.EcKey.Compressed.X86.squarePower c)) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs (by omega_using [h3]) (by have := sl_le c h7 (i := T0) (by decide); omega_using [this])
    (by have := sl_apart c (i := T3) (j := T0) (by decide); omega_using [this])) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₁
  have v₁' : sv c base s₁ T3 = sv c base s T0 := by
    simpa only [sv, wordsVal_eq_val32] using v₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine wp_movS (show readSrc s₁ (.mem (sc (c.sl T2))) = some (s₁.mem.readW (off base (c.sl T2)) 32) by
    simp only [readSrc, State.load32, hs₁.ea (d := c.sl T2) (by omega_using [h0, h2]), hs₁.read (by omega_using [h0, h2] : c.sl T2 + 4 ≤ size), ite_true]) fun s₂ u₂ _ => ?_
  have hb₂ : s₂.gpr .esi = BitVec.ofNat 32 j := by
    rw [u₂.gpr, BitVec.eq_of_toNat_eq (O₁.w32 (by have := sl_apart c (i := T2) (j := T3) (by decide); omega_using [h0, this]) (by omega_using [hn, h2])), hword]
  refine wp_decCounter hj hb₂ fun s₃ hb₃ k₃ m₃' => WP.block_nil ?_
  have K : Keeps powClob s s₃ := (k₁.mono (by decide)).trans
    ((u₂.keeps.mono (by decide)).trans (k₃.mono (by decide)))
  have hs₃ := hs.of_keeps K (by decide)
  have m₃ : s₃.mem = s₁.mem := m₃'.trans u₂.mem
  have M₃ : ModOkW c.MP' size c.C.p s₃.mem base := modP_of hc (by
    rw [m₃, O₁.wordsVal (sl_apart c (i := MP) (j := T3) (by decide))
      (by have := sl_le c h7 (i := MP) (by decide); omega_using [hn, this])]
    exact hM.val)
  refine WP.mono (squarePower_ok hc hs₃ M₃
    (by rw [sv, m₃]; change sv c base s₁ T3 < _; rw [v₁']; exact hlt) hb₃ (by omega_using [hj']))
    fun t ⟨Kt, Ut, lt, vt⟩ => ?_
  refine ⟨K.trans Kt, ?_, lt, ?_⟩
  · rw [m₃] at Ut
    exact unch_same ((slot_frame (slots := [T3, TMP]) (by simp) (Nat.le_refl _) O₁).mono
      (fun w hw => List.mem_append_left _ hw)) Ut
  · simpa only [sv, m₃, show wordsVal s₁.mem base (c.sl T3) c.n = sv c base s T0 from v₁'] using vt

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.DescentChoose`, which only this module used -/

section

/-! # Select the correction factor of the P-224 descent -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Impl.Ecdh.X86 (W0)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86
open VG.X86.Wp

theorem zero_ok {c : Cfg} {s : State} {base : Addr} {a : Nat} (hs : Scr s base size) (h0 : 0 < c.n)
    (ha : a + 8 * c.n ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86.zeroMask c a)) s fun t =>
      t.gpr .edx = mask32 (wordsVal s.mem base a c.n = 0) ∧
      Keeps [.eax, .ecx, .edx] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.X86.zeroMask
  refine WP.block_append (WP.mono (nonzero_ok c hs h0 ha) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine wp_movi fun s₂ u₂ => ?_
  refine wp_subS rfl fun s₃ u₃ _ => ?_
  refine wp_movS rfl fun s₄ u₄ _ => ?_
  refine wp_subS rfl fun t u₅ _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), e₁]
    by_cases h : wordsVal s.mem base a c.n ≠ 0 <;> simp [mask32, h]
  · exact (k₁.mono (by decide)).trans ((u₂.keeps.mono (by decide)).trans
      ((u₃.keeps.mono (by decide)).trans ((u₄.keeps.mono (by decide)).trans
        (u₅.keeps.mono (by decide)))))
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

theorem descentChoose_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (_hM : ModOkW c.MP' size c.C.p s.mem base)
    (ht : sv c base s T3 < c.C.p) (hcval : sv c base s T1 < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86.descentChoose c) s fun t =>
      Keeps clob s t ∧ Unch base (slWk c [W0, T4, TMP]) s.mem t.mem ∧
      sv c base t T4 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T4) =
        if toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1 then 1
        else toM c.C.p (2 ^ (64 * c.n)) (sv c base s T1) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  have hp := hc.p_ge
  obtain hW := sl_le c h7 (i := W0) (by decide)
  obtain hT := sl_le c h7 (i := T3) (by decide)
  obtain hC := sl_le c h7 (i := T1) (by decide)
  obtain hB := sl_le c h7 (i := T4) (by decide)
  obtain hO := sl_le c h7 (i := ONEP) (by decide)
  obtain hOlt : sv c base s ONEP < c.C.p := by rw [hOne]; exact Nat.mod_lt _ (by omega_using [ht])
  rw [Impl.EcKey.Compressed.X86.descentChoose]
  refine WP.seq (WP.mono (slSub_ok hc hs (o := W0) (a := T3) (b := ONEP)
    (by decide) (by decide) (by decide) ht hOlt) fun s₁ ⟨k₁, e₁⟩ => ?_)
  change sv c base s₁ W0 = (sv c base s T3 + c.C.p - sv c base s ONEP) % c.C.p at e₁
  obtain hs₁ := k₁.scr hs
  obtain lt₁ : sv c base s₁ W0 < c.C.p := by
    rw [e₁]; exact Nat.mod_lt _ (by omega_using [ht])
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ W0) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) - 1 := by
    rw [e₁, toM_sub (by omega_using [hOlt]), hOne, toM_one (unitMod_pow_two hc.p_odd (64 * c.n))]
  obtain z₁ : sv c base s₁ W0 = 0 ↔ toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1 := by
    rw [← toM_eq_zero_iff (unitMod_pow_two hc.p_odd (64 * c.n)) lt₁, v₁]
    constructor <;> intro h <;> grind
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (zero_ok hs₁ h0 hW) fun s₂ ⟨mask₂, k₂, m₂⟩ => ?_
  simp only [mask32, show wordsVal s₁.mem base (c.sl W0) c.n = sv c base s₁ W0 from rfl, z₁] at mask₂
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  obtain hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps u₃.keeps (by decide)
  refine WP.mono (sel_ok (decide (toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) = 1)) (2 * c.n) hs₃
    (by rw [u₃.gpr, mask₂]; simp only [decide_eq_true_eq]) (by omega_using [hB]) (by omega_using [hC]) (by omega_using [hO])
    (by have := sl_apart c (i := T4) (j := T1) (by decide); omega_using [this])
    (by have := sl_apart c (i := T4) (j := ONEP) (by decide); omega_using [this]))
    fun t ⟨v₄, k₄, O₄⟩ => ?_
  obtain mem₃ : s₃.mem = s₁.mem := u₃.mem.trans m₂
  obtain C₃ : sv c base s₃ T1 = sv c base s T1 := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  obtain O₃ : sv c base s₃ ONEP = sv c base s ONEP := by
    rw [sv, mem₃]; exact sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₄
  simp only [← wordsVal_eq_val32] at v₄
  change sv c base t T4 = _ at v₄
  simp only [decide_eq_true_eq] at v₄
  change sv c base t T4 = if _ then sv c base s₃ ONEP else sv c base s₃ T1 at v₄
  rw [C₃, O₃] at v₄
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((k₁.keeps.trans (k₂.mono (by decide))).trans
      (u₃.keeps.mono (by decide))).trans (k₄.mono (by decide))
  · have U₁ : Unch base (slWk c [W0, T4, TMP]) s.mem s₁.mem :=
      unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
    apply unch_same U₁
    rw [← mem₃]
    exact (slot_frame (slots := [W0, T4, TMP]) (by simp) (Nat.le_refl _) O₄).mono
      (fun w hw => List.mem_append_left _ hw)
  · rw [v₄]; split
    · exact hOlt
    · exact hcval
  · rw [v₄]; split
    · rw [hOne, toM_one (unitMod_pow_two hc.p_odd (64 * c.n))]
    · rfl

end VG.Proof.EcKey.Compressed.X86

end

end

/-! # One machine round refines the functional P-224 root descent -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/DescentUpdate.lean`, which only this module imported.
section

/-! # The field updates in one P-224 descent round -/

section

namespace VG.Proof.EcKey.Compressed.X86


open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

def descentN : List FOp :=
  [.mul ACC ACC T4, .mul T4 T4 T4, .mul T0 T0 T4, .mul T1 T1 T1]
abbrev descentFields : List Nat := [ACC, T0, T1, T4]
abbrev descentWritten : List Nat := [ACC, T0, T1, T4, TMP]

theorem descentOps_eq (c : Cfg) : Impl.EcKey.Compressed.X86.descentOps c =
    descentN.map (FOp.rename c.sl) := rfl

theorem descentN_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps descentN e ACC = e ACC * e T4 ∧
    runOps descentN e T0 = e T0 * (e T4 * e T4) ∧
    runOps descentN e T1 = e T1 * e T1 := by
  simp only [descentN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [ACC, T0, T1, T4, Nat.reduceEqDiff, ↓reduceIte, and_self]

theorem descentN_reads : readsOk descentN descentFields = true := by decide
theorem descentN_slots : ∀ op ∈ descentN, ∀ x ∈ op.out :: op.ins, x ∈ descentFields := by decide
theorem descentN_out : ∀ op ∈ descentN, op.out ∈ descentWritten := by decide

structure DescentUpdatePost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : Keeps clob s s'
  unch : Unch base (slWk c descentWritten) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  r : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s T4)
  t : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T0) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s T0) *
      (toM c.C.p (2 ^ (64 * c.n)) (sv c base s T4) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s T4))
  c : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T1) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s T1) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s T1)

theorem descentUpdate_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ descentFields, sv c base s i < c.C.p) :
    WP isa (Impl.Weierstrass.X86.fprog c.SP
      (Impl.EcKey.Compressed.X86.descentOps c)) s (DescentUpdatePost c base s) := by
  have h7 := hc.n10
  obtain hL : Lay c.MP' size (· ∈ descentFields.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.SP c.MP' c.C.p size c.wk (· ∈ descentFields.map c.sl) := by
    refine ⟨slCall (MP'_n c) hc.fp, ?_, sl_below_wk c (by decide), sl_below_wk c (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain H : ∀ i ∈ descentFields, i < 45 := by decide
    exact sl_below_wk c (H i hi)
  obtain I : Inv c.MP' base size c.C.p (· ∈ descentFields.map c.sl) (descentFields.map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, fun _ h => h, ?_, fun _ _ => rfl⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hlt i hi
  rw [descentOps_eq]
  refine WP.mono (fprog_ok hL hW (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
    (fun op hop x hx => ?_)
    (readsOk_rename c.sl descentN_reads)) fun t ⟨PK, IT⟩ => ?_
  · obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (descentN_slots _ h₀ _ hi)
  have hw {i : Nat} (hi : i ∈ [ACC, T0, T1]) :
      c.sl i ∈ validAfter (descentN.map (FOp.rename c.sl)) (descentFields.map c.sl) := by
    apply (mem_validAfter _ _).mpr
    exact Or.inl (List.mem_map_of_mem (by
      obtain sub : ∀ i ∈ [ACC, T0, T1], i ∈ descentFields := by decide
      exact sub i hi))
  have val {i : Nat} (hi : i ∈ [ACC, T0, T1]) := IT.val _ (hw hi)
  obtain vr := val (i := ACC) (by simp)
  obtain vt := val (i := T0) (by simp)
  obtain vc := val (i := T1) (by simp)
  rw [congrFun (runOps_rename c.sl descentN _ fun _ _ _ h => sl_inj c hc.n0 h) ACC,
    (descentN_run _).1] at vr
  rw [congrFun (runOps_rename c.sl descentN _ fun _ _ _ h => sl_inj c hc.n0 h) T0,
    (descentN_run _).2.1] at vt
  rw [congrFun (runOps_rename c.sl descentN _ fun _ _ _ h => sl_inj c hc.n0 h) T1,
    (descentN_run _).2.2] at vc
  refine ⟨PK.scr hs, ⟨PK.gpr, PK.rd, PK.wr⟩, ?_, fun i hi => IT.lt _ (hw hi), vr, vt, vc⟩
  apply PK.unch.mono
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
    obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    exact List.mem_append_left _ (List.mem_map.mpr ⟨op₀.out, descentN_out _ h₀, by rw [FOp.out_rename]; rfl⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
    · exact List.mem_append_right _ (by simp [MP'_n, wkW])
    · exact List.mem_append_right _ (by simp [wkW])

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Impl.Ecdh.X86 (W0)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Impl.EcKey.Compressed (rootDescent)

def roundSlots : List Nat := [T3, W0, T4, TMP, ACC, T0, T1, T2]

abbrev fieldAt (c : Cfg) (base : Addr) (s : State) (i : Nat) :=
  toM c.C.p (2 ^ (64 * c.n)) (sv c base s i)

structure DescentRoundPost (c : Cfg) (base : Addr) (j : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : Keeps powClob s s'
  unch : Unch base (slWk c roundSlots) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  counter : s'.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 (j - 1)
  zf : s'.zf = some (decide (j - 1 = 0))
  descent : rootDescent (j - 1) (fieldAt c base s' ACC) (fieldAt c base s' T0) (fieldAt c base s' T1) =
    rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1)

theorem descentRound_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (Impl.EcKey.Compressed.X86.descentRound c) s (DescentRoundPost c base j s) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  change WP isa (.seq (Impl.EcKey.Compressed.X86.descentPower c)
    (.seq (Impl.EcKey.Compressed.X86.descentChoose c)
      (.seq (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.descentOps c))
        (.block (Impl.EcKey.Compressed.X86.descentCounter c))))) s _
  refine WP.seq (WP.mono (descentPower_ok hc hs hM (hlt _ (by simp)) hj hj' hword)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [T3, TMP]) : sv c base s₁ i = sv c base s i :=
    sv_unch U₁ h7 hn hi (apart_slWk hi hw)
  obtain M₁ : ModOkW c.MP' size c.C.p s₁.mem base := modP_of hc (by
    change sv c base s₁ MP = _
    rw [e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.seq (WP.mono (descentChoose_ok hc hs₁ M₁ lt₁
    (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hOne)) fun s₂ ⟨k₂, U₂, lt₂, v₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ∉ [W0, T4, TMP]) : sv c base s₂ i = sv c base s₁ i :=
    sv_unch U₂ h7 hn hi (apart_slWk hi hw)
  obtain M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide)]; exact M₁.val)
  obtain b₂ : fieldAt c base s₂ T4 =
      if fieldAt c base s T0 ^ (2 ^ (j - 1)) = 1 then 1 else fieldAt c base s T1 := by
    unfold fieldAt
    rw [v₂, v₁, e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (descentUpdate_ok hc hs₂ M₂ (by
    intro i hi
    obtain sub : ∀ i ∈ descentFields, i ∈ [ACC, T0, T1] ∨ i = T4 := by decide
    rcases sub i hi with h | rfl
    · have hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i h
      obtain hn₁ : i ∉ [T3, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [T3, TMP]) i h
      obtain hn₂ : i ∉ [W0, T4, TMP] := (by decide : ∀ i ∈ [ACC, T0, T1], i ∉ [W0, T4, TMP]) i h
      rw [e₂ hi45 hn₂, e₁ hi45 hn₁]; exact hlt i h
    · exact lt₂)) fun s₃ V => ?_)
  obtain U₁₂ := unch_same (slotsWk_widen U₁ (by decide : ∀ i ∈ [T3, TMP], i ∈ roundSlots))
    (slotsWk_widen U₂ (by decide : ∀ i ∈ [W0, T4, TMP], i ∈ roundSlots))
  obtain U₁₂₃ := unch_same U₁₂ (slotsWk_widen V.unch (by decide : ∀ i ∈ descentWritten, i ∈ roundSlots))
  obtain w₃ : s₃.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j := by
    obtain U : Unch base (slWk c [T3, W0, T4, TMP, ACC, T0, T1]) s.mem s₃.mem :=
      unch_same (unch_same (slotsWk_widen U₁ (by decide)) (slotsWk_widen U₂ (by decide)))
        (slotsWk_widen V.unch (by decide))
    rw [Unch.readW32 U (fun w hw => by
      have := (apart_slWk (c := c) (by decide : T2 < 45) (by decide : T2 ∉ [T3, W0, T4, TMP, ACC, T0, T1]) h7) w hw
      omega_using [h0, this]) (by have := sl_le c h7 (i := T2) (by decide); omega_using [hn, this]), hword]
  refine WP.mono (descentCounter_ok V.scr (by have := sl_le c h7 (i := T2) (by decide); omega_using [h0, this])
    hj (by omega_using [hj']) w₃) fun s₄ ⟨word₄, zf₄, k₄, O₄⟩ => ?_
  have e₄ {i : Nat} (hi : i < 45) (hw : i ≠ T2) : sv c base s₄ i = sv c base s₃ i :=
    O₄.wordsVal (by have := sl_apart c hw; omega_using [h0, this]) (by have := sl_le c h7 hi; omega_using [hn, this])
  refine ⟨V.scr.of_keeps k₄ (by decide), ?_,
    unch_same U₁₂₃ ((slot_frame (by decide : T2 ∈ roundSlots) (by omega_using [h0]) O₄).mono
      (fun w hw => List.mem_append_left _ hw)), ?_, word₄, zf₄, ?_⟩
  · exact ((k₁.trans (k₂.mono (by decide))).trans
      (V.keep.mono (by decide))).trans (k₄.mono (by simp [powClob]))
  · intro i hi
    obtain hi45 : i < 45 := (by decide : ∀ i ∈ [ACC, T0, T1], i < 45) i hi
    obtain hn₂ : i ≠ T2 := (by decide : ∀ i ∈ [ACC, T0, T1], i ≠ T2) i hi
    rw [e₄ hi45 hn₂]; exact V.lt i hi
  · have r₄ : fieldAt c base s₄ ACC = fieldAt c base s ACC * fieldAt c base s₂ T4 := by
      rw [fieldAt, e₄ (by decide) (by decide), V.r, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    obtain t₄ : fieldAt c base s₄ T0 = fieldAt c base s T0 * (fieldAt c base s₂ T4 * fieldAt c base s₂ T4) := by
      rw [fieldAt, e₄ (by decide) (by decide), V.t, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    obtain c₄ : fieldAt c base s₄ T1 = fieldAt c base s T1 * fieldAt c base s T1 := by
      rw [fieldAt, e₄ (by decide) (by decide), V.c, e₂ (by decide) (by decide), e₁ (by decide) (by decide)]
    conv => rhs; rw [show j = j - 1 + 1 by omega_using [hj], rootDescent]
    simp only [pow_eq_npow]
    rw [r₄, t₄, c₄, b₂]

end VG.Proof.EcKey.Compressed.X86

end

end

/-! # P-224's machine candidate refines its functional root algorithm -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/DescentLoop.lean`, which only this module imported.
section

/-! # The P-224 machine loop computes the functional root descent -/

section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Impl.EcKey.Compressed (rootDescent)

structure DescentInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  counter : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j
  keep : Keeps powClob s₀ s
  unch : Unch base (slWk c roundSlots) s₀.mem s.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  val : rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) =
    rootDescent count (fieldAt c base s₀ ACC) (fieldAt c base s₀ T0) (fieldAt c base s₀ T1)

theorem descentLoop_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {count : Nat}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hword : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 count) :
    WP isa (.loop (Impl.EcKey.Compressed.X86.descentRound c) .ne) s fun t =>
      Keeps powClob s t ∧ Unch base (slWk c roundSlots) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ fieldAt c base t ACC =
        rootDescent count (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  apply countLoop_ok (Inv := fun j t => DescentInv c base count s t j) (n := count)
  · intro j t hj hjc I
    refine WP.mono (descentRound_ok hc I.scr I.mod I.lt I.one hj (by omega) I.counter)
      fun u R => ?_
    have M : ModOkW c.MP' size c.C.p u.mem base := modP_of hc (by
      rw [sv_unch R.unch h7 hn (by decide) (apart_slWk (by decide) (by decide : MP ∉ roundSlots))]
      exact I.mod.val)
    have one : sv c base u ONEP = 2 ^ (64 * c.n) % c.C.p := by
      rw [sv]
      rw [sv_unch R.unch h7 hn (by decide) (apart_slWk (by decide) (by decide : ONEP ∉ roundSlots))]
      exact I.one
    exact ⟨⟨R.scr, M, one, R.counter, I.keep.trans R.keep, unch_same I.unch R.unch,
      R.lt, R.descent.trans I.val⟩, R.zf⟩
  · intro t I
    exact ⟨I.keep, I.unch, I.lt _ (by simp), I.val⟩
  · exact hcount
  · exact ⟨hs, hM, hOne, hword, Keeps.refl _ _, Unch.refl _ _ _, hlt, rfl⟩

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86
open VG.Impl.Ecdh.X86 (W2)
open VG.Impl.EcKey.Compressed.X86 (rootQ)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

theorem power_writes_subset (c : Cfg) {j : Nat} (hj : j = 1 ∨ j = 2) :
    ∀ w ∈ rootPowerWrites c j, w ∈ candidateWrites c := by
  intro w hw
  change w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    (slW c [ACC, PT, TMP] ++ wkW c) at hw
  rcases List.mem_append.mp hw with hw | hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · simp [candidateWrites, candidateSlots, slWk, slW]
    · rcases hj with rfl | rfl <;> simp [candidateWrites]
  · rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
        ((by decide : ∀ i ∈ [ACC, PT, TMP], i ∈ candidateSlots) i hi)))
    · exact List.mem_append_left _ (List.mem_append_right _ hw)

theorem candidateTonelli_correct {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3)
    (hq : 0 < rootQ c) :
    CandidateCorrect c (fun a => Impl.EcKey.Compressed.rootTonelli a (rootQ c) 96 (Fin.ofNat c.C.p 11)) := by
  intro base s hs hM hB hO
  have h7 := hc.n10
  have hn := hs.nowrap
  simp only [Impl.EcKey.Compressed.X86.rootCandidate, hp, ↓reduceIte]
  change WP isa (.seq (Impl.EcKey.Compressed.X86.tonelliPowers c)
    (.seq (.block (Impl.EcKey.Compressed.X86.tonelliSetup c))
      (.loop (Impl.EcKey.Compressed.X86.descentRound c) .ne))) s _
  refine WP.seq (WP.mono (tonelliPowers_ok hc hs hM hB hO)
    fun s₁ ⟨k₁, U₁, lt₁, ltR₁, t₁, r₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.seq (WP.mono (tonelliSetup_ok hc hs₁ ltR₁ lt₁)
    fun s₂ ⟨k₂, U₂, lt₂, counter₂, r₂, t₂, c₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have U₁₂ : Unch base (candidateWrites c) s.mem s₂.mem :=
    unch_same (U₁.mono (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact power_writes_subset c (.inl rfl) w hw
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
            ((by decide : ∀ i ∈ [T5], i ∈ candidateSlots) i hi)))
      · exact power_writes_subset c (.inr rfl) w hw))
      (U₂.mono (by
        intro w hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
          ((by decide : ∀ i ∈ [T0, ACC, T1, T2], i ∈ candidateSlots) i hi)))))
  have M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    rw [sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact hM.val)
  have one₂ : sv c base s₂ ONEP = 2 ^ (64 * c.n) % c.C.p := by
    rw [sv, sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact hO
  refine WP.mono (descentLoop_ok hc hs₂ M₂ one₂ lt₂ (by decide : 1 ≤ 95)
    (by decide : 95 < 2 ^ 31) counter₂) fun t ⟨kt, Ut, ltt, vt⟩ => ?_
  refine ⟨(k₁.trans (k₂.mono (by decide))).trans kt,
    unch_same U₁₂ (Ut.mono (by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
          ((by decide : ∀ i ∈ roundSlots, i ∈ candidateSlots) i hi)))
      · exact List.mem_append_left _ (List.mem_append_right _ hw))), ltt, ?_⟩
  change fieldAt c base t ACC = _
  rw [vt]
  change Impl.EcKey.Compressed.rootDescent 95
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ ACC))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T0))
    (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ T1)) = _
  rw [r₂, t₂, c₂, r₁, t₁, rootTonelli_eq_descent _ _ _ _ hq]
  simp only [pow_eq_npow]

end VG.Proof.EcKey.Compressed.X86
