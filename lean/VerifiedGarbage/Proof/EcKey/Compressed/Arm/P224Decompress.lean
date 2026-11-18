module

import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Umaal
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressMain
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.Verified
import VerifiedGarbage.Proof.P224.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm
meta import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P224.Arm
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Contract
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P224.Arm
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressFront
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.TaintMono
meta import VerifiedGarbage.Proof.Framework.Arm.TaintMono
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Frame
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Candidate
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Weierstrass.Sqrt
public import VerifiedGarbage.Impl.Ecdsa.Arm
public import VerifiedGarbage.Proof.Mont.Arm.Words
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Weierstrass.Arm
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.DecompressFront
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Candidate
meta import VerifiedGarbage.Impl.EcKey.Compressed.Root
meta import VerifiedGarbage.Proof.Weierstrass.RootTonelli
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Main
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
meta import VerifiedGarbage.Proof.Ecdh.Arm.Peer
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
meta import VerifiedGarbage.Proof.Mont.Words
meta import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.Proof.Weierstrass.Sqrt
meta import VerifiedGarbage.Impl.Ecdsa.Arm
meta import VerifiedGarbage.Proof.Mont.Arm.Words
meta import VerifiedGarbage.Proof.Weierstrass.Env
meta import VerifiedGarbage.Proof.Weierstrass.Unch
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Impl.Weierstrass.Arm
meta import VerifiedGarbage.Proof.Weierstrass.Arm.Const

/-! ### `EcKey.Compressed.Arm.RootCT`, which only this module used -/

section

/-! ### `EcKey.Compressed.Arm.Tonelli`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.Arm.TonelliSetup`, which this module and modules that import it used -/

section

/-! # Initialize P-224's descent from its two computed powers -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest wp_mov wp_str op2_imm)
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.EcKey.Compressed.Arm (rootQ)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

theorem tonelliSetup_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hr : sv c base s T5 < c.C.p) (ht : sv c base s ACC < c.C.p) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.tonelliSetup c)) s fun t =>
      Rest [.r4] s t ∧ Unch base (slW c [T0, ACC, T1, T2]) s.mem t.mem ∧
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
  obtain hT0 := sl_le c h7 (i := T0) (by decide)
  obtain hACC := sl_le c h7 (i := ACC) (by decide)
  obtain hT5 := sl_le c h7 (i := T5) (by decide)
  obtain hT1 := sl_le c h7 (i := T1) (by decide)
  obtain hT2 := sl_le c h7 (i := T2) (by decide)
  rw [Impl.EcKey.Compressed.Arm.tonelliSetup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs (by omega_using [hT0]) (by omega_using [hACC])
    (by have := sl_apart c (i := T0) (j := ACC) (by decide); omega_using [this])) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  simp only [← wordsVal_eq_val32] at v₁
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₁
  obtain hs₁ := hs.of_rest k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs₁ (by omega_using [hACC]) (by omega_using [hT5])
    (by have := sl_apart c (i := ACC) (j := T5) (by decide); omega_using [this])) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  simp only [← wordsVal_eq_val32] at v₂
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₂
  obtain hs₂ := hs₁.of_rest k₂ (by decide)
  obtain r₂ : sv c base s₂ ACC = sv c base s T5 := by
    rw [sv, v₂, O₁.wordsVal (sl_apart c (i := T5) (j := T0) (by decide)) (by omega_using [hn, hT5])]
  obtain t₂ : sv c base s₂ T0 = sv c base s ACC := by
    rw [sv, O₂.wordsVal (sl_apart c (i := T0) (j := ACC) (by decide)) (by omega_using [hn, hT0]), v₁]
  let z := Spec.Weierstrass.pow (Fin.ofNat c.C.p 11) (rootQ c)
  have zR : c.mont z.val < 2 ^ (64 * c.n) := Nat.lt_trans
    (Nat.mod_lt _ (by have := hc.p_ge; omega_using [hr])) hc.p_lt
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₂ hT1 zR) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_rest k₃ (by decide)
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  obtain hs₄ := hs₃.of_rest (u₄.rest (ws := [.r4]) (by simp)) (by decide)
  refine wp_str (hs₄.off_lt (by omega_using [h0, hT2])) (hs₄.ea (by omega_using [h0, hT2])) (hs₄.write (by omega_using [h0, hT2] : c.sl T2 + 4 ≤ size))
    fun t m₄ => WP.block_nil ?_
  obtain O₄ : Outside base (c.sl T2) 4 s₃.mem t.mem := by
    rw [m₄.mem, u₄.mem]
    exact writeW32_outside _ _ _ (by omega_using [hn, hT2])
  obtain v₄ : t.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 95 := by
    rw [m₄.mem, Mem.readW_writeW_self32, u₄.gpr]; rfl
  obtain k₄ : Rest [.r4] s₃ t := (u₄.rest (by simp)).trans (m₄.rest _)
  have e₃ {i : Nat} (hi : i < 45) (hw : i ≠ T1) : sv c base s₃ i = sv c base s₂ i :=
    O₃.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega_using [hn, this])
  have e₄ {i : Nat} (hi : i < 45) (hw : i ≠ T2) : sv c base t i = sv c base s₃ i :=
    O₄.wordsVal (by have := sl_apart c hw; omega_using [h0, this]) (by have := sl_le c h7 hi; omega_using [hn, this])
  obtain r₄ : sv c base t ACC = sv c base s T5 := by
    rw [e₄ (by decide) (by decide), e₃ (by decide) (by decide), r₂]
  obtain t₄ : sv c base t T0 = sv c base s ACC := by
    rw [e₄ (by decide) (by decide), e₃ (by decide) (by decide), t₂]
  obtain c₄ : sv c base t T1 = c.mont z.val := by
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

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.TonelliPowers`, which this module and modules that import it used -/

section

/-! # The two initial powers in P-224's root recovery -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdh.Arm (W2)
open VG.Impl.EcKey.Compressed.Arm (rootQ)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

abbrev tonelliPowerWrites (c : Cfg) :=
  rootPowerWrites c 1 ++ slW c [T5] ++ rootPowerWrites c 2

theorem tonelliPowers_ok {c : Cfg} (hc : CfgOk c)
    {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.Arm.tonelliPowers c) s fun t =>
      Rest powClob s t ∧ Unch base (tonelliPowerWrites c) s.mem t.mem ∧
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
  change WP isa (.seq (Impl.EcKey.Compressed.Arm.rootPower c ((rootQ c + 1) / 2) 1)
    (.seq (.block (copy (2 * c.n) (c.sl T5) (c.sl ACC)))
      (Impl.EcKey.Compressed.Arm.rootPower c (rootQ c) 2))) s _
  refine WP.seq (WP.mono (rootPower_ok hc (by decide) he hs hf hM hB hO)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  have hs₁ := hs.of_rest k₁ (by decide)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [EXPP, ACC, PT, TMP]) :
      sv c base s₁ i = sv c base s i := sv_unch U₁ h7 hn hi (rootPower_apart hc hi hw)
  refine WP.seq (WP.mono (copy_ok (2 * c.n) hs₁ (by have := sl_le c h7 (i := T5) (by decide); omega_using [this]) (by have := sl_le c h7 (i := ACC) (by decide); omega_using [this])
    (by have := sl_apart c (i := T5) (j := ACC) (by decide); omega_using [this])) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_)
  simp only [← wordsVal_eq_val32] at v₂
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₂
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ≠ T5) : sv c base s₂ i = sv c base s₁ i :=
    O₂.wordsVal (sl_apart c hw) (by have := sl_le c h7 hi; omega_using [hn, this])
  have M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide), e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.mono (rootPower_ok hc (by decide) hqR hs₂ ((hf.of_rest k₁).of_rest k₂) M₂
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

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.DescentRound`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.Arm.DescentPower`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.Arm.Square`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.Arm.Counter`, which this module and modules that import it used -/

section

/-! # Public loop counters for P-224 coordinate recovery -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

theorem testCounter_ok {j : Nat} (s : State) (hj : j < 2 ^ 32)
    (hb : s.gpr .r11 = BitVec.ofNat 32 j) :
    WP isa (.block [testCounter]) s fun t =>
      t.z = decide (j = 0) ∧ Rest [] s t ∧ t.mem = s.mem :=
  wp_testCounter hj hb fun _ f hz => WP.block_nil ⟨hz, f.rest [], f.mem⟩

theorem descentCounter_ok {c : Cfg} {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hd : c.sl T2 + 4 ≤ size) (hj : 1 ≤ j) (hj' : j < 2 ^ 32)
    (hw : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.descentCounter c)) s fun t =>
      t.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 (j - 1) ∧
      t.z = decide (j - 1 = 0) ∧ Rest [.r11] s t ∧
      Outside base (c.sl T2) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.Arm.descentCounter
  refine wp_ldr (hs.off_lt (by omega_using [hd])) (hs.ea (by omega_using [hd])) (hs.read hd) fun s₁ u₁ => ?_
  refine wp_decCounter hj (by rw [u₁.gpr, hw]) fun s₂ u₂ => ?_
  have K : Rest [.r11] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have hs₂ := hs.of_rest K (by decide)
  refine wp_str (hs₂.off_lt (by omega_using [hd])) (hs₂.ea (by omega_using [hd])) (hs₂.write hd) fun s₃ m₃ => ?_
  refine wp_testCounter (j := j - 1) (by omega_using [hj']) (by rw [m₃.gpr, u₂.gpr]) fun t f hz => WP.block_nil ?_
  refine ⟨?_, hz, K.trans ((m₃.rest _).trans (f.rest _)), ?_⟩
  · rw [f.mem, m₃.mem, Mem.readW_writeW_self32, u₂.gpr]
  · rw [f.mem, m₃.mem, u₂.mem, u₁.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega_using [hd, this])

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! # Repeated squaring for the P-224 root descent

The backwards invariant `current^(2^remaining) = original^(2^count)`
avoids any assumption about the input being a square or nonzero.
-/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest)

structure SquareInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  mod : ModOkW c.MP' size c.C.p s.mem base
  counter : s.gpr .r11 = BitVec.ofNat 32 j
  keep : Rest powClob s₀ s
  unch : Unch base (slWk c [T3, TMP]) s₀.mem s.mem
  lt : sv c base s T3 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ j) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s₀ T3) ^ (2 ^ count)

theorem squareStep_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {count j : Nat}
    (hj : 1 ≤ j) (hcount : count < 2 ^ 31) (hjc : j ≤ count) {s₀ s : State}
    (I : SquareInv c base count s₀ s j) :
    WP isa (Impl.EcKey.Compressed.Arm.squareStep c) s fun s' =>
      SquareInv c base count s₀ s' (j - 1) ∧ s'.z = decide (j - 1 = 0) := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  rw [Impl.EcKey.Compressed.Arm.squareStep]
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 I.scr I.far
    (o := T3) (a := T3) (b := T3) (by decide) (by decide) (by decide) I.lt)
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr I.scr
  have hm₁ := I.mod.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have hb₁ : s₁.gpr .r11 = BitVec.ofNat 32 j :=
    (k₁.rest.gpr _ (by decide)).trans I.counter
  have U₁ : Unch base (slWk c [T3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  have v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ T3) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ 2 := by
    rw [toM_mul (unitMod_pow_two hc.p_odd (64 * c.n)) e₁, Lean.Grind.Semiring.pow_two]
  refine wp_decCounter hj hb₁ fun s₂ u₂ => ?_
  refine wp_testCounter (j := j - 1) (by omega_using [hcount, hjc]) (by rw [u₂.gpr]) fun s₃ f₃ hz₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s₁.mem := f₃.mem.trans u₂.mem
  have K : Rest powClob s₁ s₃ := (u₂.rest (by simp [powClob])).trans (f₃.rest _)
  refine ⟨⟨hs₁.of_rest K (by decide), (I.far.of_rest k₁.rest).of_rest K,
    by rw [m₃]; exact hm₁, by rw [f₃.gpr, u₂.gpr],
    (I.keep.trans (k₁.rest.mono (by decide))).trans K, ?_,
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
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .r11 = BitVec.ofNat 32 count)
    (hcount : count < 2 ^ 31) (hpos : 1 ≤ count) :
    WP isa (.loop (Impl.EcKey.Compressed.Arm.squareStep c) .ne) s fun s' =>
      Rest powClob s s' ∧ Unch base (slWk c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  apply countLoop_ok (Inv := fun j t => SquareInv c base count s t j)
    (fun j t hj hjc hi => squareStep_ok hc hj hcount hjc hi) (n := count)
  · intro t I
    refine ⟨I.keep, I.unch, I.lt, ?_⟩
    simpa only [Nat.pow_zero, Lean.Grind.Semiring.pow_one] using I.val
  · exact hpos
  · exact ⟨hs, hf, hM, hb, Rest.refl _ _, Unch.refl _ _ _, hlt, rfl⟩

theorem squarePower_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {count : Nat} {s : State}
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T3 < c.C.p) (hb : s.gpr .r11 = BitVec.ofNat 32 count)
    (hcount : count < 2 ^ 31) :
    WP isa (Impl.EcKey.Compressed.Arm.squarePower c) s fun s' =>
      Rest powClob s s' ∧ Unch base (slWk c [T3, TMP]) s.mem s'.mem ∧
      sv c base s' T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T3) ^ (2 ^ count) := by
  rw [Impl.EcKey.Compressed.Arm.squarePower]
  refine WP.seq (WP.mono (testCounter_ok s (by omega_using [hcount]) hb) fun s₁ ⟨hz₁, k₁, m₁⟩ => ?_)
  have hs₁ := hs.of_rest k₁ (by decide)
  refine WP.ite (decide (count = 0)) (by rw [VG.Proof.X25519.Arm.eval_eq, hz₁]) (fun hz => ?_) (fun hn => ?_)
  · have hn : count = 0 := of_decide_eq_true hz
    apply WP.block_nil
    refine ⟨k₁.mono (by simp), ?_, ?_, ?_⟩
    · rw [m₁]
      exact Unch.refl _ _ _
    · rw [sv, m₁]
      exact hlt
    · rw [sv, m₁, hn, Nat.pow_zero, Lean.Grind.Semiring.pow_one]
  · have hn : count ≠ 0 := of_decide_eq_false hn
    refine WP.mono (squareLoop_ok hc hs₁ (hf.of_rest k₁) (m₁ ▸ hM) (by rw [sv, m₁]; exact hlt)
      (by rw [k₁.gpr _ (by decide), hb]) hcount (by omega_using [hn])) fun t ⟨kt, Ut, lt, vt⟩ => ?_
    refine ⟨(k₁.mono (by simp)).trans kt, ?_, lt, ?_⟩
    · rw [← m₁]
      exact Ut
    · simpa only [sv, m₁] using vt

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! # The tested power in a P-224 descent round -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem descentPower_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : sv c base s T0 < c.C.p) (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (Impl.EcKey.Compressed.Arm.descentPower c) s fun t =>
      Rest powClob s t ∧ Unch base (slWk c [T3, TMP]) s.mem t.mem ∧
      sv c base t T3 < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base t T3) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s T0) ^ (2 ^ (j - 1)) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  have h3 := sl_le c h7 (i := T3) (by decide)
  have h2 := sl_le c h7 (i := T2) (by decide)
  change WP isa (.seq (.block (copy (2 * c.n) (c.sl T3) (c.sl T0) ++
    [.ldr .r11 wb (c.sl T2), decCounter])) (Impl.EcKey.Compressed.Arm.squarePower c)) s _
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs (by omega_using [h3]) (by have := sl_le c h7 (i := T0) (by decide); omega_using [this])
    (by have := sl_apart c (i := T3) (j := T0) (by decide); omega_using [this])) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₁
  have v₁' : sv c base s₁ T3 = sv c base s T0 := by
    simpa only [sv, wordsVal_eq_val32] using v₁
  have hs₁ := hs.of_rest k₁ (by decide)
  refine wp_ldr (hs₁.off_lt (by omega_using [h0, h2])) (hs₁.ea (by omega_using [h0, h2])) (hs₁.read (by omega_using [h0, h2] : c.sl T2 + 4 ≤ size)) fun s₂ u₂ => ?_
  have hb₂ : s₂.gpr .r11 = BitVec.ofNat 32 j := by
    rw [u₂.gpr, BitVec.eq_of_toNat_eq (O₁.w32 (by have := sl_apart c (i := T2) (j := T3) (by decide); omega_using [h0, this]) (by omega_using [hn, h2])), hword]
  refine wp_decCounter hj hb₂ fun s₃ u₃ => WP.block_nil ?_
  have K : Rest powClob s s₃ := (k₁.mono (by decide)).trans
    ((u₂.rest (by simp [powClob])).trans (u₃.rest (by simp [powClob])))
  have hs₃ := hs.of_rest K (by decide)
  have m₃ : s₃.mem = s₁.mem := u₃.mem.trans u₂.mem
  have M₃ : ModOkW c.MP' size c.C.p s₃.mem base := modP_of hc (by
    rw [m₃, O₁.wordsVal (sl_apart c (i := MP) (j := T3) (by decide))
      (by have := sl_le c h7 (i := MP) (by decide); omega_using [hn, this])]
    exact hM.val)
  refine WP.mono (squarePower_ok hc hs₃ (hf.of_rest K) M₃
    (by rw [sv, m₃]; change sv c base s₁ T3 < _; rw [v₁']; exact hlt) u₃.gpr (by omega_using [hj']))
    fun t ⟨Kt, Ut, lt, vt⟩ => ?_
  refine ⟨K.trans Kt, ?_, lt, ?_⟩
  · rw [m₃] at Ut
    exact unch_same ((slot_frame (slots := [T3, TMP]) (by simp) (Nat.le_refl _) O₁).mono
      (fun w hw => List.mem_append_left _ hw)) Ut
  · simpa only [sv, m₃, show wordsVal s₁.mem base (c.sl T3) c.n = sv c base s T0 from v₁'] using vt

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.DescentChoose`, which only this module used -/

section

/-! # Select the correction factor of the P-224 descent -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdh.Arm (W0)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_dp op2_reg op2_imm dpVal)

theorem zero_ok {c : Cfg} {s : State} {base : Addr} {a : Nat} (hs : Scr s base size) (h0 : 0 < c.n)
    (ha : a + 8 * c.n ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.zeroMask c a)) s fun t =>
      t.gpr .r5 = mask32 (wordsVal s.mem base a c.n = 0) ∧
      Rest [.r4, .r5] s t ∧ t.mem = s.mem := by
  unfold Impl.EcKey.Compressed.Arm.zeroMask
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c hs h0 ha) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_imm (by decide)) fun t u₄ => WP.block_nil ?_
  refine ⟨?_, k₁.trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))), ?_⟩
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), e₁]
    simp only [dpVal]
    rw [mask_not]
    simp only [ne_eq, Decidable.not_not]
  · rw [u₄.mem, u₃.mem, u₂.mem, m₁]

theorem descentChoose_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hf : Far s base 8192) (_hM : ModOkW c.MP' size c.C.p s.mem base)
    (ht : sv c base s T3 < c.C.p) (hcval : sv c base s T1 < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.Arm.descentChoose c) s fun t =>
      Rest Mont.callClob s t ∧ Unch base (slWk c [W0, T4, TMP]) s.mem t.mem ∧
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
  rw [Impl.EcKey.Compressed.Arm.descentChoose]
  refine WP.seq (WP.mono (slSub_ok hc.fp (MP'_n c) h7 hs hf (o := W0) (a := T3) (b := ONEP)
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
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  obtain hs₃ := (hs₁.of_rest k₂ (by decide)).of_rest (u₃.rest (ws := [.r10]) (by simp)) (by decide)
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
  · exact ((k₁.rest.trans (k₂.mono (by decide))).trans
      (u₃.rest (by simp [Mont.callClob, clob]))).trans (k₄.mono (by decide))
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

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! # One machine round refines the functional P-224 root descent -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/Arm/DescentUpdate.lean`, which only this module imported.
section

/-! # The field updates in one P-224 descent round -/

section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

def descentN : List FOp :=
  [.mul ACC ACC T4, .mul T4 T4 T4, .mul T0 T0 T4, .mul T1 T1 T1]
abbrev descentFields : List Nat := [ACC, T0, T1, T4]
abbrev descentWritten : List Nat := [ACC, T0, T1, T4, TMP]

theorem descentOps_eq (c : Cfg) : Impl.EcKey.Compressed.Arm.descentOps c =
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
  keep : Rest Mont.callClob s s'
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
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ descentFields, sv c base s i < c.C.p) :
    WP isa (Impl.Weierstrass.Arm.fprog c.SP
      (Impl.EcKey.Compressed.Arm.descentOps c) c.umaal) s (DescentUpdatePost c base s) := by
  have h7 := hc.n10
  obtain hL : Lay c.MP' size (· ∈ descentFields.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.MP' size c.wk (· ∈ descentFields.map c.sl) := by
    refine ⟨wk_le c h7 rfl, ?_, sl_below_wk c h7 (by decide), sl_below_wk c h7 (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain H : ∀ i ∈ descentFields, i < 45 := by decide
    exact sl_below_wk c h7 (H i hi)
  obtain I : Inv c.MP' base size c.C.p (· ∈ descentFields.map c.sl) (descentFields.map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base o c.n)) s := by
    refine ⟨hs, hM, fun _ h => h, ?_, fun _ _ => rfl, hf⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hlt i hi
  rw [descentOps_eq]
  refine WP.mono (fprog_ok hL hW hc.fp (unitMod_pow_two hc.p_odd (64 * c.n)) _ I
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
  refine ⟨PK.scr hs, PK.rest, ?_, fun i hi => IT.lt _ (hw hi), vr, vt, vc⟩
  apply PK.unch.mono
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
    obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
    exact List.mem_append_left _ (List.mem_map.mpr ⟨op₀.out, descentN_out _ h₀, by rw [FOp.out_rename]; rfl⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
    · exact List.mem_append_right _ (by simp [MP'_n])

end VG.Proof.EcKey.Compressed.Arm
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (W0)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Impl.EcKey.Compressed (rootDescent)

def roundSlots : List Nat := [T3, W0, T4, TMP, ACC, T0, T1, T2]

abbrev fieldAt (c : Cfg) (base : Addr) (s : State) (i : Nat) :=
  toM c.C.p (2 ^ (64 * c.n)) (sv c base s i)

structure DescentRoundPost (c : Cfg) (base : Addr) (j : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : Rest powClob s s'
  unch : Unch base (slWk c roundSlots) s.mem s'.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s' i < c.C.p
  counter : s'.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 (j - 1)
  zf : s'.z = decide (j - 1 = 0)
  descent : rootDescent (j - 1) (fieldAt c base s' ACC) (fieldAt c base s' T0) (fieldAt c base s' T1) =
    rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1)

theorem descentRound_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {j : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hword : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (Impl.EcKey.Compressed.Arm.descentRound c) s (DescentRoundPost c base j s) := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hn := hs.nowrap
  change WP isa (.seq (Impl.EcKey.Compressed.Arm.descentPower c)
    (.seq (Impl.EcKey.Compressed.Arm.descentChoose c)
      (.seq (Impl.Weierstrass.Arm.fprog c.SP (Impl.EcKey.Compressed.Arm.descentOps c) c.umaal)
        (.block (Impl.EcKey.Compressed.Arm.descentCounter c))))) s _
  refine WP.seq (WP.mono (descentPower_ok hc hs hf hM (hlt _ (by simp)) hj hj' hword)
    fun s₁ ⟨k₁, U₁, lt₁, v₁⟩ => ?_)
  obtain hs₁ := hs.of_rest k₁ (by decide)
  have e₁ {i : Nat} (hi : i < 45) (hw : i ∉ [T3, TMP]) : sv c base s₁ i = sv c base s i :=
    sv_unch U₁ h7 hn hi (apart_slWk h7 hi hw)
  obtain M₁ : ModOkW c.MP' size c.C.p s₁.mem base := modP_of hc (by
    change sv c base s₁ MP = _
    rw [e₁ (by decide) (by decide)]; exact hM.val)
  refine WP.seq (WP.mono (descentChoose_ok hc hs₁ (hf.of_rest k₁) M₁ lt₁
    (by rw [e₁ (by decide) (by decide)]; exact hlt _ (by simp))
    (by rw [e₁ (by decide) (by decide)]; exact hOne)) fun s₂ ⟨k₂, U₂, lt₂, v₂⟩ => ?_)
  obtain hs₂ := hs₁.of_rest k₂ (by decide)
  have e₂ {i : Nat} (hi : i < 45) (hw : i ∉ [W0, T4, TMP]) : sv c base s₂ i = sv c base s₁ i :=
    sv_unch U₂ h7 hn hi (apart_slWk h7 hi hw)
  obtain M₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = _
    rw [e₂ (by decide) (by decide)]; exact M₁.val)
  obtain b₂ : fieldAt c base s₂ T4 =
      if fieldAt c base s T0 ^ (2 ^ (j - 1)) = 1 then 1 else fieldAt c base s T1 := by
    unfold fieldAt
    rw [v₂, v₁, e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (descentUpdate_ok hc hs₂ ((hf.of_rest k₁).of_rest k₂) M₂ (by
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
      have := apart_slWk (c := c) h7 (by decide : T2 < 45) (by decide : T2 ∉ [T3, W0, T4, TMP, ACC, T0, T1]) w hw
      omega_using [h0, this]) (by have := sl_le c h7 (i := T2) (by decide); omega_using [hn, this]), hword]
  refine WP.mono (descentCounter_ok V.scr (by have := sl_le c h7 (i := T2) (by decide); omega_using [h0, this])
    hj (by omega_using [hj']) w₃) fun s₄ ⟨word₄, zf₄, k₄, O₄⟩ => ?_
  have e₄ {i : Nat} (hi : i < 45) (hw : i ≠ T2) : sv c base s₄ i = sv c base s₃ i :=
    O₄.wordsVal (by have := sl_apart c hw; omega_using [h0, this]) (by have := sl_le c h7 hi; omega_using [hn, this])
  refine ⟨V.scr.of_rest k₄ (by decide), ?_,
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

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! # P-224's machine candidate refines its functional root algorithm -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/Arm/DescentLoop.lean`, which only this module imported.
section

/-! # The P-224 machine loop computes the functional root descent -/

section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Impl.EcKey.Compressed (rootDescent)

structure DescentInv (c : Cfg) (base : Addr) (count : Nat) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  mod : ModOkW c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  counter : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j
  keep : Rest powClob s₀ s
  unch : Unch base (slWk c roundSlots) s₀.mem s.mem
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  val : rootDescent j (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) =
    rootDescent count (fieldAt c base s₀ ACC) (fieldAt c base s₀ T0) (fieldAt c base s₀ T1)

theorem descentLoop_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {count : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hOne : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hlt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p)
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hword : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 count) :
    WP isa (.loop (Impl.EcKey.Compressed.Arm.descentRound c) .ne) s fun t =>
      Rest powClob s t ∧ Unch base (slWk c roundSlots) s.mem t.mem ∧
      sv c base t ACC < c.C.p ∧ fieldAt c base t ACC =
        rootDescent count (fieldAt c base s ACC) (fieldAt c base s T0) (fieldAt c base s T1) := by
  have hn := hs.nowrap
  have h7 := hc.n10
  apply countLoop_ok (Inv := fun j t => DescentInv c base count s t j) (n := count)
  · intro j t hj hjc I
    refine WP.mono (descentRound_ok hc I.scr I.far I.mod I.lt I.one hj (by omega) I.counter)
      fun u R => ?_
    have M : ModOkW c.MP' size c.C.p u.mem base := modP_of hc (by
      rw [sv_unch R.unch h7 hn (by decide) (apart_slWk h7 (by decide) (by decide : MP ∉ roundSlots))]
      exact I.mod.val)
    have one : sv c base u ONEP = 2 ^ (64 * c.n) % c.C.p := by
      rw [sv]
      rw [sv_unch R.unch h7 hn (by decide) (apart_slWk h7 (by decide) (by decide : ONEP ∉ roundSlots))]
      exact I.one
    exact ⟨⟨R.scr, I.far.of_rest R.keep, M, one, R.counter, I.keep.trans R.keep, unch_same I.unch R.unch,
      R.lt, R.descent.trans I.val⟩, R.zf⟩
  · intro t I
    exact ⟨I.keep, I.unch, I.lt _ (by simp), I.val⟩
  · exact hcount
  · exact ⟨hs, hf, hM, hOne, hword, Rest.refl _ _, Unch.refl _ _ _, hlt, rfl⟩

end VG.Proof.EcKey.Compressed.Arm
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (W2)
open VG.Impl.EcKey.Compressed.Arm (rootQ)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

theorem power_writes_subset (c : Cfg) {j : Nat} (hj : j = 1 ∨ j = 2) :
    ∀ w ∈ rootPowerWrites c j, w ∈ candidateWrites c := by
  intro w hw
  change w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    (slW c [ACC, PT, TMP] ++ [(c.wk, 64 * c.n)]) at hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (rfl | rfl) | hw | rfl
  · simp [candidateWrites, candidateSlots, slWk, slW]
  · rcases hj with rfl | rfl <;> simp [candidateWrites]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
      ((by decide : ∀ i ∈ [ACC, PT, TMP], i ∈ candidateSlots) i hi)))
  · exact List.mem_append_left _ (List.mem_append_right _ (by simp))

theorem candidateTonelli_correct {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3)
    (hq : 0 < rootQ c) :
    CandidateCorrect c (fun a => Impl.EcKey.Compressed.rootTonelli a (rootQ c) 96 (Fin.ofNat c.C.p 11)) := by
  intro base s hs hf hM hB hO
  have h7 := hc.n10
  have hn := hs.nowrap
  simp only [Impl.EcKey.Compressed.Arm.rootCandidate, hp, ↓reduceIte]
  change WP isa (.seq (Impl.EcKey.Compressed.Arm.tonelliPowers c)
    (.seq (.block (Impl.EcKey.Compressed.Arm.tonelliSetup c))
      (.loop (Impl.EcKey.Compressed.Arm.descentRound c) .ne))) s _
  refine WP.seq (WP.mono (tonelliPowers_ok hc hs hf hM hB hO)
    fun s₁ ⟨k₁, U₁, lt₁, ltR₁, t₁, r₁⟩ => ?_)
  have hs₁ := hs.of_rest k₁ (by decide)
  refine WP.seq (WP.mono (tonelliSetup_ok hc hs₁ ltR₁ lt₁)
    fun s₂ ⟨k₂, U₂, lt₂, counter₂, r₂, t₂, c₂⟩ => ?_)
  have hs₂ := hs₁.of_rest k₂ (by decide)
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
  refine WP.mono (descentLoop_ok hc hs₂ ((hf.of_rest k₁).of_rest k₂) M₂ one₂ lt₂ (by decide : 1 ≤ 95)
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

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! # Carry P-224's public counter through existing field calls

The field calls preserve the scratch counter, but their pointer-based
stores cause the syntactic taint analysis to forget it. RelCT combines the
existing taint checks with the already-proved counter invariants.
-/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr)

def RootPublic (s t : State) : Prop := s.gpr .r12 = t.gpr .r12 ∧ s.gpr .lr = t.gpr .lr

def PowerPublic (s t : State) : Prop := RootPublic s t ∧ s.gpr .r11 = t.gpr .r11

def descentPrefix (c : Cfg) : Prog isa :=
  .block (copy (2 * c.n) (c.sl T3) (c.sl T0) ++ [.ldr .r11 wb (c.sl T2), decCounter])

def descentRest (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.Arm.descentChoose c)
    (.seq (fprog c.SP (Impl.EcKey.Compressed.Arm.descentOps c) c.umaal)
      (.block (Impl.EcKey.Compressed.Arm.descentCounter c)))

structure LoopState (c : Cfg) (base : Addr) (j : Nat) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  mod : ModOkW c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  counter : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j

def LoopPair (c : Cfg) (j : Nat) (s t : State) : Prop :=
  ∃ base, LoopState c base j s ∧ LoopState c base j t ∧ RootPublic s t

theorem RootPublic.keep {s t u v : State} (hp : RootPublic s t)
    (K : Rest powClob s u) (L : Rest powClob t v) : RootPublic u v := by
  rcases hp with ⟨hb, ho⟩
  exact ⟨by rw [K.gpr _ (by decide), L.gpr _ (by decide), hb],
    by rw [K.gpr _ (by decide), L.gpr _ (by decide), ho]⟩

theorem rel_of_ct {c : Prog isa} {P : State → State → Prop}
    (h : ConstantTime isa (fun _ => True) P c) : RelCT isa P c (fun _ _ => True) :=
  fun _ _ _ _ _ _ hp e₁ e₂ => ⟨h _ _ _ _ _ _ trivial trivial hp e₁ e₂, trivial⟩

theorem descentPrefix_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {j : Nat} {s : State}
    (hs : Scr s base size) (hj : 1 ≤ j)
    (hw : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (descentPrefix c) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (j - 1) ∧ Rest powClob s t := by
  have h7 := hc.n10
  have h0 := hc.n0
  have h3 := sl_le c h7 (i := T3) (by decide)
  have h2 := sl_le c h7 (i := T2) (by decide)
  unfold descentPrefix
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * c.n) hs (by omega_using [h3])
    (by have := sl_le c h7 (i := T0) (by decide); omega_using [this])
    (by have := sl_apart c (i := T3) (j := T0) (by decide); omega_using [this])) fun s₁ ⟨_, K₁, O₁⟩ => ?_
  rw [show 4 * (2 * c.n) = 8 * c.n by omega_using []] at O₁
  have hs₁ := hs.of_rest K₁ (by decide)
  refine wp_ldr (hs₁.off_lt (by omega_using [h0, h2])) (hs₁.ea (by omega_using [h0, h2])) (hs₁.read (by omega_using [h0, h2] : c.sl T2 + 4 ≤ size))
    fun s₂ U₂ => ?_
  have hb₂ : s₂.gpr .r11 = BitVec.ofNat 32 j := by
    rw [U₂.gpr, BitVec.eq_of_toNat_eq (O₁.w32
      (by have := sl_apart c (i := T2) (j := T3) (by decide); omega_using [h0, this])
      (by have := hs.nowrap; omega_using [h2, this])), hw]
  refine wp_decCounter hj hb₂ fun t U₃ => WP.block_nil
    ⟨U₃.gpr, (K₁.mono (by decide)).trans
      ((U₂.rest (by simp [powClob])).trans (U₃.rest (by simp [powClob])))⟩

theorem descentRound_rel {c : Cfg} (hc : CfgOk c) {j : Nat}
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hprefix : ConstantTime isa (fun _ => True) RootPublic (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) PowerPublic (Impl.EcKey.Compressed.Arm.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) RootPublic (descentRest c)) :
    RelCT isa (LoopPair c j) (Impl.EcKey.Compressed.Arm.descentRound c) (fun _ _ => True) := by
  have Hprefix := ((rel_of_ct hprefix).mono (P' := LoopPair c j)
    (fun _ _ ⟨_, _, _, hp⟩ => hp) (fun _ _ _ => trivial)).wpDep
    (F := fun (s t : State) => t.gpr .r11 = BitVec.ofNat 32 (j - 1) ∧ Rest powClob s t)
    (fun s t ⟨base, I, J, _⟩ =>
      ⟨descentPrefix_ok hc I.scr hj I.counter, descentPrefix_ok hc J.scr hj J.counter⟩)
  have Hpower : RelCT isa (LoopPair c j) (Impl.EcKey.Compressed.Arm.descentPower c) (fun _ _ => True) := by
    apply RelCT.seq Hprefix
    apply (rel_of_ct hsquare).mono
    · rintro _ _ ⟨_, s, t, ⟨_, _, _, hp⟩, ⟨hs, K⟩, ⟨ht, L⟩⟩
      exact ⟨hp.keep K L, hs.trans ht.symm⟩
    · exact fun _ _ _ => trivial
  have Hpower' := Hpower.wpDep
    (F := fun (s t : State) => Rest powClob s t)
    (fun s t ⟨base, I, J, _⟩ => ⟨
      WP.mono (descentPower_ok hc I.scr I.far I.mod (I.lt _ (by simp)) hj hj' I.counter)
        (fun _ h => h.1),
      WP.mono (descentPower_ok hc J.scr J.far J.mod (J.lt _ (by simp)) hj hj' J.counter)
        (fun _ h => h.1)⟩)
  apply RelCT.seq Hpower'
  apply (rel_of_ct hrest).mono
  · rintro _ _ ⟨_, _, _, ⟨_, _, _, hp⟩, K, L⟩
    exact hp.keep K L
  · exact fun _ _ _ => trivial

theorem LoopState.step {c : Cfg} (hc : CfgOk c) {base : Addr} {j : Nat} {s t : State}
    (I : LoopState c base j s) (R : DescentRoundPost c base j s t) : LoopState c base (j - 1) t := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  refine ⟨R.scr, I.far.of_rest R.keep, modP_of hc ?_, ?_, R.lt, R.counter⟩
  · rw [sv_unch R.unch h7 hn (by decide) (apart_slWk h7 (by decide) (by decide : MP ∉ roundSlots))]
    exact I.mod.val
  · rw [sv, sv_unch R.unch h7 hn (by decide)
      (apart_slWk h7 (by decide) (by decide : ONEP ∉ roundSlots))]
    exact I.one

theorem descentLoop_rel {c : Cfg} (hc : CfgOk c) {count : Nat}
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hprefix : ConstantTime isa (fun _ => True) RootPublic (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) PowerPublic (Impl.EcKey.Compressed.Arm.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) RootPublic (descentRest c)) :
    RelCT isa (LoopPair c count) (.loop (Impl.EcKey.Compressed.Arm.descentRound c) .ne) RootPublic := by
  have H : ∀ j, RelCT isa (fun s t => 1 ≤ j ∧ j < 2 ^ 31 ∧ LoopPair c j s t)
      (Impl.EcKey.Compressed.Arm.descentRound c) fun u v =>
      isa.eval .ne u = isa.eval .ne v ∧ (isa.eval .ne u = some false → RootPublic u v) ∧
      (isa.eval .ne u = some true → ∃ k < j, 1 ≤ k ∧ k < 2 ^ 31 ∧ LoopPair c k u v) := by
    intro j
    intro s t ts tt u v hp es et
    rcases hp with ⟨hj, hj', base, I, J, hpub⟩
    obtain ⟨ht, _⟩ := descentRound_rel hc hj hj' hprefix hsquare hrest s t ts tt u v
      ⟨base, I, J, hpub⟩ es et
    obtain ⟨_, u', eu, R⟩ := descentRound_ok hc I.scr I.far I.mod I.lt I.one hj hj' I.counter
    obtain ⟨_, rfl⟩ := Exec.det es eu
    obtain ⟨_, v', ev, S⟩ := descentRound_ok hc J.scr J.far J.mod J.lt J.one hj hj' J.counter
    obtain ⟨_, rfl⟩ := Exec.det et ev
    refine ⟨ht, ?_, fun _ => hpub.keep R.keep S.keep, ?_⟩
    · rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, R.zf, S.zf]
    · intro he
      have hn : j - 1 ≠ 0 := by
        intro hz
        rw [VG.Proof.X25519.Arm.eval_ne, R.zf, decide_eq_true hz] at he
        cases he
      exact ⟨j - 1, by omega_using [hj], by omega_using [hn], by omega_using [hj'], base, I.step hc R, J.step hc S,
        hpub.keep R.keep S.keep⟩
  exact (RelCT.loop (fun j s t => 1 ≤ j ∧ j < 2 ^ 31 ∧ LoopPair c j s t) H count).mono
    (fun _ _ hp => ⟨hcount, hcount', hp⟩) (fun _ _ h => h)

def prepareRoot (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.Arm.tonelliPowers c) (.block (Impl.EcKey.Compressed.Arm.tonelliSetup c))

structure RootInput (c : Cfg) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  mod : ModOkW c.MP' size c.C.p s.mem base
  rhs : sv c base s Impl.Ecdh.Arm.W2 < c.C.p
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p

def RootPair (c : Cfg) (s t : State) : Prop :=
  ∃ base, RootInput c base s ∧ RootInput c base t ∧ RootPublic s t

theorem prepareRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} (I : RootInput c base s) :
    WP isa (prepareRoot c) s fun t => LoopState c base 95 t ∧ Rest powClob s t := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  refine WP.seq (WP.mono (tonelliPowers_ok hc I.scr I.far I.mod I.rhs I.one)
    fun s₁ ⟨K₁, U₁, lt₁, ltr₁, _, _⟩ => ?_)
  have hs₁ := I.scr.of_rest K₁ (by decide)
  refine WP.mono (tonelliSetup_ok hc hs₁ ltr₁ lt₁) fun s₂ ⟨K₂, U₂, lt₂, counter₂, _, _, _⟩ => ?_
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
  have K := K₁.trans (K₂.mono (by decide))
  refine ⟨⟨hs₁.of_rest K₂ (by decide), I.far.of_rest K, modP_of hc ?_, ?_, lt₂, counter₂⟩, K⟩
  · rw [sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact I.mod.val
  · rw [sv, sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact I.one

theorem rootCandidate_rel {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3)
    (hprepare : ConstantTime isa (fun _ => True) RootPublic (prepareRoot c))
    (hprefix : ConstantTime isa (fun _ => True) RootPublic (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) PowerPublic (Impl.EcKey.Compressed.Arm.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) RootPublic (descentRest c)) :
    RelCT isa (RootPair c) (Impl.EcKey.Compressed.Arm.rootCandidate c) RootPublic := by
  have H := ((rel_of_ct hprepare).mono (P' := RootPair c)
    (fun _ _ ⟨_, _, _, hp⟩ => hp) (fun _ _ _ => trivial)).wpDep
    (F := fun (s t : State) => ∃ base, RootInput c base s ∧ LoopState c base 95 t ∧ Rest powClob s t)
    (by
      rintro s t ⟨base, I, J, _⟩
      exact ⟨WP.mono (prepareRoot_ok hc I) (fun _ ⟨L, K⟩ => ⟨base, I, L, K⟩),
        WP.mono (prepareRoot_ok hc J) (fun _ ⟨L, K⟩ => ⟨base, J, L, K⟩)⟩)
  simp only [Impl.EcKey.Compressed.Arm.rootCandidate, hp, ↓reduceIte]
  apply RelCT.assoc
  apply RelCT.seq H
  apply (descentLoop_rel hc (by decide : 1 ≤ 95) (by decide : 95 < 2 ^ 31) hprefix hsquare hrest).mono
  · rintro _ _ ⟨_, s, t, ⟨base, I, J, hp⟩, ⟨b₁, I₁, L, K⟩, ⟨b₂, I₂, R, N⟩⟩
    have h₁ : b₁ = base := by rw [← I₁.scr.wb, I.scr.wb]
    have h₂ : b₂ = base := by rw [← I₂.scr.wb, J.scr.wb]
    subst b₁; subst b₂
    exact ⟨base, L, R, hp.keep K N⟩
  · exact fun _ _ h => h

def conversionFront (c : Cfg) : Prog isa :=
  .seq (.seq (.block (c.setupWith Impl.EcKey.Compressed.Arm.args))
    (.block (Impl.EcKey.Compressed.Arm.decompressPeer c)))
    (fprog c.SP (Impl.EcKey.Compressed.Arm.rhsOps c) c.umaal)

def conversionSuffix (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.Arm.selectRoot c)
    (.seq (Impl.EcKey.Compressed.Arm.checkRoot c) (.block (Impl.EcKey.Compressed.Arm.decompressFinish c)))

theorem conversionFront_ok {c : Cfg} (hc : CfgOk c) {s : State}
    (hp : InputPre c (1 + c.C.len) s) :
    WP isa (conversionFront c) s (DecompressFront c s) := by
  have h := decompressFront_ok hc hp (rest := .block []) (fun _ F => WP.block_nil F)
  simpa only [conversionFront, WP.seq_iff (M := isa), WP.block_nil_iff (M := isa)] using h

theorem rel_assoc_left {a b c : Prog isa} {P Q : State → State → Prop}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s t ts tt u v hp es et
  cases es with
  | seq ab c₁ =>
    cases ab with
    | seq a₁ b₁ =>
      cases et with
      | seq ab c₂ =>
        cases ab with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          exact ⟨by simpa only [List.append_assoc] using ht, hq⟩

theorem decompress_tonelli_ct {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3)
    {root : Spec.Weierstrass.Fe c.C → Spec.Weierstrass.Fe c.C}
    (hfront : ConstantTime isa (fun _ => True) (decompressContract c.C root).pub (conversionFront c))
    (hprepare : ConstantTime isa (fun _ => True) RootPublic (prepareRoot c))
    (hprefix : ConstantTime isa (fun _ => True) RootPublic (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) PowerPublic (Impl.EcKey.Compressed.Arm.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) RootPublic (descentRest c))
    (hsuffix : ConstantTime isa (fun _ => True) RootPublic (conversionSuffix c)) :
    ConstantTime isa (decompressContract c.C root).pre (decompressContract c.C root).pub
      (Impl.EcKey.Compressed.Arm.decompress c) := by
  let P := fun s t => (decompressContract c.C root).pre s ∧
    (decompressContract c.C root).pre t ∧ (decompressContract c.C root).pub s t
  have Hfront := ((rel_of_ct hfront).mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ _ => trivial)).wpDep
    (F := fun s t => DecompressFront c s t)
    (by
      rintro s t ⟨hs, ht, _⟩
      have pre {u : State} (h : (decompressContract c.C root).pre u) : InputPre c (1 + c.C.len) u := by
        obtain ⟨hrd, hwr, _, hd, _, _, hpk, hws⟩ := h
        exact ⟨by rw [hrd]; simp [Nat.add_comm], by rw [hwr]; simp,
          by simpa only [Nat.add_comm] using hd, by omega_using [hpk], hws⟩
      exact ⟨conversionFront_ok hc (pre hs), conversionFront_ok hc (pre ht)⟩)
  have Hroot := rootCandidate_rel hc hp hprepare hprefix hsquare hrest
  have Hfront' : RelCT isa P (conversionFront c) (RootPair c) := Hfront.mono
    (fun _ _ h => h) (by
      rintro u v ⟨_, s, t, ⟨_, _, hp⟩, F, G⟩
      rcases hp with ⟨_, ho, _, hb⟩
      have I : RootInput c (ptr s .r2) u := ⟨F.scr, F.far, modP_of hc F.fixed.mp, F.rhs_lt, F.fixed.onep⟩
      have J : RootInput c (ptr s .r2) v := by
        rw [show ptr s .r2 = ptr t .r2 from congrArg State.addr hb]
        exact ⟨G.scr, G.far, modP_of hc G.fixed.mp, G.rhs_lt, G.fixed.onep⟩
      refine ⟨ptr s .r2, I, J, ?_, ?_⟩
      · apply BitVec.eq_of_toNat_eq
        rw [I.scr.wb_toNat, J.scr.wb_toNat]
      · rw [F.out, G.out, ho])
  have Hsuffix := rel_of_ct hsuffix
  have Hrecovery : RelCT isa (RootPair c)
      (.seq (Impl.EcKey.Compressed.Arm.recoverCoordinate c)
        (.block (Impl.EcKey.Compressed.Arm.decompressFinish c))) (fun _ _ => True) := by
    apply rel_assoc_left
    apply RelCT.seq Hroot
    exact rel_assoc_left Hsuffix
  apply RelCT.constantTime
  exact RelCT.assoc (RelCT.assoc (RelCT.seq Hfront' Hrecovery))

end VG.Proof.EcKey.Compressed.Arm

end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm.P224Decompress

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.P224

abbrev code : Prog isa := Impl.EcKey.Compressed.Arm.decompress p224

materialize_shared baseline := code

/-- The function with `umaal`. -/
abbrev codeU : Prog isa := Impl.EcKey.Compressed.Arm.decompress (p224With true)

materialize_shared umaal := codeU

abbrev root (a : Spec.Weierstrass.Fe Spec.P224.curve) :=
  Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)

/-! The functions modulo `p` as literals, for their summaries (the kernel would otherwise build
their instructions once for the analysis and once for the frame). -/
materialize_code mulModP := Impl.Weierstrass.Arm.Mont.mulFnWith false p224.SP.k p224.SP.m
materialize_code addModP := Impl.Weierstrass.Arm.Mont.addFnWith false p224.SP.k p224.SP.m
materialize_code subModP := Impl.Weierstrass.Arm.Mont.subFnWith false p224.SP.k p224.SP.m

/-! The constant-time analyses of the calls of the functions modulo `p`, from their arguments,
each done once for the six checks of `ct` (`taint_decide_sum`), which would each analyse the
functions' code again. They keep what is public of `r10` (which the callers keep `lr` in) and of
the loops' counter `r11`: the functions write neither. The analysis is `taintS`'s, which has
summaries (`Proof/Framework/Arm/TaintMono.lean`); `ctU`'s is `taintU`'s, which has none. -/
taint_summary mulPSum : taintS (Taint.ofRegs [.r0, .r1, .r2, .r3])
  (.call (Impl.Weierstrass.Arm.Mont.mulName false p224.SP)
    (Impl.Weierstrass.Arm.Mont.mulFnWith false p224.SP.k p224.SP.m))
  keeping (Taint.ofRegs [.r10, .r11])
taint_summary addPSum : taintS (Taint.ofRegs [.r0, .r1, .r2, .r3])
  (.call (Impl.Weierstrass.Arm.Mont.addName false p224.SP)
    (Impl.Weierstrass.Arm.Mont.addFnWith false p224.SP.k p224.SP.m))
  keeping (Taint.ofRegs [.r10, .r11])
taint_summary subPSum : taintS (Taint.ofRegs [.r0, .r1, .r2, .r3])
  (.call (Impl.Weierstrass.Arm.Mont.subName false p224.SP)
    (Impl.Weierstrass.Arm.Mont.subFnWith false p224.SP.k p224.SP.m))
  keeping (Taint.ofRegs [.r10, .r11])

theorem ct : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub code := by
  apply decompress_tonelli_ct p224_ok (by decide +kernel)
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r0, .r1, .r2])
    · intro s t _ _ ⟨_, h0, h1, h2⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr, .r11])
    · intro s t _ _ ⟨⟨hb, ho⟩, hc⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hb
      · exact ho
      · exact hc
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide_sum [mulPSum, addPSum, subPSum]
  · apply VG.Taint.constantTime_of_exists (A := taintS) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide_sum [mulPSum, addPSum, subPSum]

theorem ctU : ConstantTime isa (decompressContract Spec.P224.curve root).pre
    (decompressContract Spec.P224.curve root).pub codeU := by
  apply decompress_tonelli_ct p224u_ok (by decide +kernel)
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r0, .r1, .r2])
    · intro s t _ _ ⟨_, h0, h1, h2⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr, .r11])
    · intro s t _ _ ⟨⟨hb, ho⟩, hc⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hb
      · exact ho
      · exact hc
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide
  · apply VG.Taint.constantTime (A := taintU) (Taint.ofRegs [.r12, .lr])
    · intro s t _ _ ⟨hb, ho⟩
      apply Taint.agree_ofRegs
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hb
      · exact ho
    · taint_decide

theorem sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0).pre s := by
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argRegs, reduceClassify, Loc.val, State.addr, decompressSatState] [decompressSatState] using (decompressSatState 28)

theorem verified (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    Verified target code (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct p224 p224_ok _ (candidateTonelli_correct p224_ok (by decide +kernel) (by decide +kernel))) ct
    (decompress_implies Spec.EcKey.P224.inst _
      (Proof.P224.rootFacts hL) sat)

theorem verifiedU (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    Verified target codeU (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) :=
  Verified.of_correct (decompress_correct (p224With true) p224u_ok _
      (candidateTonelli_correct p224u_ok (by decide +kernel) (by decide +kernel))) ctU
    (decompress_implies Spec.EcKey.P224.inst _
      (Proof.P224.rootFacts hL) sat)

end VG.Proof.EcKey.Compressed.Arm.P224Decompress
