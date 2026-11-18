module

import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressVerified
import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.P224.Sqrt
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.LitAlias
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.LitAlias
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.MulTaint
meta import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86
meta import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
meta import VerifiedGarbage.Impl.Ecdsa.P224.X86
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Impl.Ecdsa.P224.X86
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressContract
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressMain
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.CT
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.SlotOps
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Front
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Contract
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Weierstrass.X86.Loop
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Slots
public import VerifiedGarbage.Proof.Weierstrass.X86.Pow
public import VerifiedGarbage.Spec.EcKey.Compressed
public import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Impl.EcKey.Compressed.Root
import VerifiedGarbage.Proof.Weierstrass.RootTonelli
public import VerifiedGarbage.Proof.Ecdsa.X86.Main
public import VerifiedGarbage.Impl.Ecdh.X86
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdh.X86.Peer
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Impl.Ecdsa.X86
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Impl.Weierstrass.X86
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.SlotOps
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressContract
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.DecompressMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.EcKey.Compressed.X86.Front
meta import VerifiedGarbage.Proof.Framework.X86.Call
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Weierstrass.X86.Copy
meta import VerifiedGarbage.Proof.Mont.X86.Instr
meta import VerifiedGarbage.Proof.Framework.X86.Exec
meta import VerifiedGarbage.Proof.Weierstrass.X86.Loop
meta import VerifiedGarbage.Proof.Ecdsa.X86.Layout
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Slots
meta import VerifiedGarbage.Proof.Weierstrass.X86.Pow
meta import VerifiedGarbage.Spec.EcKey.Compressed
meta import VerifiedGarbage.Spec.EcKey.Generic
meta import VerifiedGarbage.Spec.Weierstrass
meta import VerifiedGarbage.TCB.X86.Isa
meta import VerifiedGarbage.Impl.EcKey.Compressed.Root
meta import VerifiedGarbage.Proof.Weierstrass.RootTonelli
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.Ecdsa.X86.Main
meta import VerifiedGarbage.Impl.Ecdh.X86
meta import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
meta import VerifiedGarbage.Proof.Ecdsa.X86.Middle
meta import VerifiedGarbage.Proof.Ecdh.X86.Peer
meta import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
meta import VerifiedGarbage.Proof.Ecdsa.X86.Lays
meta import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
meta import VerifiedGarbage.Proof.Mont.Words
meta import VerifiedGarbage.Proof.Weierstrass.Sqrt
meta import Mathlib.Algebra.Group.Nat.Defs
meta import VerifiedGarbage.Impl.Ecdsa.X86
meta import VerifiedGarbage.Proof.Mont.X86.Words
meta import VerifiedGarbage.Proof.Weierstrass.Env
meta import VerifiedGarbage.Proof.Weierstrass.Unch
meta import VerifiedGarbage.Impl.Weierstrass.X86
meta import VerifiedGarbage.Proof.Ecdsa.X86.Stages

/-! ### `EcKey.Compressed.X86.DecompressCT`, which only this module used -/

section

/-! ### `EcKey.Compressed.X86.RootCT`, which this module and modules that import it used -/

section

/-! ### `EcKey.Compressed.X86.Tonelli`, which this module and modules that import it used -/

section

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

end

end

/-! # Carry P-224's public counter through existing field calls

The field calls preserve the scratch counter, but their pointer-based
stores cause the syntactic taint analysis to forget it. RelCT combines the
existing taint checks with the already-proved counter invariants.
-/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.X86.Wp

def rootT (c : Cfg) : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .edi], flags := false,
    lens := [2 * c.C.len + 1, 8192], bases := [(.edi, 1, 0)], room := 28 }

def RootPublic (c : Cfg) (s t : State) : Prop :=
  VG.X86.Taint.Wf (rootT c) s ∧ VG.X86.Taint.Wf (rootT c) t ∧
  s.wr = t.wr ∧ s.gpr .edi = t.gpr .edi ∧ s.gpr .esp = t.gpr .esp

def PowerPublic (c : Cfg) (s t : State) : Prop := RootPublic c s t ∧ s.gpr .esi = t.gpr .esi

def descentPrefix (c : Cfg) : Prog isa :=
  .block (copy (2 * c.n) (c.sl T3) (c.sl T0) ++ [.mov .esi (.mem (sc (c.sl T2))), decCounter])

def descentKeeps (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.X86.descentChoose c)
    (.seq (fprog c.SP (Impl.EcKey.Compressed.X86.descentOps c))
      (.block (Impl.EcKey.Compressed.X86.descentCounter c)))

structure LoopState (c : Cfg) (base : Addr) (j : Nat) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p
  lt : ∀ i ∈ [ACC, T0, T1], sv c base s i < c.C.p
  counter : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j

def LoopPair (c : Cfg) (j : Nat) (s t : State) : Prop :=
  ∃ base, LoopState c base j s ∧ LoopState c base j t ∧ RootPublic c s t

theorem root_wf_keep {c : Cfg} {s t : State} (hw : VG.X86.Taint.Wf (rootT c) s)
    (K : Keeps powClob s t) : VG.X86.Taint.Wf (rootT c) t where
  lens h := by rw [K.2.2]; exact hw.lens h
  bases p hp := by
    simp only [rootT, List.mem_singleton] at hp
    subst p
    simpa only [K.1 .edi (by decide), VG.X86.Taint.region, K.2.2] using hw.bases (.edi, 1, 0) (by simp [rootT])
  wbases _ h := nomatch h
  args h := by cases h
  argBases _ h := nomatch h
  stk := by simpa only [rootT, VG.X86.Taint.depth, Nat.add_zero, K.1 .esp (by decide)] using hw.stk
  frames _ h := nomatch h
  room h := by
    simpa only [rootT, VG.X86.Taint.depth, VG.X86.Taint.nframes,
      Nat.add_zero, List.drop_zero, VG.X86.Taint.argByte, BitVec.add_zero,
      K.1 .esp (by decide), K.2.2] using hw.room h

theorem RootPublic.keep {c : Cfg} {s t u v : State} (hp : RootPublic c s t)
    (K : Keeps powClob s u) (L : Keeps powClob t v) : RootPublic c u v := by
  rcases hp with ⟨hs, ht, hw, hb, he⟩
  exact ⟨root_wf_keep hs K, root_wf_keep ht L, by rw [K.2.2, L.2.2, hw],
    by rw [K.1 _ (by decide), L.1 _ (by decide), hb],
    by rw [K.1 _ (by decide), L.1 _ (by decide), he]⟩

theorem rel_of_ct {c : Prog isa} {P : State → State → Prop}
    (h : ConstantTime isa (fun _ => True) P c) : RelCT isa P c (fun _ _ => True) :=
  fun _ _ _ _ _ _ hp e₁ e₂ => ⟨h _ _ _ _ _ _ trivial trivial hp e₁ e₂, trivial⟩

theorem descentPrefix_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {j : Nat} {s : State}
    (hs : Scr s base size) (hj : 1 ≤ j)
    (hw : s.mem.readW (off base (c.sl T2)) 32 = BitVec.ofNat 32 j) :
    WP isa (descentPrefix c) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (j - 1) ∧ Keeps powClob s t := by
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
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine wp_movS (show readSrc s₁ (.mem (sc (c.sl T2))) = some (s₁.mem.readW (off base (c.sl T2)) 32) by
    simp only [readSrc, State.load32, hs₁.ea (d := c.sl T2) (by omega_using [h0, h2]),
      hs₁.read (by omega_using [h0, h2] : c.sl T2 + 4 ≤ size), ite_true]) fun s₂ U₂ _ => ?_
  have hb₂ : s₂.gpr .esi = BitVec.ofNat 32 j := by
    rw [U₂.gpr, BitVec.eq_of_toNat_eq (O₁.w32
      (by have := sl_apart c (i := T2) (j := T3) (by decide); omega_using [h0, this])
      (by have := hs.nowrap; omega_using [h2, this])), hw]
  refine wp_decCounter hj hb₂ fun t hb₃ K₃ _ => WP.block_nil
    ⟨hb₃, (K₁.mono (by decide)).trans
      ((U₂.keeps.mono (by decide)).trans (K₃.mono (by decide)))⟩

theorem descentRound_rel {c : Cfg} (hc : CfgOk c) {j : Nat}
    (hj : 1 ≤ j) (hj' : j < 2 ^ 31)
    (hprefix : ConstantTime isa (fun _ => True) (RootPublic c) (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) (PowerPublic c) (Impl.EcKey.Compressed.X86.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) (RootPublic c) (descentKeeps c)) :
    RelCT isa (LoopPair c j) (Impl.EcKey.Compressed.X86.descentRound c) (fun _ _ => True) := by
  have Hprefix := ((rel_of_ct hprefix).mono (P' := LoopPair c j)
    (fun _ _ ⟨_, _, _, hp⟩ => hp) (fun _ _ _ => trivial)).wpDep
    (F := fun (s t : State) => t.gpr .esi = BitVec.ofNat 32 (j - 1) ∧ Keeps powClob s t)
    (fun s t ⟨base, I, J, _⟩ =>
      ⟨descentPrefix_ok hc I.scr hj I.counter, descentPrefix_ok hc J.scr hj J.counter⟩)
  have Hpower : RelCT isa (LoopPair c j) (Impl.EcKey.Compressed.X86.descentPower c) (fun _ _ => True) := by
    apply RelCT.seq Hprefix
    apply (rel_of_ct hsquare).mono
    · rintro _ _ ⟨_, s, t, ⟨_, _, _, hp⟩, ⟨hs, K⟩, ⟨ht, L⟩⟩
      exact ⟨hp.keep K L, hs.trans ht.symm⟩
    · exact fun _ _ _ => trivial
  have Hpower' := Hpower.wpDep
    (F := fun (s t : State) => Keeps powClob s t)
    (fun s t ⟨base, I, J, _⟩ => ⟨
      WP.mono (descentPower_ok hc I.scr I.mod (I.lt _ (by simp)) hj hj' I.counter)
        (fun _ h => h.1),
      WP.mono (descentPower_ok hc J.scr J.mod (J.lt _ (by simp)) hj hj' J.counter)
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
  refine ⟨R.scr, modP_of hc ?_, ?_, R.lt, R.counter⟩
  · rw [sv_unch R.unch h7 hn (by decide) (apart_slWk (by decide) (by decide : MP ∉ roundSlots))]
    exact I.mod.val
  · rw [sv, sv_unch R.unch h7 hn (by decide)
      (apart_slWk (by decide) (by decide : ONEP ∉ roundSlots))]
    exact I.one

theorem descentLoop_rel {c : Cfg} (hc : CfgOk c) {count : Nat}
    (hcount : 1 ≤ count) (hcount' : count < 2 ^ 31)
    (hprefix : ConstantTime isa (fun _ => True) (RootPublic c) (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) (PowerPublic c) (Impl.EcKey.Compressed.X86.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) (RootPublic c) (descentKeeps c)) :
    RelCT isa (LoopPair c count) (.loop (Impl.EcKey.Compressed.X86.descentRound c) .ne) (RootPublic c) := by
  have H : ∀ j, RelCT isa (fun s t => 1 ≤ j ∧ j < 2 ^ 31 ∧ LoopPair c j s t)
      (Impl.EcKey.Compressed.X86.descentRound c) fun u v =>
      isa.eval .ne u = isa.eval .ne v ∧ (isa.eval .ne u = some false → RootPublic c u v) ∧
      (isa.eval .ne u = some true → ∃ k < j, 1 ≤ k ∧ k < 2 ^ 31 ∧ LoopPair c k u v) := by
    intro j
    intro s t ts tt u v hp es et
    rcases hp with ⟨hj, hj', base, I, J, hpub⟩
    obtain ⟨ht, _⟩ := descentRound_rel hc hj hj' hprefix hsquare hrest s t ts tt u v
      ⟨base, I, J, hpub⟩ es et
    obtain ⟨_, u', eu, R⟩ := descentRound_ok hc I.scr I.mod I.lt I.one hj hj' I.counter
    obtain ⟨_, rfl⟩ := Exec.det es eu
    obtain ⟨_, v', ev, S⟩ := descentRound_ok hc J.scr J.mod J.lt J.one hj hj' J.counter
    obtain ⟨_, rfl⟩ := Exec.det et ev
    refine ⟨ht, ?_, fun _ => hpub.keep R.keep S.keep, ?_⟩
    · simp only [VG.X86.eval, R.zf, S.zf]
    · intro he
      have hn : j - 1 ≠ 0 := by
        intro hz
        simp only [VG.X86.eval, R.zf, decide_eq_true hz, Option.map_some, Bool.not_true] at he
        cases he
      exact ⟨j - 1, by omega_using [hj], by omega_using [hn], by omega_using [hj'], base, I.step hc R, J.step hc S,
        hpub.keep R.keep S.keep⟩
  exact (RelCT.loop (fun j s t => 1 ≤ j ∧ j < 2 ^ 31 ∧ LoopPair c j s t) H count).mono
    (fun _ _ hp => ⟨hcount, hcount', hp⟩) (fun _ _ h => h)

def prepareRoot (c : Cfg) : Prog isa :=
  .seq (Impl.EcKey.Compressed.X86.tonelliPowers c) (.block (Impl.EcKey.Compressed.X86.tonelliSetup c))

structure RootInput (c : Cfg) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkW c.MP' size c.C.p s.mem base
  rhs : sv c base s Impl.Ecdh.X86.W2 < c.C.p
  one : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p

def RootPair (c : Cfg) (s t : State) : Prop :=
  ∃ base, RootInput c base s ∧ RootInput c base t ∧ RootPublic c s t

theorem prepareRoot_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} (I : RootInput c base s) :
    WP isa (prepareRoot c) s fun t => LoopState c base 95 t ∧ Keeps powClob s t := by
  have h7 := hc.n10
  have hn := I.scr.nowrap
  refine WP.seq (WP.mono (tonelliPowers_ok hc I.scr I.mod I.rhs I.one)
    fun s₁ ⟨K₁, U₁, lt₁, ltr₁, _, _⟩ => ?_)
  have hs₁ := I.scr.of_keeps K₁ (by decide)
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
  refine ⟨⟨hs₁.of_keeps K₂ (by decide), modP_of hc ?_, ?_, lt₂, counter₂⟩, K⟩
  · rw [sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact I.mod.val
  · rw [sv, sv_unch U₁₂ h7 hn (by decide) (candidate_apart hc (by decide) (by decide))]
    exact I.one

theorem rootCandidate_rel {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 ≠ 3)
    (hprepare : ConstantTime isa (fun _ => True) (RootPublic c) (prepareRoot c))
    (hprefix : ConstantTime isa (fun _ => True) (RootPublic c) (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) (PowerPublic c) (Impl.EcKey.Compressed.X86.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) (RootPublic c) (descentKeeps c)) :
    RelCT isa (RootPair c) (Impl.EcKey.Compressed.X86.rootCandidate c) (RootPublic c) := by
  have H := ((rel_of_ct hprepare).mono (P' := RootPair c)
    (fun _ _ ⟨_, _, _, hp⟩ => hp) (fun _ _ _ => trivial)).wpDep
    (F := fun (s t : State) => ∃ base, RootInput c base s ∧ LoopState c base 95 t ∧ Keeps powClob s t)
    (by
      rintro s t ⟨base, I, J, _⟩
      exact ⟨WP.mono (prepareRoot_ok hc I) (fun _ ⟨L, K⟩ => ⟨base, I, L, K⟩),
        WP.mono (prepareRoot_ok hc J) (fun _ ⟨L, K⟩ => ⟨base, J, L, K⟩)⟩)
  simp only [Impl.EcKey.Compressed.X86.rootCandidate, hp, ↓reduceIte]
  apply RelCT.assoc
  apply RelCT.seq H
  apply (descentLoop_rel hc (by decide : 1 ≤ 95) (by decide : 95 < 2 ^ 31) hprefix hsquare hrest).mono
  · rintro _ _ ⟨_, s, t, ⟨base, I, J, hp⟩, ⟨b₁, I₁, L, K⟩, ⟨b₂, I₂, R, N⟩⟩
    have h₁ : b₁ = base := by rw [← I₁.scr.edi, I.scr.edi]
    have h₂ : b₂ = base := by rw [← I₂.scr.edi, J.scr.edi]
    subst b₁; subst b₂
    exact ⟨base, L, R, hp.keep K N⟩
  · exact fun _ _ h => h


end VG.Proof.EcKey.Compressed.X86

end

end

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/CodecFrame.lean`, which only this module imported.
section

section
namespace VG.Proof.EcKey.Compressed.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86

 theorem codec_args_frame {il ol : Nat} {s t : State} (hp : codecPre il ol false s)
    (he : t.gpr .esp = s.gpr .esp) (W : Frame (s.wr ++ [below (s.gpr .esp) 28]) s.mem t.mem) :
    ∀ i, i < 3 → arg t i = arg s i := by
  obtain ⟨_, hwr, _, _, _, hao, haw, _, _, _, _, _, hsf, hlo, _, _⟩ := hp
  intro i hi
  have hd : ∀ r ∈ s.wr ++ [below (s.gpr .esp) 28], Region.Disjoint ⟨argAddr s i, 4⟩ r := by
    intro r hr
    rw [hwr] at hr
    simp only [Bool.false_eq_true, ite_false, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hao.sub_left (arg_subN (k := 3) (by omega) hi)
    · exact haw.sub_left (arg_subN (k := 3) (by omega) hi)
    · exact ((below_disjoint_args (k := 12) hlo (by omega) (by decide)).sub_right
        (arg_subN (k := 3) (by omega) hi)).symm
  change t.mem.readW (argAddr t i) 32 = _
  rw [show argAddr t i = argAddr s i by simp only [argAddr, he]]
  exact W.readW (Region.contains_self _ _) hd (by decide)

 theorem codec_pre_frame {il ol : Nat} {s t : State} (hp : codecPre il ol false s)
    (he : t.gpr .esp = s.gpr .esp) (hr : t.rd = s.rd) (hw : t.wr = s.wr)
    (W : Frame (s.wr ++ [below (s.gpr .esp) 28]) s.mem t.mem) : codecPre il ol false t := by
  have ha := codec_args_frame hp he W
  simpa only [codecPre, ptr, argAddr, he, ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), hr, hw]
    using hp

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

 theorem root_agree {c : Cfg} {s t : State} (hp : RootPublic c s t) :
    VG.X86.Taint.Agree (rootT c) s t := by
  rcases hp with ⟨hs, ht, hw, hb, he⟩
  refine ⟨⟨?_, (fun h => nomatch h)⟩, (fun _ => hw), hs, ht,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty,
    (fun _ => he), (fun _ _ h => False.elim (Nat.not_lt_zero _ h))⟩
  intro r hr
  simp only [rootT, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact he
  · exact hb

 def powerT (c : Cfg) : VG.X86.Taint.T :=
  { rootT c with regs := .ofList [.esp, .edi, .esi] }

 theorem power_agree {c : Cfg} {s t : State} (hp : PowerPublic c s t) :
    VG.X86.Taint.Agree (powerT c) s t := by
  have R := root_agree hp.1
  refine ⟨⟨?_, R.rf.2⟩, R.wr,
    ⟨R.wf₁.lens, R.wf₁.bases, R.wf₁.wbases, R.wf₁.args, R.wf₁.argBases, R.wf₁.stk, R.wf₁.frames, R.wf₁.room⟩,
    ⟨R.wf₂.lens, R.wf₂.bases, R.wf₂.wbases, R.wf₂.args, R.wf₂.argBases, R.wf₂.stk, R.wf₂.frames, R.wf₂.room⟩, R.ok, R.slots, R.sp, R.argMem⟩
  intro r hr
  simp only [powerT, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.1.2.2.2.2
  · exact hp.1.2.2.2.1
  · exact hp.2

 theorem root_wf {c : Cfg} {s t : State}
    (hp : codecPre (c.C.len + 1) (2 * c.C.len + 1) false s)
    (hs : Scr t (ptr s 2) size) (he : t.gpr .esp = s.gpr .esp) (hw : t.wr = s.wr) :
    VG.X86.Taint.Wf (rootT c) t where
  lens h := by rw [hw]; exact (codec_wf hp).lens h
  bases p h := by
    simp only [rootT, List.mem_singleton] at h
    subst p
    simpa only [addr, BitVec.add_zero, VG.X86.Taint.region,
      hw, hp.2.1, ptr, Bool.false_eq_true, ite_false, List.getD_cons_succ, List.getD_cons_zero] using hs.edi
  wbases _ h := nomatch h
  args h := by cases h
  argBases _ h := nomatch h
  stk := by simpa only [rootT, codecT, VG.X86.Taint.depth, Nat.add_zero, he] using (codec_wf hp).stk
  frames _ h := nomatch h
  room h := by
    simpa only [rootT, codecT, VG.X86.Taint.depth, VG.X86.Taint.nframes,
      Nat.add_zero, List.drop_zero, VG.X86.Taint.argByte, BitVec.add_zero, he, hw] using (codec_wf hp).room h

 def finishT (c : Cfg) : VG.X86.Taint.T :=
  { codecT (2 * c.C.len + 1) with regs := .ofList [.esp, .edi], bases := [(.edi, 1, 0)] }

 theorem finish_agree {c : Cfg} {s t : State}
    (hs : codecPre (c.C.len + 1) (2 * c.C.len + 1) false s)
    (ht : codecPre (c.C.len + 1) (2 * c.C.len + 1) false t)
    (hp : RootPublic c s t)
    (ha : s.gpr .esp = t.gpr .esp ∧ arg s 0 = arg t 0 ∧ arg s 1 = arg t 1 ∧ arg s 2 = arg t 2) :
    VG.X86.Taint.Agree (finishT c) s t := by
  have A := codec_agree hs ht ha
  have R := root_agree hp
  exact ⟨R.rf, A.wr,
    ⟨A.wf₁.lens, R.wf₁.bases, A.wf₁.wbases, A.wf₁.args, A.wf₁.argBases,
      A.wf₁.stk, A.wf₁.frames, A.wf₁.room⟩,
    ⟨A.wf₂.lens, R.wf₂.bases, A.wf₂.wbases, A.wf₂.args, A.wf₂.argBases,
      A.wf₂.stk, A.wf₂.frames, A.wf₂.room⟩,
    A.ok, A.slots, A.sp, A.argMem⟩

 def conversionFront (c : Cfg) : Prog isa :=
  .seq (.seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
    (.block (Impl.EcKey.Compressed.X86.decompressPeer c)))
    (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c))

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
    (hroot : CandidateCorrect c root)
    (hsp : SpOk (Impl.EcKey.Compressed.X86.decompress c) 28)
    (hfront : ConstantTime isa (decompressContract c.C root).pre (decompressContract c.C root).pub (conversionFront c))
    (hprepare : ConstantTime isa (fun _ => True) (RootPublic c) (prepareRoot c))
    (hprefix : ConstantTime isa (fun _ => True) (RootPublic c) (descentPrefix c))
    (hsquare : ConstantTime isa (fun _ => True) (PowerPublic c) (Impl.EcKey.Compressed.X86.squarePower c))
    (hrest : ConstantTime isa (fun _ => True) (RootPublic c) (descentKeeps c))
    (hmiddle : ConstantTime isa (fun _ => True) (RootPublic c)
      (.seq (Impl.EcKey.Compressed.X86.selectRoot c) (Impl.EcKey.Compressed.X86.checkRoot c)))
    (hfinish : ConstantTime isa (decompressContract c.C root).pre
      (fun s t => RootPublic c s t ∧ (decompressContract c.C root).pub s t)
      (.block (Impl.EcKey.Compressed.X86.decompressFinish c))) :
    ConstantTime isa (decompressContract c.C root).pre (decompressContract c.C root).pub
      (Impl.EcKey.Compressed.X86.decompress c) := by
  let P := fun s t => (decompressContract c.C root).pre s ∧
    (decompressContract c.C root).pre t ∧ (decompressContract c.C root).pub s t
  have Hfront : RelCT isa P (conversionFront c) (RootPair c) := by
    have H : RelCT isa P (conversionFront c) (fun _ _ => True) :=
      fun _ _ _ _ _ _ ⟨hs, ht, hp⟩ es et => ⟨hfront _ _ _ _ _ _ hs ht hp es et, trivial⟩
    apply (H.wpDep (F := fun s t => DecompressFront c s t) (by
      rintro s t ⟨hs, ht, _⟩
      exact ⟨conversionFront_ok hc (by simpa only [Nat.add_comm] using codec_input (c := c) hs),
        conversionFront_ok hc (by simpa only [Nat.add_comm] using codec_input (c := c) ht)⟩)).mono
    · exact fun _ _ h => h
    · rintro u v ⟨_, s, t, ⟨hs, ht, hp⟩, F, G⟩
      have hb : ptr s 2 = ptr t 2 := congrArg (BitVec.setWidth 64) hp.2.2.2
      have J : RootInput c (ptr s 2) v := by
        rw [hb]; exact ⟨G.scr, modP_of hc G.fixed.mp, G.rhs_lt, G.fixed.onep⟩
      refine ⟨ptr s 2, ⟨F.scr, modP_of hc F.fixed.mp, F.rhs_lt, F.fixed.onep⟩, J,
        root_wf hs F.scr F.esp F.wr, root_wf ht G.scr G.esp G.wr, ?_, ?_, ?_⟩
      · simp only [F.wr, G.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2, Bool.false_eq_true, ite_false]
      · apply BitVec.eq_of_toNat_eq
        rw [F.scr.edi_toNat, J.scr.edi_toNat]
      · rw [F.esp, G.esp, hp.1]
  have Hbody : RelCT isa P (decompressBody c) (fun _ _ => True) :=
    RelCT.assoc (RelCT.assoc (RelCT.seq Hfront
      (RelCT.seq (rootCandidate_rel hc hp hprepare hprefix hsquare hrest) (rel_of_ct hmiddle))))
  have hbody : SpOk (decompressBody c) 28 :=
    hsp.left.seq (hsp.right.left.seq (hsp.right.right.left.seq hsp.right.right.right.left))
  have Hbody' := Hbody.wpDep (F := fun (s t : State) => DecompressChecked c root s t ∧
      Frame (s.wr ++ [below (s.gpr .esp) 28]) s.mem t.mem) (by
    rintro s t ⟨hs, ht, _⟩
    exact ⟨WP.spFrame hbody hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (decompressBody_ok hc hroot
        (by simpa only [Nat.add_comm] using codec_input (c := c) hs)),
      WP.spFrame hbody ht.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (decompressBody_ok hc hroot
        (by simpa only [Nat.add_comm] using codec_input (c := c) ht))⟩)
  apply RelCT.constantTime
  change RelCT isa P ([.block (c.setupWith Impl.EcKey.Compressed.X86.args),
    .block (Impl.EcKey.Compressed.X86.decompressPeer c),
    Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c)].foldr .seq
    (.seq (Impl.EcKey.Compressed.X86.recoverCoordinate c)
      (.block (Impl.EcKey.Compressed.X86.decompressFinish c)))) (fun _ _ => True)
  -- Regroup the same prefix used by the correctness proof.
  apply RelCT.assoc
  apply RelCT.assoc
  apply RelCT.assoc
  apply RelCT.seq (rel_assoc_left (rel_assoc_left Hbody'))
  intro u v tu tv u' v' ⟨_, s, t, ⟨hs, ht, hp⟩, ⟨F, W⟩, ⟨G, V⟩⟩ eu ev
  have hu := codec_pre_frame hs F.esp F.rd F.wr W
  have hv := codec_pre_frame ht G.esp G.rd G.wr V
  have as_ := codec_args_frame hs F.esp W
  have at_ := codec_args_frame ht G.esp V
  have ha : (decompressContract c.C root).pub u v := by
    refine ⟨by rw [F.esp, G.esp, hp.1], ?_, ?_, ?_⟩
    · rw [as_ 0 (by decide), at_ 0 (by decide), hp.2.1]
    · rw [as_ 1 (by decide), at_ 1 (by decide), hp.2.2.1]
    · rw [as_ 2 (by decide), at_ 2 (by decide), hp.2.2.2]
  have hb : ptr s 2 = ptr t 2 := congrArg (BitVec.setWidth 64) hp.2.2.2
  have RP : RootPublic c u v := by
    refine ⟨root_wf hs F.scr F.esp F.wr, root_wf ht G.scr G.esp G.wr, ?_, ?_, ha.1⟩
    · simp only [F.wr, G.wr, hs.2.1, ht.2.1, hp.2.1, hp.2.2.2, Bool.false_eq_true, ite_false]
    · apply BitVec.eq_of_toNat_eq
      rw [F.scr.edi_toNat, G.scr.edi_toNat, hb]
  exact ⟨hfinish _ _ _ _ _ _ hu hv ⟨RP, ha⟩ eu ev, trivial⟩

end VG.Proof.EcKey.Compressed.X86

end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86.P224Decompress

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86.P224

abbrev code : Prog isa := Impl.EcKey.Compressed.X86.decompress p224

materialize_aliases fns := code
materialize_shared baseline := code

theorem sp : SpOk code 28 := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

taint_summary mulSum : taint ({ codecMulT (2 * Spec.P224.curve.len + 1) with regs := .ofList [.esp, .edi, .esi], argLen := 0, argBases := [] })
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p224p.k Impl.Weierstrass.Mont.p224p.m)

taint_summary mulSumW : taint ({ codecMulT (2 * Spec.P224.curve.len + 1) with regs := .ofList [.esp, .edi], argLen := 0, argBases := [] })
  (Impl.Weierstrass.X86.Mont.mulFn Impl.Weierstrass.Mont.p224p.k Impl.Weierstrass.Mont.p224p.m)

theorem ct : ConstantTime isa (decompressContract Spec.P224.curve (fun a : Spec.Weierstrass.Fe Spec.P224.curve => Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11))).pre
    (decompressContract Spec.P224.curve (fun a : Spec.Weierstrass.Fe Spec.P224.curve => Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11))).pub code := by
  apply decompress_tonelli_ct p224_ok (by decide +kernel)
    (candidateTonelli_correct p224_ok (by decide +kernel) (by decide +kernel)) sp
  · apply VG.Taint.constantTime (A := taint) (codecT (2 * Spec.P224.curve.len + 1))
    · exact fun _ _ hs ht hp => codec_agree hs ht hp
    · taint_decide
  · obtain ⟨_, hc⟩ : ∃ h, (taint.check (rootT p224) (prepareRoot p224) h).isSome = true := by
      native_taint_decide_sum [mulSum]
    exact VG.Taint.constantTime (A := taint) (rootT p224) (fun _ _ _ _ hp => root_agree hp) hc
  · apply VG.Taint.constantTime (A := taint) (rootT p224)
    · exact fun _ _ _ _ hp => root_agree hp
    · taint_decide
  · obtain ⟨_, hc⟩ : ∃ h, (taint.check (powerT p224) (Impl.EcKey.Compressed.X86.squarePower p224) h).isSome = true := by
      native_taint_decide_sum [mulSum]
    exact VG.Taint.constantTime (A := taint) (powerT p224) (fun _ _ _ _ hp => power_agree hp) hc
  · obtain ⟨_, hc⟩ : ∃ h, (taint.check (rootT p224) (descentKeeps p224) h).isSome = true := by
      native_taint_decide_sum [mulSumW]
    exact VG.Taint.constantTime (A := taint) (rootT p224) (fun _ _ _ _ hp => root_agree hp) hc
  · obtain ⟨_, hc⟩ : ∃ h, (taint.check (rootT p224) (.seq (Impl.EcKey.Compressed.X86.selectRoot p224) (Impl.EcKey.Compressed.X86.checkRoot p224)) h).isSome = true := by
      native_taint_decide_sum [mulSumW]
    exact VG.Taint.constantTime (A := taint) (rootT p224) (fun _ _ _ _ hp => root_agree hp) hc
  · apply VG.Taint.constantTime (A := taint) (finishT p224)
    · exact fun _ _ hs ht hp => finish_agree hs ht hp.1 hp.2
    · taint_decide

theorem sat : ∃ s, (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 28).pre s := by
  have a0 : arg (satState 29 57) 0 = 0x1000 := by decide
  have a1 : arg (satState 29 57) 1 = 0x2000 := by decide
  have a2 : arg (satState 29 57) 2 = 0x8000 := by decide
  have ea : argAddr (satState 29 57) 0 = 0x20004 := by decide
  have esp : (satState 29 57).gpr .esp = 0x20000 := rfl
  have hlen : Spec.P224.curve.len = 28 := rfl
  sig_implies_sat [Spec.EcKey.P224.inst, Spec.EcKey.Instance.decompressPublicKeyContract,
    Spec.EcKey.Instance.decompressPublicKeySig, hlen, Spec.EcKey.scratchWords,
    abi, argSlots, argVal, argBytes, stackBelow, satState] [a0, a1, a2, ea, esp] using (satState 29 57)

theorem verified (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    Verified target code (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 28) :=
  decompress_verified (p224_ok) Spec.EcKey.P224.inst rfl (fun a : Spec.Weierstrass.Fe Spec.P224.curve => Impl.EcKey.Compressed.rootTonelli a ((Spec.P224.curve.p - 1) / 2 ^ 96) 96 (Fin.ofNat Spec.P224.curve.p 11)) (candidateTonelli_correct (p224_ok) (by decide +kernel) (by decide +kernel)) (Proof.P224.rootFacts hL) sp ct sat

end VG.Proof.EcKey.Compressed.X86.P224Decompress
