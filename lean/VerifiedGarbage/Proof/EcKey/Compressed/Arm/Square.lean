module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Counter
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Weierstrass.RootPowers
import VerifiedGarbage.Proof.Weierstrass.Arm.Pow
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
public import VerifiedGarbage.Impl.Ecdsa.Arm
public import VerifiedGarbage.Proof.Mont.Arm.Words
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch

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
  refine wp_testCounter (j := j - 1) (by omega) (by rw [u₂.gpr]) fun s₃ f₃ hz₃ => WP.block_nil ?_
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
  refine WP.seq (WP.mono (testCounter_ok s (by omega) hb) fun s₁ ⟨hz₁, k₁, m₁⟩ => ?_)
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
      (by rw [k₁.gpr _ (by decide), hb]) hcount (by omega)) fun t ⟨kt, Ut, lt, vt⟩ => ?_
    refine ⟨(k₁.mono (by simp)).trans kt, ?_, lt, ?_⟩
    · rw [← m₁]
      exact Ut
    · simpa only [sv, m₁] using vt

end VG.Proof.EcKey.Compressed.Arm
