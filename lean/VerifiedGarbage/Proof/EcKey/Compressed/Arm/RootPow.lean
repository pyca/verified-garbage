module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
public import VerifiedGarbage.Proof.Weierstrass.Arm.Pow
public import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.Bits

/-! # The root exponentiation's workspace layout -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Ecdsa.Arm VG.Impl.Ecdh.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm

/-- The square-root power uses the same accumulator and temporary as the
existing powers, and a table separate from Montgomery's temporary area. -/
theorem rootPow_lay {c : Cfg} (hc : CfgOk c) {j : Nat} (hj : j < 3)
    : PowLay (Impl.EcKey.Compressed.Arm.rootPow c j) size 8192 :=
  powLay_of hc (jm := MP) (by decide) _ hj (base := W2) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide)

theorem rootPow_wk {c : Cfg} (hc : CfgOk c) {j : Nat} :
    PowWk (Impl.EcKey.Compressed.Arm.rootPow c j) size c.wk :=
  powWk_of hc (jm := MP) (by decide) _ (base := W2) (by decide)

/-- The precise writes of one root exponentiation. -/
abbrev rootPowerWrites (c : Cfg) (j : Nat) : List (Nat × Nat) :=
  [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    powWx (Impl.EcKey.Compressed.Arm.rootPow c j) c.wk

theorem rootPower_fixed {c : Cfg} (hc : CfgOk c) (j : Nat) : FixedOk c (rootPowerWrites c j) := by
  change FixedOk c ([(c.sl EXPP, 8 * c.n)] ++ [(bitsAt c.n j, 64 * c.n)] ++
    (slW c [ACC, PT, TMP] ++ [(c.wk, 64 * c.n)]))
  exact ((fixedOk_slW (l := [EXPP]) (by decide)).append (fixedOk_tbl hc.n10 j)).append
    ((fixedOk_slW (l := [ACC, PT, TMP]) (by decide)).append (fixedOk_wk hc.n10))

theorem rootPower_apart {c : Cfg} (hc : CfgOk c) {i j : Nat} (hi : i < 45)
    (hw : i ∉ [EXPP, ACC, PT, TMP]) :
    ∀ w ∈ rootPowerWrites c j, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  change ∀ w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    (slW c [ACC, PT, TMP] ++ [(c.wk, 64 * c.n)]), _
  apply apart_append
  · intro w h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact sl_apart c (by intro h; exact hw (h ▸ (by simp)))
    · exact (apart_tbl hc.n10 hi j) _ (by simp)
  · exact apart_append (apart_slW (fun h => hw (List.mem_cons_of_mem _ h))) (apart_wk hc.n10 hi)

/-- Materializing an exponent and running the field power. -/
theorem rootPower_ok {c : Cfg} (hc : CfgOk c) {e j : Nat}
    (hj : j < 3) (he : e < 2 ^ (64 * c.n))
    {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.Arm.rootPower c e j) s fun s' =>
      Rest powClob s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
        powWx (Impl.EcKey.Compressed.Arm.rootPow c j) c.wk) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have h0 := hc.n0
  have hE := sl_le c h7 (i := EXPP) (by decide)
  rw [Impl.EcKey.Compressed.Arm.rootPower]
  change WP isa (.seq (.block (setConst c.n (c.sl EXPP) e))
    (.seq (bits (c.sl EXPP) (bitsAt c.n j) (8 * c.n))
      (pow (Impl.EcKey.Compressed.Arm.rootPow c j) c.SP))) s _
  refine WP.seq (WP.mono (setConst_ok hs hE he) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_rest k₁ (by decide)
  refine WP.seq (WP.mono (bits_ok hs₁ (hf.of_rest k₁) h0 hE (bitsAt_le c h7 hj)
    (bitsAt_lt hc hj) (by simp [bitsAt, Nat.add_mod, Nat.mul_mod])
    (Or.inl (sl_below_bits c h7 (i := EXPP) (by decide) j 0)) (enc8n h7))
    fun s₂ ⟨bits₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have keep₂ {i : Nat} (hi : i < 45) (hiE : i ≠ EXPP) (hiT : i ≠ TMP) :
      sv c base s₂ i = sv c base s i := by
    have hsl := sl_le c h7 hi
    rw [sv, O₂.wordsVal (Or.inl (sl_below_bits c h7 hi j 0)) (by omega),
      O₁.wordsVal (sl_apart c hiE) (by omega)]
  have hM₂ : ModOkW c.MP' size c.C.p s₂.mem base := modP_of hc (by
    change sv c base s₂ MP = c.C.p
    rw [keep₂ (by decide) (by decide) (by decide)]
    exact hM.val)
  have B₂ : wordsVal s₂.mem base (c.sl W2) c.n < c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl W2) c.n = sv c base s₂ W2 from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hB
  have O₂' : wordsVal s₂.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl ONEP) c.n = sv c base s₂ ONEP from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hO
  have henc : encodable (BitVec.ofNat 32 (64 * c.n)) = true := by
    have h : ∀ n < 10, encodable (BitVec.ofNat 32 (64 * n)) = true := by decide
    exact h _ h7
  refine WP.mono (pow_ok (rootPow_lay hc hj) (rootPow_wk hc) hc.fp
    (unitMod_pow_two hc.p_odd (64 * c.n)) (bitsAt_lt hc hj) hs₂ ((hf.of_rest k₁).of_rest k₂) hM₂ B₂ O₂'
    (by simpa only [e₁, Impl.EcKey.Compressed.Arm.rootPow] using bits₂) he henc) fun s₃ ⟨k₃, U₃, lt₃, v₃⟩ => ?_
  refine ⟨?_, (O₁.unch.trans O₂.unch).trans U₃, lt₃, ?_⟩
  · exact ((k₁.mono (by simp [powClob, clob])).trans (k₂.mono (by simp [powClob, clob]))).trans k₃
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ W2) ^ e at v₃
    rw [keep₂ (by decide) (by decide) (by decide)] at v₃
    exact v₃

/-- The three-mod-four candidate uses an exponent derived from the prime. -/
theorem rootThree_ok {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 = 3)
    {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.Arm.rootCandidate c) s fun s' =>
      Rest powClob s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n 2, 64 * c.n)] ++
        powWx (Impl.EcKey.Compressed.Arm.rootPow c 2) c.wk) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((c.C.p + 1) / 4) := by
  simp only [Impl.EcKey.Compressed.Arm.rootCandidate, hp, ↓reduceIte]
  exact rootPower_ok hc (by decide)
    (by have := hc.p_lt; have := hc.p_ge; omega) hs hf hM hB hO

end VG.Proof.EcKey.Compressed.Arm
