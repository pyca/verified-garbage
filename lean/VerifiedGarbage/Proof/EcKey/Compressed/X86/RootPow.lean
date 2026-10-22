module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
public import VerifiedGarbage.Proof.Weierstrass.X86.Pow
public import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Weierstrass.X86.Bits

/-! # The root exponentiation's workspace layout -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86


open VG.Impl.Ecdsa.X86 VG.Impl.Ecdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86

/-- The square-root power uses the same accumulator and temporary as the
existing powers, and a table separate from Montgomery's temporary area. -/
theorem rootPow_lay {c : Cfg} (hc : CfgOk c) {j : Nat} (hj : j < 3)
    : PowLay (Impl.EcKey.Compressed.X86.rootPow c j) size :=
  powLay_of hc (jm := MP) (by decide) _ hj (base := W2) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide)

theorem rootPow_wk {c : Cfg} (hc : CfgOk c) {j : Nat} (hj : j < 3) :
    PowWk (Impl.EcKey.Compressed.X86.rootPow c j) c.SP c.C.p size c.wk :=
  powWk_of hc hc.fp (jm := MP) (by decide) _ hj (base := W2) (by decide)

/-- The precise writes of one root exponentiation. -/
abbrev rootPowerWrites (c : Cfg) (j : Nat) : List (Nat × Nat) :=
  [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    powWx (Impl.EcKey.Compressed.X86.rootPow c j) c.wk

theorem rootPower_fixed {c : Cfg} (hc : CfgOk c) (j : Nat) : FixedOk c (rootPowerWrites c j) := by
  change FixedOk c ([(c.sl EXPP, 8 * c.n)] ++ [(bitsAt c.n j, 64 * c.n)] ++
    (slW c [ACC, PT, TMP] ++ wkW c))
  exact ((fixedOk_slW (l := [EXPP]) (by decide)).append (fixedOk_tbl j)).append
    ((fixedOk_slW (l := [ACC, PT, TMP]) (by decide)).append (fixedOk_wk))

theorem rootPower_apart {c : Cfg} (hc : CfgOk c) {i j : Nat} (hi : i < 45)
    (hw : i ∉ [EXPP, ACC, PT, TMP]) :
    ∀ w ∈ rootPowerWrites c j, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  change ∀ w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    (slW c [ACC, PT, TMP] ++ wkW c), _
  apply apart_append
  · intro w h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact sl_apart c (by intro h; exact hw (h ▸ (by simp)))
    · exact (apart_tbl hi j) _ (by simp)
  · exact apart_append (apart_slW (fun h => hw (List.mem_cons_of_mem _ h))) (apart_wk hi)

/-- Materializing an exponent and running the field power. -/
theorem rootPower_ok {c : Cfg} (hc : CfgOk c) {e j : Nat}
    (hj : j < 3) (he : e < 2 ^ (64 * c.n))
    {base : Addr} {s : State} (hs : Scr s base size)
    (_hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86.rootPower c e j) s fun s' =>
      Keeps powClob s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
        powWx (Impl.EcKey.Compressed.X86.rootPow c j) c.wk) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have h0 := hc.n0
  have hE := sl_le c h7 (i := EXPP) (by decide)
  rw [Impl.EcKey.Compressed.X86.rootPower]
  change WP isa (.seq (.block (setConst c.n (c.sl EXPP) e))
    (.seq (bits (c.sl EXPP) (bitsAt c.n j) (8 * c.n))
      (pow (Impl.EcKey.Compressed.X86.rootPow c j) c.SP))) s _
  refine WP.seq (WP.mono (setConst_ok hs hE he) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.seq (WP.mono (bits_ok hs₁ h0 hE (bitsAt_le c h7 hj)
    (Or.inl (sl_below_bits c (i := EXPP) (by decide) j 0)))
    fun s₂ ⟨bits₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have keep₂ {i : Nat} (hi : i < 45) (hiE : i ≠ EXPP) (hiT : i ≠ TMP) :
      sv c base s₂ i = sv c base s i := by
    have hsl := sl_le c h7 hi
    rw [sv, O₂.wordsVal (Or.inl (sl_below_bits c hi j 0)) (by omega),
      O₁.wordsVal (sl_apart c hiE) (by omega)]
  have B₂ : wordsVal s₂.mem base (c.sl W2) c.n < c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl W2) c.n = sv c base s₂ W2 from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hB
  have O₂' : wordsVal s₂.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p := by
    rw [show wordsVal s₂.mem base (c.sl ONEP) c.n = sv c base s₂ ONEP from rfl,
      keep₂ (by decide) (by decide) (by decide)]
    exact hO
  refine WP.mono (pow_ok (rootPow_lay hc hj) (rootPow_wk hc hj)
    (unitMod_pow_two hc.p_odd (64 * c.n)) hs₂ B₂ O₂'
    (by simpa only [e₁, Impl.EcKey.Compressed.X86.rootPow] using bits₂) he) fun s₃ ⟨k₃, U₃, lt₃, v₃⟩ => ?_
  refine ⟨?_, (O₁.unch.trans O₂.unch).trans U₃, lt₃, ?_⟩
  · exact ((k₁.mono (by simp [powClob, clob])).trans (k₂.mono (by simp [powClob, clob]))).trans k₃
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ W2) ^ e at v₃
    rw [keep₂ (by decide) (by decide) (by decide)] at v₃
    exact v₃

/-- The three-mod-four candidate uses an exponent derived from the prime. -/
theorem rootThree_ok {c : Cfg} (hc : CfgOk c) (hp : c.C.p % 4 = 3)
    {base : Addr} {s : State} (hs : Scr s base size)
    (_hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86.rootCandidate c) s fun s' =>
      Keeps powClob s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n 2, 64 * c.n)] ++
        powWx (Impl.EcKey.Compressed.X86.rootPow c 2) c.wk) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((c.C.p + 1) / 4) := by
  simp only [Impl.EcKey.Compressed.X86.rootCandidate, hp, ↓reduceIte]
  exact rootPower_ok hc (by decide)
    (by have := hc.p_lt; have := hc.p_ge; omega) hs _hM hB hO

end VG.Proof.EcKey.Compressed.X86
