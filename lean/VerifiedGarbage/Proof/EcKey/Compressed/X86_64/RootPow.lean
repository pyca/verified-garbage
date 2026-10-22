module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
import VerifiedGarbage.Proof.Weierstrass.X86_64.Pow
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bits

/-! # The root exponentiation's workspace layout -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64

/-- The square-root power uses the same accumulator and temporary as the
existing powers, and a table separate from Montgomery's temporary area. -/
theorem rootPow_lay {c : Cfg} (hc : BaseCfgOk c) {j : Nat} (hj : j < 3)
    (hsep : j ≠ 1 ∨ c.n ≠ 9) :
    PowLay (Impl.EcKey.Compressed.X86_64.rootPow c ACC j) size :=
  powLay_of hc (jm := MP) (by decide) _ hj (base := W2) (by decide) (by decide)
    (one := ONEP) (by decide) (by decide) ⟨by have := hc.n0; omega, Nat.le_refl _⟩ hsep

/-- The precise writes of one root exponentiation. -/
abbrev rootPowerWrites (c : Cfg) (j : Nat) : List (Nat × Nat) :=
  [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
    powW (Impl.EcKey.Compressed.X86_64.rootPow c ACC j)

theorem rootPower_fixed (c : Cfg) (j : Nat) : FixedOk c (rootPowerWrites c j) := by
  change FixedOk c ([(c.sl EXPP, 8 * c.n)] ++ [(bitsAt c.n j, 64 * c.n)] ++ slW c [ACC, PT, TMP])
  exact ((fixedOk_slW (l := [EXPP]) (by decide)).append (fixedOk_tbl j)).append
    (fixedOk_slW (l := [ACC, PT, TMP]) (by decide))

theorem rootPower_apart {c : Cfg} {i j : Nat} (hi : i < 45) (hw : i ∉ [EXPP, ACC, PT, TMP]) :
    ∀ w ∈ rootPowerWrites c j, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  change ∀ w ∈ [(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++ slW c [ACC, PT, TMP], _
  apply apart_append
  · intro w h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact sl_apart c (by intro h; exact hw (h ▸ (by simp)))
    · exact (apart_tbl hi j (.inl (by intro h; exact hw (h ▸ (by simp))))) _ (by simp)
  · exact apart_slW (fun h => hw (List.mem_cons_of_mem _ h))

/-- Materializing an exponent and running the field power. -/
theorem rootPower_ok {c : Cfg} (hc : BaseCfgOk c) {e j : Nat}
    (hj : j < 3) (hsep : j ≠ 1 ∨ c.n ≠ 9) (he : e < 2 ^ (64 * c.n))
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86_64.rootPower c e j).inline s fun s' =>
      KeepRegs (powClob c.n) s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n j, 64 * c.n)] ++
        powW (Impl.EcKey.Compressed.X86_64.rootPow c ACC j)) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ e := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have h0 := hc.n0
  have hE := sl_le c h7 (i := EXPP) (by decide)
  rw [Impl.EcKey.Compressed.X86_64.rootPower]
  change WP isa (.seq (.block (setConst c.n (c.sl EXPP) e))
    (.seq (bits (c.sl EXPP) (bitsAt c.n j) (8 * c.n))
      (pow (Impl.EcKey.Compressed.X86_64.rootPow c ACC j)))) s _
  refine WP.seq (WP.mono (setConst_ok hs hE he) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.seq (WP.mono (bits_ok hs₁ h0 (by omega) hE (bitsAt_le c h7 hj)
    (sl_apart_bits c (i := EXPP) (j := j) (by decide) (.inl (by decide)) (64 * c.n) (by omega)))
    fun s₂ ⟨bits₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have keep₂ {i : Nat} (hi : i < 45) (hiE : i ≠ EXPP) (hiT : i ≠ TMP) :
      sv c base s₂ i = sv c base s i := by
    have hsl := sl_le c h7 hi
    rw [sv, O₂.wordsVal (sl_apart_bits c hi (.inl hiT) (64 * c.n) (by omega)) (by omega),
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
  refine WP.mono (pow_ok (rootPow_lay hc (j := j) hj hsep)
    (unitMod_pow_two hc.p_odd (64 * c.n)) hs₂ hM₂ B₂ O₂'
    (by simpa only [e₁, Impl.EcKey.Compressed.X86_64.rootPow] using bits₂) he) fun s₃ ⟨k₃, U₃, lt₃, v₃⟩ => ?_
  refine ⟨?_, (O₁.unch.trans O₂.unch).trans U₃, lt₃, ?_⟩
  · exact ((k₁.mono (by simp [powClob, clob])).trans (k₂.mono (by simp [powClob, clob]))).trans k₃
  · change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₃ ACC) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ W2) ^ e at v₃
    rw [keep₂ (by decide) (by decide) (by decide)] at v₃
    exact v₃

/-- The three-mod-four candidate uses an exponent derived from the prime. -/
theorem rootThree_ok {c : Cfg} (hc : BaseCfgOk c) (hp : c.C.p % 4 = 3)
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : sv c base s W2 < c.C.p)
    (hO : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p) :
    WP isa (Impl.EcKey.Compressed.X86_64.rootCandidate c).inline s fun s' =>
      KeepRegs (powClob c.n) s s' ∧
      Unch base ([(c.sl EXPP, 8 * c.n), (bitsAt c.n 2, 64 * c.n)] ++
        powW (Impl.EcKey.Compressed.X86_64.rootPow c ACC 2)) s.mem s'.mem ∧
      sv c base s' ACC < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s W2) ^ ((c.C.p + 1) / 4) := by
  simp only [Impl.EcKey.Compressed.X86_64.rootCandidate, hp, ↓reduceIte]
  exact rootPower_ok hc (by decide) (.inl (by decide))
    (by have := hc.p_lt; have := hc.p_ge; omega) hs hM hB hO

end VG.Proof.EcKey.Compressed.X86_64
