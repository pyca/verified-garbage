module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Tables
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Lit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Tables
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Lit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# Deterministic ECDSA on AArch64: P-521

P-521 as the proof's curve (`p521`): scalars of 9 words and 66 bytes, longer
than any hash function's output (`wide`), the order `n` of 521 bits, so that
the signature drops 7 bits of a 66-byte digest, and `vg_ecdsa_p521_sign`,
proven correct (given the group law, the inversions' soundness and the comb's
tables) and constant time against its contract (`coreK` at P-521's sizes,
which is `Proof.Ecdsa.AArch64.P521.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

/-! ## The blocks for each hash function's sizes -/

theorem p521_blk₀ : RfcT (cfgS Impl.Ecdsa.AArch64.p521 false 7 16 64) := by rfcT_decide
theorem p521_blk₁ : RfcT (cfgS Impl.Ecdsa.AArch64.p521 false 7 20 64) := by rfcT_decide
theorem p521_blk₂ : RfcT (cfgS Impl.Ecdsa.AArch64.p521 false 7 28 64) := by rfcT_decide
theorem p521_blk₃ : RfcT (cfgS Impl.Ecdsa.AArch64.p521 false 7 32 64) := by rfcT_decide
theorem p521_blk₄ : RfcT (cfgS Impl.Ecdsa.AArch64.p521 false 7 48 128) := by rfcT_decide
theorem p521_blk₅ : RfcT (cfgS Impl.Ecdsa.AArch64.p521 false 7 64 128) := by rfcT_decide
theorem p521_blk₆ : RfcT (cfgS Impl.Ecdsa.AArch64.p521 false 7 28 128) := by rfcT_decide
theorem p521_blk₇ : RfcT (cfgS Impl.Ecdsa.AArch64.p521 false 7 32 128) := by rfcT_decide

/-- P-521, with the group law `hL`, the inversions' soundness `hI` and the comb's tables `hT`. -/
def p521 (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start) : RfcCurve where
  E := Impl.Ecdsa.AArch64.p521
  inst := Spec.Ecdsa.P521.inst
  curve := rfl
  wide := true
  sizes := ⟨rfl, rfl, Proof.Ecdsa.AArch64.P521.p521_nBits⟩
  n_lt := by decide +kernel
  sh := 7
  sh_eq := Proof.Ecdsa.AArch64.P521.p521_sh
  coreN := "vg_ecdsa_p521_sign_k"
  coreC := Impl.Ecdsa.AArch64.signP521
  coreX := Proof.Ecdsa.AArch64.P521.sign_a64 hL hI hT
  coreCT := Proof.Ecdsa.AArch64.P521.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := nofun
  blkT := blkT_of p521_blk₀ p521_blk₁ p521_blk₂ p521_blk₃ p521_blk₄ p521_blk₅ p521_blk₆ p521_blk₇


theorem p521_tbl : Impl.Ecdsa.AArch64.p521.tbl.isEmpty = false := rfl

/-- `vg_ecdsa_p521_sign`, with the tables of `vs`. -/
theorem p521T_verified (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ Impl.Ecdsa.AArch64.p521.tsym ∉ Proof.HashTable.AArch64.names vs) :
    Verified AArch64.target (signCode (p521 hL hI hT) Spec.Ecdsa.Rfc6979.Curves.p521.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p521 Impl.Ecdsa.AArch64.p521.combConsts vs) := by
  have e : constsOf Impl.Ecdsa.AArch64.p521 = Impl.Ecdsa.AArch64.p521.combConsts := by
    simp only [constsOf, p521_tbl, Bool.false_eq_true, ite_false]
  have hsat : ∃ s, (specK Spec.Ecdsa.Rfc6979.Curves.p521 (constsOf Impl.Ecdsa.AArch64.p521) vs).pre s := by
    rw [e]
    exact sat_one h.1 Proof.Ecdsa.AArch64.P521.satMem h.2 (by rw [Proof.Ecdsa.AArch64.P521.p521_combWords_length]; decide)
      Proof.Ecdsa.AArch64.P521.satMem_held (by decide) rfl
  rw [← e]
  exact signT_verified (R := p521 hL hI hT) ⟨rfl, by decide, by decide⟩ (.inl p521_tbl) rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.AArch64
