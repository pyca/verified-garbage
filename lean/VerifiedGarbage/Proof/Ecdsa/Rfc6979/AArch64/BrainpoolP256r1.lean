module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP256r1Literals
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Tables
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Order.RelClasses
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.TableSat
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Order.RelClasses
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# Deterministic ECDSA on AArch64: brainpoolP256r1

brainpoolp256r1 as the proof's curve (`brainpoolp256r1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_brainpoolp256r1_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at brainpoolP256r1's sizes).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem coreK_brainpoolp256r1 : coreK Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg =
    Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.signAArch64 := by rfl

/-! ## The curve's blocks -/

theorem brainpoolp256r1_blk : RfcT (cfgC Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg false 0) := by rfcT_decide

/-- brainpoolp256r1, with the group law `hL`, the inversions' soundness `hI`. -/
def brainpoolp256r1 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg
  inst := Spec.Ecdsa.BrainpoolP256r1.inst
  curve := rfl
  big := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.AArch64.BrainpoolP256r1.brainpoolp256r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.BrainpoolP256r1.brainpoolp256r1_sh
  coreN := "vg_ecdsa_brainpoolp256r1_sign_k"
  coreC := Impl.Ecdsa.AArch64.BrainpoolP256r1.signComb
  coreX := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.sign_a64 hL hI
  coreCT := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  blk := brainpoolp256r1_blk

/-- `vg_ecdsa_brainpoolp256r1_sign`, with the tables of `vs`. -/
theorem brainpoolp256r1T_verified (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds) (vs : List Proof.Pbkdf2.Md.AArch64.MdHash)
    (h : OK vs ∧ "VG_BRAINPOOLP256R1_COMB7" ∉ Proof.HmacTable.AArch64.names vs) :
    Verified AArch64.target (signCodeT (brainpoolp256r1 hL hI) Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1 Impl.Ecdsa.AArch64.BrainpoolP256r1.combCfg.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.brainpoolp256r1) h.1 Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.satMem h.2
    (by rw [Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.combCfg_combWords_length]; decide) Proof.Ecdsa.AArch64.BrainpoolP256r1.Comb.satMem_held (by decide) rfl
  exact signT_verified ⟨rfl, by decide, by decide⟩ rfl rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.AArch64
