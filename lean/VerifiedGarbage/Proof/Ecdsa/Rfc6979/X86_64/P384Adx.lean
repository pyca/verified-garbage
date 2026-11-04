module

import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitEraseAdx
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# Deterministic ECDSA on x86-64: P-384 with BMI2 and ADX

As `P384.lean`, with `vg_ecdsa_p384_sign_adx` (`p384x`, P-384 multiplying
with BMI2 and ADX), proven correct and constant time against the same
contract; `p384Of` is either.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` is the same for `p384x` as for `p384`, the same curve. -/
theorem coreK_p384x : coreK Impl.Ecdsa.X86_64.p384x = Proof.Ecdsa.X86_64.P384.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P384.p384x_combConsts, Proof.Ecdsa.X86_64.P384.p384x_C,
    Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
  simp only [Abi.constsHeld, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true, Proof.Ecdsa.X86_64.P384.signX86_64, Proof.Ecdsa.X86_64.P384.TblHeld]
  rfl

/-- P-384 with BMI2 and ADX, with the group law `hL`, the comb's tables `hT`
and the inversions' soundness `hI`. -/
def p384x (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p384x
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  wide := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  hHigh := false
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.P384.p384x_sh
  coreN := "vg_ecdsa_p384_sign" ++ "_adx"
  coreC := Impl.Ecdsa.X86_64.signP384Adx
  coreX := by rw [coreK_p384x]; exact Proof.Ecdsa.X86_64.P384.sign_call_x86_adx hL hT hI
  coreCT := by rw [coreK_p384x]; exact Proof.Ecdsa.X86_64.P384.sign_ct_adx
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  reduceT := (p384 hL hT hI).reduceT
  blkT := blkT_of p384_blk₀ p384_blk₁ p384_blk₂ p384_blk₃ p384_blk₄ p384_blk₅ p384_blk₆ p384_blk₇

/-- P-384 with BMI2 and ADX (`adx`) or without. -/
def p384Of (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve :=
  bif adx then p384x hL hT hI else p384 hL hT hI


/-- `vg_ecdsa_p384_sign` (`_adx`, with BMI2 and ADX), with the tables of `vs`. -/
theorem p384T_verified (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs ∧ "VG_P384_COMB" ∉ Proof.HashTable.X86_64.names vs) :
    Verified X86_64.target (signCode (p384Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Ecdsa.X86_64.p384.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p384) h.1 Proof.Ecdsa.X86_64.P384.satMem h.2
    (by rw [Proof.Ecdsa.X86_64.P384.p384W_length]; decide) Proof.Ecdsa.X86_64.P384.satMem_held (by decide) rfl
  cases adx
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.X86_64
