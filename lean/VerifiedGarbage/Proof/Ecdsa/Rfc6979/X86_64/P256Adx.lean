module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.LitAdx
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr

/-! ### `Ecdsa.Rfc6979.X86_64.P256`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86-64: P-256

P-256 as the proof's curve (`p256`): scalars of 4 words, the order `n` of
exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_p256_sign`, proven correct
(given the group law and the comb's tables) and constant time against its
contract (`coreK` at P-256's sizes, which is `Proof.Ecdsa.X86_64.signX86_64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem p256_nBits : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  show Spec.P256.curve.n.log2 + 1 = 256
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- `coreK` at P-256's sizes is `Proof.Ecdsa.X86_64.signX86_64` (by rewriting, as
deciding it would evaluate the tables' length). -/
theorem coreK_p256 : coreK Impl.Ecdsa.X86_64.p256 = Proof.Ecdsa.X86_64.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.p256_combConsts, Abi.constRegions_cons,
    Abi.constRegions_nil, Sig.forall_mem_const_single]
  simp only [Abi.constsHeld, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true, Proof.Ecdsa.X86_64.signX86_64, Proof.Ecdsa.X86_64.TblHeld]
  rfl

/-! ## The curve's blocks -/

theorem p256_blk : RfcT (cfgC Impl.Ecdsa.X86_64.p256 false 0) := by rfcT_decide


/-- P-256, with the group law `hL`, the comb's tables `hT` and the inversions'
soundness `hI`. -/
def p256 (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p256
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  big := false
  sizes := ⟨.inl rfl, .inl rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.p256_sh
  coreN := "vg_ecdsa_p256_sign_k"
  coreC := Impl.Ecdsa.X86_64.signP256
  coreX := by rw [coreK_p256]; exact Proof.Ecdsa.X86_64.sign_call_x86 hL hT hI
  coreCT := by rw [coreK_p256]; exact Proof.Ecdsa.X86_64.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  blk := p256_blk

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

/-!
# Deterministic ECDSA on x86-64: P-256 with BMI2 and ADX

As `P256.lean`, with `vg_ecdsa_p256_sign_adx` (`p256x`, P-256 multiplying
with BMI2 and ADX), proven correct and constant time against the same
contract; `p256Of` is either. `vg_ecdsa_p256_sign` with either, taking the
tables of `vs` for its hash function, is verified (`p256T_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

/-- `coreK` is the same for `p256x` as for `p256`, the same curve. -/
theorem coreK_p256x : coreK Impl.Ecdsa.X86_64.p256x = Proof.Ecdsa.X86_64.signX86_64 := coreK_p256

/-- P-256 with BMI2 and ADX, with the group law `hL`, the comb's tables `hT`
and the inversions' soundness `hI`. -/
def p256x (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p256x
  inst := Spec.Ecdsa.P256.inst
  curve := rfl
  big := false
  sizes := ⟨.inl rfl, .inl rfl, p256_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.p256_sh
  coreN := "vg_ecdsa_p256_sign_k" ++ "_adx"
  coreC := Impl.Ecdsa.X86_64.signP256Adx
  coreX := by rw [coreK_p256x]; exact Proof.Ecdsa.X86_64.sign_call_x86_adx hL hT hI
  coreCT := by rw [coreK_p256x]; exact Proof.Ecdsa.X86_64.sign_ct_adx
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  blk := by exact p256_blk

/-- P-256 with BMI2 and ADX (`adx`) or without. -/
def p256Of (adx : Bool) (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve :=
  bif adx then p256x hL hT hI else p256 hL hT hI


/-- `vg_ecdsa_p256_sign` (`_adx`, with BMI2 and ADX), with the tables of `vs`. -/
theorem p256T_verified (adx : Bool) (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash)
    (h : OK vs ∧ "VG_P256_COMB" ∉ Proof.HmacTable.X86_64.names vs) :
    Verified X86_64.target (signCodeT (p256Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p256.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p256 Impl.Ecdsa.X86_64.p256.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p256) h.1 Proof.Ecdsa.X86_64.satMem h.2
    (by rw [Proof.Ecdsa.X86_64.p256W_length]; decide) Proof.Ecdsa.X86_64.satMem_held (by decide) rfl
  cases adx
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat

end VG.Proof.Ecdsa.Rfc6979.X86_64
