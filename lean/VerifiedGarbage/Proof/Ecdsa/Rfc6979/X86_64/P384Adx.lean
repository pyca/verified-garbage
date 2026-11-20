module

import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Scrub
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitAdx
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.TableSat
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Curves
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.VerifiedAdx
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.LitEraseAdx
import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
public import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Framework.TaintMap
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Verified
meta import VerifiedGarbage.Proof.Ecdsa.X86_64.P384.Lit
meta import Mathlib.Data.Finset.Attr
meta import Mathlib.Tactic.SetLike
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintMap

/-! ### `Ecdsa.Rfc6979.X86_64.P384`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86-64: P-384

P-384 as the proof's curve (`p384`): scalars of 6 words, the order `n` of
exactly 384 bits with `2^384 < 2 n`, and `vg_ecdsa_p384_sign`, proven correct
(given the group law and the comb's tables) and constant time against its
contract (`coreK` at P-384's sizes, which is `Proof.Ecdsa.X86_64.P384.signX86_64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64

theorem p384_nBits : Spec.Ecdsa.nBits Spec.P384.curve = 384 := by
  show Spec.P384.curve.n.log2 + 1 = 384
  have h₁ : 383 ≤ Spec.P384.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P384.curve.n.log2 < 384 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega_using [h₁, h₂]

/-- `coreK` at P-384's sizes is `Proof.Ecdsa.X86_64.P384.signX86_64` (by rewriting, as
deciding it would evaluate the tables' length). -/
theorem coreK_p384 : coreK Impl.Ecdsa.X86_64.p384 = Proof.Ecdsa.X86_64.P384.signX86_64 := by
  simp only [coreK, TblsOk, Proof.Ecdsa.X86_64.P384.p384_combConsts, Abi.constRegions_cons,
    Abi.constRegions_nil, Sig.forall_mem_const_single]
  simp only [Abi.constsHeld, List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true, Proof.Ecdsa.X86_64.P384.signX86_64, Proof.Ecdsa.X86_64.P384.TblHeld]
  rfl

/-! ## The curve's blocks -/

theorem p384_blk : RfcT (cfgC Impl.Ecdsa.X86_64.p384 false 0) := by rfcT_decide


/-- P-384, with the group law `hL`, the comb's tables `hT` and the inversions'
soundness `hI`. -/
def p384 (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.X86_64.p384
  inst := Spec.Ecdsa.P384.inst
  curve := rfl
  big := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.P384.p384_sh
  coreN := "vg_ecdsa_p384_sign_k"
  coreC := Impl.Ecdsa.X86_64.signP384
  coreX := by rw [coreK_p384]; exact Proof.Ecdsa.X86_64.P384.sign_call_x86 hL hT hI
  coreCT := by rw [coreK_p384]; exact Proof.Ecdsa.X86_64.P384.sign_ct
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  blk := p384_blk

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

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
  big := false
  sizes := ⟨.inr (.inl rfl), .inl rfl, p384_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.X86_64.P384.p384x_sh
  coreN := "vg_ecdsa_p384_sign_k" ++ "_adx"
  coreC := Impl.Ecdsa.X86_64.signP384Adx
  coreX := by rw [coreK_p384x]; exact Proof.Ecdsa.X86_64.P384.sign_call_x86_adx hL hT hI
  coreCT := by rw [coreK_p384x]; exact Proof.Ecdsa.X86_64.P384.sign_ct_adx
  coreNs := by lit_decide
  coreSp := by lit_decide
  coreMx := by lit_decide
  coreD := by lit_decide
  blk := by exact p384_blk

/-- P-384 with BMI2 and ADX (`adx`) or without. -/
def p384Of (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) : RfcCurve :=
  bif adx then p384x hL hT hI else p384 hL hT hI


/-- `vg_ecdsa_p384_sign` (`_adx`, with BMI2 and ADX), with the tables of `vs`. -/
theorem p384T_verified (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs ∧ "VG_P384_COMB" ∉ Proof.HmacTable.X86_64.names vs) :
    Verified X86_64.target (signCodeT (p384Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Ecdsa.X86_64.p384.combConsts vs) := by
  have hsat := sat_one (T := Spec.Ecdsa.Rfc6979.Curves.p384) h.1 Proof.Ecdsa.X86_64.P384.satMem h.2
    (by rw [Proof.Ecdsa.X86_64.P384.p384W_length]; decide) Proof.Ecdsa.X86_64.P384.satMem_held (by decide) rfl
  cases adx
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat
  · exact signT_verified ⟨rfl, by decide, by decide⟩ rfl h.1 hsat


/-! ## The function as emitted -/

theorem p384_stub (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve) (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) (hI : Weierstrass.X86_64.InvSounds) : SignStub (p384Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p384.tries := by
  cases adx <;> (dsimp only [SignStub, cfgS, cfgT, p384Of, cond, p384, p384x]; exact ⟨by lit_decide, by lit_decide⟩)

/-- `vg_ecdsa_p384_sign`, with the tables of `vs`, as emitted (`Impl.Ecdsa.Rfc6979.X86_64.Fn.sign`), its
cleanup included, meets its contract in constant time and returns without secret residue. -/
theorem p384T_scrubbed (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve) (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) (hI : Weierstrass.X86_64.InvSounds) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) (h : OK vs ∧ "VG_P384_COMB" ∉ Proof.HmacTable.X86_64.names vs)
    (hu : ∀ w ∈ vs, HmacUp w) :
    VerifiedScrubbed X86_64.target (Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (cfgT (p384Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs))
      (specK Spec.Ecdsa.Rfc6979.Curves.p384 Impl.Ecdsa.X86_64.p384.combConsts vs) 32 :=
  sign_scrubbed (api := Spec.Ecdsa.Rfc6979.Curves.p384SignApi)
    { tables := [("hmac", Proof.HmacTable.X86_64.tables vs)]
      code := signCodeT (p384Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs
      verified := p384T_verified adx hL hT hI vs h
      spSafe := signCode_sp _ _ _ }
    (signOut _ Impl.Ecdsa.X86_64.p384.combConsts _ _) rfl rfl hu (p384_stub adx hL hT hI)

theorem p384T_spSafe (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve) (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start) (hI : Weierstrass.X86_64.InvSounds) (vs : List Proof.Pbkdf2.Md.X86_64.MdHash) :
    (Impl.Ecdsa.Rfc6979.X86_64.Fn.sign (cfgT (p384Of adx hL hT hI) Spec.Ecdsa.Rfc6979.Curves.p384.tries vs)).all
      (fun i => !VG.X86_64.isa.writesSp i) = true :=
  X86_64.Scrub.scrubKs_spSafe (signCode_sp _ _ _)

end VG.Proof.Ecdsa.Rfc6979.X86_64
