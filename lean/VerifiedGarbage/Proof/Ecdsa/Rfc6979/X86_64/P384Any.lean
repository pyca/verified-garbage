module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P384Adx
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P384Sha384
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
public import VerifiedGarbage.Proof.P384.Comb7

/-!
# Deterministic ECDSA over P-384 on x86-64, with the hash function as an argument

P-384 as the proof's curve, with a tier `T` of hash functions and its multiplication
with BMI2 and ADX (`adx`) or without (`any`); the contract
`Spec.Ecdsa.Rfc6979.P384Sha384.inst.signAnyContract` for 544 bytes of stack and the
comb's table, which a state permits (`sat`): `vg_ecdsa_p384_rfc6979_sign` is
verified (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P384Any

open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (Tier)
open VG.Proof.Ecdsa.X86_64.P384 (p384_combConsts p384W_length satMem satMem_held)

/-- P-384 with the tier `T`, and its multiplication with BMI2 and ADX (`adx`) or without. -/
def any (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) : RfcAny where
  R := p384Of adx hL hT hI
  T := T
  I0 := Spec.Ecdsa.Rfc6979.P384Sha384.inst
  ecdsa := by cases adx <;> rfl
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  scratch := rfl

/-- The comb's table. -/
theorem combConsts (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) :
    (any adx hL hT hI T).R.E.combConsts = [("VG_P384_COMB", VG.Proof.Ecdsa.X86_64.P384.p384W)] := by
  cases adx <;> exact p384_combConsts

theorem shape (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) : RfcAny.TblShape (any adx hL hT hI T).R.E.combConsts :=
  .inr ⟨_, _, combConsts adx hL hT hI T⟩

theorem sat (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) : ∃ s, (any adx hL hT hI T).contract.pre s := by
  have hl := p384W_length
  have hc := combConsts adx hL hT hI T
  have hq : (any adx hL hT hI T).I0.ecdsa.curve.len = 48 := rfl
  refine (any adx hL hT hI T).sat_of (shape adx hL hT hI T) (m := satMem) (Tr := [⟨0x100000, 337920⟩])
    (by rw [hc, Abi.constRegions_cons, Abi.constRegions_nil, hl]) (by rw [hq]; decide) ?_
  rw [hc, hq]
  refine ⟨fun c hc => ?_, ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact satMem_held
  · rw [Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
    refine ⟨by rw [hl]; decide, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by rw [hl]; decide)

theorem sign_verified (adx : Bool) (hL : Weierstrass.Law Spec.P384.curve)
    (hT : Weierstrass.CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) :
    Verified X86_64.target (any adx hL hT hI T).code
      (Spec.Ecdsa.Rfc6979.P384Sha384.inst.signAnyContract (X86_64.abi.withConsts Impl.Ecdsa.X86_64.p384.combConsts) 544) := by
  cases adx <;> exact (any _ hL hT hI T).verified (shape _ hL hT hI T) (sat _ hL hT hI T)

end VG.Proof.Ecdsa.Rfc6979.X86_64.P384Any
