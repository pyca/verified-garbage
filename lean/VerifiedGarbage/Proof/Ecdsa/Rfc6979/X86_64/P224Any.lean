module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.P224
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P224Sha224
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
import VerifiedGarbage.Spec.EcKey.Generic
public import VerifiedGarbage.Proof.P224.Comb7

/-!
# Deterministic ECDSA over P-224 on x86-64, with the hash function as an argument

P-224 as the proof's curve, with a tier `T` of hash functions (`any`); the contract
`Spec.Ecdsa.Rfc6979.P224Sha224.inst.signAnyContract` for 544 bytes of stack and the
comb's table, which a state permits (`sat`): `vg_ecdsa_p224_rfc6979_sign` is
verified (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.P224Any

open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (Tier)
open VG.Proof.Ecdsa.X86_64.P224 (p224_combConsts p224W_length satMem satMem_held)

/-- P-224 with the tier `T`. -/
def any (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) : RfcAny where
  R := p224 hL hT hI
  T := T
  I0 := Spec.Ecdsa.Rfc6979.P224Sha224.inst
  ecdsa := rfl
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  scratch := rfl

/-- The comb's table. -/
theorem combConsts (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) :
    (any hL hT hI T).R.E.combConsts = [("VG_P224_COMB", VG.Proof.Ecdsa.X86_64.P224.p224W)] := by
  exact p224_combConsts

theorem shape (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) : RfcAny.TblShape (any hL hT hI T).R.E.combConsts :=
  .inr ⟨_, _, combConsts hL hT hI T⟩

theorem sat (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) : ∃ s, (any hL hT hI T).contract.pre s := by
  have hl := p224W_length
  have hc := combConsts hL hT hI T
  have hq : (any hL hT hI T).I0.ecdsa.curve.len = 28 := rfl
  refine (any hL hT hI T).sat_of (shape hL hT hI T) (m := satMem) (Tr := [⟨0x100000, 151552⟩])
    (by rw [hc, Abi.constRegions_cons, Abi.constRegions_nil, hl]) (by rw [hq]; decide) ?_
  rw [hc, hq]
  refine ⟨fun c hc => ?_, ?_⟩
  · simp only [List.mem_singleton] at hc; subst hc; exact satMem_held
  · rw [Abi.constRegions_cons, Abi.constRegions_nil, Sig.forall_mem_const_single]
    refine ⟨by rw [hl]; decide, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by rw [hl]; decide)

theorem sign_verified (hL : Weierstrass.Law Spec.P224.curve)
    (hT : Weierstrass.CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : Weierstrass.X86_64.InvSounds) (T : Tier) :
    Verified X86_64.target (any hL hT hI T).code (any hL hT hI T).contract :=
  (any hL hT hI T).verified (shape hL hT hI T) (sat hL hT hI T)

end VG.Proof.Ecdsa.Rfc6979.X86_64.P224Any
