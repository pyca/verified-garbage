module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384
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

/-!
# Deterministic ECDSA over brainpoolP384r1 on x86-64, with the hash function as an argument

brainpoolP384r1 as the proof's curve, with a tier `T` of hash functions (`any`); the contract
`Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst.signAnyContract` for 544 bytes of stack, which a state permits (`sat`): `vg_ecdsa_brainpoolp384r1_rfc6979_sign` is
verified (`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Any

open VG VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (Tier)

/-- brainpoolP384r1 with the tier `T`. -/
def any (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (hI : Weierstrass.X86_64.InvSounds) (T : Tier) : RfcAny where
  R := brainpoolp384r1 hL hI
  T := T
  I0 := Spec.Ecdsa.Rfc6979.BrainpoolP384r1Sha384.inst
  ecdsa := rfl
  tries_pos := Nat.le_of_ble_eq_true rfl
  tries_lt := Nat.le_of_ble_eq_true rfl
  scratch := rfl

theorem shape (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (hI : Weierstrass.X86_64.InvSounds) (T : Tier) :
    RfcAny.TblShape (any hL hI T).R.E.combConsts := .inl rfl

theorem sat (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (hI : Weierstrass.X86_64.InvSounds) (T : Tier) :
    ∃ s, (any hL hI T).contract.pre s := by
  have hq : (any hL hI T).I0.ecdsa.curve.len = 48 := rfl
  exact (any hL hI T).sat_of (shape hL hI T) (m := fun _ => 0) (Tr := []) rfl (by rw [hq]; decide)
    ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem sign_verified (hL : Weierstrass.Law Spec.BrainpoolP384r1.curve) (hI : Weierstrass.X86_64.InvSounds) (T : Tier) :
    Verified X86_64.target (any hL hI T).code (any hL hI T).contract :=
  (any hL hI T).verified (shape hL hI T) (sat hL hI T)

end VG.Proof.Ecdsa.Rfc6979.X86_64.BrainpoolP384r1Any
