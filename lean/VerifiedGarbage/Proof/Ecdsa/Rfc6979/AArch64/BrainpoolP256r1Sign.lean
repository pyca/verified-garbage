module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.AnyHash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP256r1
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA over brainpoolP256r1 on AArch64, with any hash function

The contract `Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.signAnyContract` (the instance's hash function
unused) for 512 bytes of stack, which implies the one the proof is
written against (`implies`, with a witness of its precondition, `sat`):
`vg_ecdsa_brainpoolp256r1_rfc6979_sign` is verified for each tier of hash functions
(`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP256r1Sign

open VG VG.AArch64

/-- A state satisfying the proof's precondition. -/
theorem sat : ∃ s, (rfcAArch64 Impl.Ecdsa.AArch64.brainpoolp256r1 Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst 512).pre s := by
  refine ⟨{ satState 32 (fun _ => 0) 0 with rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩] }, by decide,
    fun G hG => by cases hG; rfl, by rw [tableRegions_nt rfl]; rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩
  all_goals rw [show Impl.Ecdsa.AArch64.brainpoolp256r1.combWords = [] from rfl]
  · exact fun i hi => absurd hi (Nat.not_lt_zero _)
  · rw [tableAddr]; decide
  · intro r _ x hx
    simp only [Region.Contains, List.length_nil, Nat.mul_zero] at hx
    omega

theorem implies :
    (rfcAArch64 Impl.Ecdsa.AArch64.brainpoolp256r1 Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst 512).Implies
      (Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.signAnyContract AArch64.abi 512) :=
  implies_nt rfl rfl rfl sat

theorem sign_verified (t : Pbkdf2.Md.AArch64.Tier) (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target (cfgT (brainpoolp256r1 hL hI) t Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.tries).sign
      (Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst.signAnyContract AArch64.abi 512) :=
  AArch64.sign_verified (R := brainpoolp256r1 hL hI) (J := Spec.Ecdsa.Rfc6979.BrainpoolP256r1Sha256.inst) rfl (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.BrainpoolP256r1Sign
