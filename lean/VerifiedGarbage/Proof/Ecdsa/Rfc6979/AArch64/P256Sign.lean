module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Verified
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.AnyHash
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Tables
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.P256
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA over P-256 on AArch64, with any hash function

The contract `Spec.Ecdsa.Rfc6979.P256Sha256.inst.signAnyContract` (the instance's hash function
unused) for 512 bytes of stack and the comb's tables, which implies the one the proof is
written against (`implies`, with a witness of its precondition, `sat`):
`vg_ecdsa_p256_rfc6979_sign` is verified for each tier of hash functions
(`sign_verified`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64.P256Sign

open VG VG.AArch64
open VG.Proof.Ecdsa.AArch64 (p256_combWords_length satMem satMem_held)

/-- A state satisfying the proof's precondition, with the comb's tables. -/
theorem sat : ∃ s, (rfcAArch64 Impl.Ecdsa.AArch64.p256 Spec.Ecdsa.Rfc6979.P256Sha256.inst 512).pre s := by
  have hl := p256_combWords_length
  refine ⟨satState 32 satMem 151552, by decide, fun G hG => by cases hG; rfl,
    by rw [tableRegions_of rfl, hl]; rfl, rfl, Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
    Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_⟩
  all_goals rw [tableAddr_of rfl]
  · exact satMem_held
  · rw [hl]; decide
  · rw [hl]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)

theorem implies :
    (rfcAArch64 Impl.Ecdsa.AArch64.p256 Spec.Ecdsa.Rfc6979.P256Sha256.inst 512).Implies
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signAnyContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts) 512) :=
  implies_of rfl rfl sat

theorem sign_verified (t : Pbkdf2.Md.AArch64.Tier) (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target (cfgT (p256 hL hI hT) t Spec.Ecdsa.Rfc6979.P256Sha256.inst.tries).sign
      (Spec.Ecdsa.Rfc6979.P256Sha256.inst.signAnyContract (AArch64.abi.withConsts Impl.Ecdsa.AArch64.p256.combConsts) 512) :=
  AArch64.sign_verified (R := p256 hL hI hT) (J := Spec.Ecdsa.Rfc6979.P256Sha256.inst) rfl (Nat.le_of_ble_eq_true rfl)
    (Nat.le_of_ble_eq_true rfl) implies

end VG.Proof.Ecdsa.Rfc6979.AArch64.P256Sign
