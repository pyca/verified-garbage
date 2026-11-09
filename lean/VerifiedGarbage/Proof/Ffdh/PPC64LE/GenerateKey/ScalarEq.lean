module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Dsa.PackedBytes

/-!
# `vg_ffdh_generate_key` on PPC64LE: x is the spec's scalar

The bound's octets at `bptr` are `KeyScalar.bnd` of the domain
(`bptr_bnd`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.Proof.Mont VG.Proof.Ffdh.KeyScalar
open VG.Spec.Rsa (bytesAt os2ip)

/-- The bound's octets the code scans are `KeyScalar.bnd`'s. -/
theorem bptr_bnd (m : Mem) (D : Addr) {k L : Nat} (hL : L = 2 * k ∨ L = 3 * k) :
    bytesAt m (bptr D k L) k = bnd k (bytesAt m D L) := by
  have hl : (bytesAt m D L).length = L := by simp [bytesAt]
  unfold bptr bnd
  rw [hl]
  by_cases hq : L = 3 * k
  · rw [ite_eq_left hq, ite_eq_left hq, VG.Proof.Dsa.bytesAt_slice m D (by omega : 2 * k + k ≤ L)]
  · rw [ite_eq_right hq, ite_eq_right hq, Proof.Ffdh.take_bytesAt m D (by omega)]

end VG.Proof.Ffdh.PPC64LE.GenerateKey
