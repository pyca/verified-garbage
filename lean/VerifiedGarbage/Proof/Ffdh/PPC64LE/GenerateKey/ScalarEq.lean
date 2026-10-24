module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Body
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Dsa.PackedBytes

/-!
# `vg_ffdh_generate_key` on PPC64LE: x is the spec's scalar

The octets the code cuts x to (`gkOct`) are `KeyScalar.cut` of `rand` at the
bound's first nonzero octet (`bptr_bnd`), so x is `scalarOfOctets` of `rand`
(`gkOct_eq`).
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

theorem gkOct_length (m : Mem) (D R : Addr) {k L : Nat} (hk : 1 ≤ k) : (gkOct m D R k L).length = k := by
  have hl : (bytesAt m (bptr D k L) k).length = k := by simp [bytesAt]
  have hne : bytesAt m (bptr D k L) k ≠ [] := fun he => by rw [he] at hl; simp at hl; omega
  have := Proof.Ffdh.lead_lt hne
  have hR : (bytesAt m R k).length = k := by simp [bytesAt]
  unfold gkOct
  rw [cut_length _ (by rw [hR]; omega), hR]

/-- x's octets are the scalar of the attempt. -/
theorem gkOct_eq (m : Mem) (D R : Addr) {k L : Nat} (hk : 1 ≤ k) (hL : L = 2 * k ∨ L = 3 * k)
    (hp : L ≠ 3 * k → os2ip (bytesAt m D k) % 2 = 1 ∧ 1 < os2ip (bytesAt m D k)) :
    os2ip (gkOct m D R k L) = Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf k (bytesAt m D L)) (bytesAt m R k) := by
  have hl : (bytesAt m D L).length = L := by simp [bytesAt]
  have hd : (bytesAt m D L).length = 2 * k ∨ (bytesAt m D L).length = 3 * k := by rw [hl]; exact hL
  unfold gkOct smeared
  rw [bptr_bnd m D hL]
  refine cut_eq hk hd (fun h3 => ?_) (by simp [bytesAt]) ?_
  · rw [Proof.Ffdh.take_bytesAt m D (by omega)]; exact hp (by rw [hl] at h3; exact h3)
  · rw [Proof.Ffdh.getD_of (Proof.Ffdh.lead_lt (by
        intro he; have := bnd_length hd; rw [he] at this; simp at this; omega))]
    have hlt := BitVec.isLt ((bnd k (bytesAt m D L))[lead (bnd k (bytesAt m D L))]'(Proof.Ffdh.lead_lt (by
        intro he; have := bnd_length hd; rw [he] at this; simp at this; omega)))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (smearN_lt _ hlt), smearN_eq _ hlt]

end VG.Proof.Ffdh.PPC64LE.GenerateKey
