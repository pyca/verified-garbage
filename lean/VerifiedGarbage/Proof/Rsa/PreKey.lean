module

public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

-- separate module: every architecture's `*_precomputed` witnesses share this key (the PKCS#1, PSS and OAEP registrations on every ISA import it).

/-!
# A key with its precomputed values, for the precomputed contracts' witnesses

The `*_precomputed` contracts require `pre` to hold `privatePrecompute` of
`n`, `p` and `q`, so a state meeting one needs a real key: `keyMem`, and
`key_pre_of` for any memory that agrees with it on the key's buffers.
-/

@[expose] public section

namespace VG.Proof.Rsa.PreKey

open VG

/-! ## A key for the witness

`p = q = 2²⁵⁶ − 1` (32 octets each) and `n = p q` (64 octets): `n` is odd,
at least `2⁵¹¹`, and `p q = n`, so `privatePrecompute` has a value, `kPre`
(24 words). `keyMem` holds `n` at `0x2000`, `p` at `0x4200`, `q` at
`0x4300` and `kPre` at `0x4800`. -/

def kP : Nat := 2 ^ 256 - 1
def kN : Nat := kP * kP

/-- The key's precomputed values. -/
def kPre : List (BitVec 64) :=
  (Spec.Rsa.privatePrecompute (Spec.Rsa.i2osp kN 64) (Spec.Rsa.i2osp kP 32) (Spec.Rsa.i2osp kP 32)).getD []

/-- Whether the address `i` is in the key's buffers. -/
def keyIn (i : Nat) : Bool :=
  (Nat.ble 0x2000 i && Nat.blt i 0x2040) || (Nat.ble 0x4200 i && Nat.blt i 0x4220) ||
    (Nat.ble 0x4300 i && Nat.blt i 0x4320) || (Nat.ble 0x4800 i && Nat.blt i 0x48C0)

/-- The key's buffers. -/
def keyMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.blt i 0x2040 then (Spec.Rsa.i2osp kN 64).getD (i - 0x2000) 0
  else bif Nat.blt i 0x4800 then 0xFF
  else BitVec.ofNat 8 ((kPre.getD ((i - 0x4800) / 8) 0).toNat / 256 ^ ((i - 0x4800) % 8))

theorem keyMem_pre : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt keyMem 0x2000 64)
    (Spec.Rsa.bytesAt keyMem 0x4200 32) (Spec.Rsa.bytesAt keyMem 0x4300 32) =
      some (Spec.Rsa.wordsAt keyMem 0x4800 24) := by lit_decide

/-- A memory that agrees with `keyMem` on the key's buffers holds the key. -/
theorem key_pre_of {m : Mem} (h : ∀ a : Addr, keyIn a.toNat = true → m a = keyMem a) :
    Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt m 0x2000 64) (Spec.Rsa.bytesAt m 0x4200 32)
      (Spec.Rsa.bytesAt m 0x4300 32) = some (Spec.Rsa.wordsAt m 0x4800 24) := by
  have hb : ∀ (A : Addr) (L : Nat), (∀ i < L, keyIn (A + BitVec.ofNat 64 i).toNat = true) →
      Spec.Rsa.bytesAt m A L = Spec.Rsa.bytesAt keyMem A L := fun A L hk =>
    List.map_congr_left fun i hi => h _ (hk i (List.mem_range.mp hi))
  have kin : ∀ (A : Addr) (i : Nat), A.toNat + i < 0x300000 →
      (A + BitVec.ofNat 64 i).toNat = A.toNat + i := fun A i h => by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have kb : ∀ (A : Addr) (L : Nat), A.toNat + L < 0x300000 →
      (∀ i < L, keyIn (A.toNat + i) = true) → ∀ i < L, keyIn (A + BitVec.ofNat 64 i).toNat = true :=
    fun A L hL h i hi => by rw [kin A i (by omega)]; exact h i hi
  have ki : ∀ x, ((0x2000 ≤ x ∧ x < 0x2040) ∨ (0x4200 ≤ x ∧ x < 0x4220) ∨ (0x4300 ≤ x ∧ x < 0x4320) ∨
      (0x4800 ≤ x ∧ x < 0x48C0)) → keyIn x = true := fun x hx => by
    simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; omega
  rw [hb 0x2000 64 (kb _ _ (by decide) fun i hi => ki _ (by have : (0x2000 : Addr).toNat = 0x2000 := rfl; omega)),
    hb 0x4200 32 (kb _ _ (by decide) fun i hi => ki _ (by have : (0x4200 : Addr).toNat = 0x4200 := rfl; omega)),
    hb 0x4300 32 (kb _ _ (by decide) fun i hi => ki _ (by have : (0x4300 : Addr).toNat = 0x4300 := rfl; omega))]
  have hw : Spec.Rsa.wordsAt m 0x4800 24 = Spec.Rsa.wordsAt keyMem 0x4800 24 := by
    refine List.map_congr_left fun i hi => Mem.readW_congr fun j hj => h _ ?_
    have hi := List.mem_range.mp hi
    have e0 : (0x4800 : Addr).toNat = 0x4800 := rfl
    have e1 : ((0x4800 : Addr) + BitVec.ofNat 64 (8 * i)).toNat = 0x4800 + 8 * i := kin _ _ (by omega)
    rw [kin _ j (by rw [e1]; omega), e1]
    exact ki _ (by omega)
  rw [hw]
  exact keyMem_pre

end VG.Proof.Rsa.PreKey
