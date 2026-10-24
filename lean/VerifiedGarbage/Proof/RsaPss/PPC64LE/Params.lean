module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Pre
public import VerifiedGarbage.Spec.RsaPss
import VerifiedGarbage.Proof.RsaPss.Params
import all Init.Data.Nat.Bitwise.Basic

/-!
# RSASSA-PSS verification on PPC64LE: the encoding's parameters

Untrusted: everything here is checked by Lean. For a modulus whose first
byte `n₀` is not zero, `lo` and `c` (`Pre.lean`) are those of EMSA-PSS: `lo`
is 1 exactly when `emLen = k - 1`, and `c` is the mask `0xFF >> (8 emLen -
emBits)` of `maskedDB`'s first byte (`lo_eq`, `cm_eq`), by one check of every
byte (`byte_ok`) and `Proof.RsaPss.emLength_eq`, `Proof.RsaPss.mask_eq`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE

/-- `smear`, `lo` and `c` of a byte. -/
def smB (b : Byte) : BitVec 64 :=
  let a := b.setWidth 64 >>> 1
  let b := a ||| a >>> 1
  let c := b ||| b >>> 2
  c ||| c >>> 4

def loB (b : Byte) : BitVec 64 := (smB b - BitVec.ofNat 64 1) >>> 63

def cmB (b : Byte) : BitVec 64 := smB b ||| ((BitVec.ofNat 64 0 - loB b) &&& BitVec.ofNat 64 0xFF)

theorem byte_ok : ∀ n < 256, n ≠ 0 →
    loB (BitVec.ofNat 8 n) = BitVec.ofNat 64 (if n = 1 then 1 else 0) ∧
      cmB (BitVec.ofNat 8 n) = BitVec.ofNat 64 (if n = 1 then 255 else 2 ^ Nat.log2 n - 1) := by
  decide +kernel

theorem lo_byte (s : State) : lo s = loB (s.mem (s.gpr .r3)) := rfl
theorem cm_byte (s : State) : cm s = cmB (s.mem (s.gpr .r3)) := rfl

section
variable {s : State} (h0 : s.mem (s.gpr .r3) ≠ 0)
include h0

theorem byte_ne : (s.mem (s.gpr .r3)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)

theorem lo_eq : lo s = BitVec.ofNat 64 (if (s.mem (s.gpr .r3)).toNat = 1 then 1 else 0) := by
  have := (byte_ok _ (s.mem (s.gpr .r3)).isLt (byte_ne h0)).1
  rw [lo_byte, ← this, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cm_eq : cm s = (if (s.mem (s.gpr .r3)).toNat = 1 then (0xFF : Byte) else
    BitVec.ofNat 8 (2 ^ Nat.log2 (s.mem (s.gpr .r3)).toNat - 1)).setWidth 64 := by
  have := (byte_ok _ (s.mem (s.gpr .r3)).isLt (byte_ne h0)).2
  rw [cm_byte, BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
  rw [this]
  split
  · rfl
  · have h8 := Proof.RsaPss.log2_lt8 (s.mem (s.gpr .r3))
    have hp : 2 ^ Nat.log2 (s.mem (s.gpr .r3)).toNat ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have hp1 := Nat.one_le_two_pow (n := Nat.log2 (s.mem (s.gpr .r3)).toNat)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

end

end VG.Proof.RsaPss.PPC64LE
