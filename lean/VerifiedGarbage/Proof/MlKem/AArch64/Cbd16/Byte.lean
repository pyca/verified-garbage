module

public import VerifiedGarbage.Proof.MlKem.Encode

/-! # CBD2 byte arithmetic

The SIMD byte operations preserve both four-bit differences independently.
The finite lemma checks every possible input byte with Lean's kernel.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16
open VG VG.Spec.MlKem

def sums (b : BitVec 8) : BitVec 8 := (b &&& 0x55#8) + ((b >>> 1) &&& 0x55#8)
def differences (b : BitVec 8) : BitVec 8 :=
  ((sums b &&& 0x33#8) + 0x22#8) - ((sums b >>> 2) &&& 0x33#8)
def nibble (b : BitVec 8) (high : Bool) : BitVec 8 :=
  if high then differences b >>> 4 else differences b &&& 0x0f#8

def canonical (x : BitVec 8) : BitVec 32 :=
  let y := x.setWidth 32 + 3327#32
  if y.toNat ≤ (y - 3329#32).toNat then y else y - 3329#32

theorem byte_values : ∀ v < 256,
    (nibble (BitVec.ofNat 8 v) false).toNat ≤ 4 ∧
    (nibble (BitVec.ofNat 8 v) true).toNat ≤ 4 ∧
    (canonical (nibble (BitVec.ofNat 8 v) false)).toNat =
      (cbdX v + 3329 - cbdY v) % 3329 ∧
    (canonical (nibble (BitVec.ofNat 8 v) true)).toNat =
      (cbdX (v / 16) + 3329 - cbdY (v / 16)) % 3329 := by
  decide +kernel


theorem nibble_values : ∀ v < 256, ∀ h : Bool,
    (nibble (BitVec.ofNat 8 v) h).toNat ≤ 4 ∧
    ((nibble (BitVec.ofNat 8 v) h).toNat + 3327) % 3329 =
      (cbdX (v / if h then 16 else 1) + 3329 - cbdY (v / if h then 16 else 1)) % 3329 := by
  decide +kernel

end VG.Proof.MlKem.AArch64.Cbd16
