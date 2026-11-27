module
public import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Isa

import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.Contract

/-! # ByteDecode12 contract and input representation -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Decode12

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev B : List Byte := bytesAt s₀.mem (bP s₀) 384
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((decode12 (B s₀))[i]!).val
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((B s₀).getD j 0).toNat

end

theorem G_even (s₀ : State) {k : Nat} (hk : k < 128) :
    G s₀ (2 * k) = BitVec.ofNat 32 (condSub (byte s₀ (3 * k) + (byte s₀ (3 * k + 1) % 16) * 256)) := by
  have : byte s₀ (3 * k) < 256 := byte_lt _
  have : byte s₀ (3 * k + 1) < 256 := byte_lt _
  have : ((B s₀).getD (3 * k) 0).toNat < 256 := byte_lt _
  have : ((B s₀).getD (3 * k + 1) 0).toNat < 256 := byte_lt _
  have hq : q = 3329 := rfl
  rw [G, decode12_even _ (bytesAt_length _ _ _) hk, val_ofNat, condSub_eq (by omega_arith), Nat.mul_comm 256]

theorem G_odd (s₀ : State) {k : Nat} (hk : k < 128) :
    G s₀ (2 * k + 1) = BitVec.ofNat 32 (condSub (byte s₀ (3 * k + 1) / 16 + byte s₀ (3 * k + 2) * 16)) := by
  have : byte s₀ (3 * k + 1) < 256 := byte_lt _
  have : byte s₀ (3 * k + 2) < 256 := byte_lt _
  have : ((B s₀).getD (3 * k + 1) 0).toNat < 256 := byte_lt _
  have : ((B s₀).getD (3 * k + 2) 0).toNat < 256 := byte_lt _
  have hq : q = 3329 := rfl
  rw [G, decode12_odd _ (bytesAt_length _ _ _) hk, val_ofNat, condSub_eq (by omega_arith), Nat.mul_comm 16]

end VG.Proof.MlKem.AArch64.Decode12
