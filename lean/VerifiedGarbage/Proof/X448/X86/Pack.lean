module

import VerifiedGarbage.Proof.X448.X86.ByteMem
public import VerifiedGarbage.Proof.X448.Radix16Bytes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86.Field
import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# X448 on x86 (32-bit): encoding a 16-bit limb

Two byte stores encode each 16-bit limb in little-endian order without
requiring output alignment.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def packMem (m : Mem) (p : Addr) (i : Nat) (v : BitVec 32) : Mem :=
  (m.writeW (off p (2 * i)) (v.setWidth 8)).writeW (off p (2 * i + 1)) ((v >>> 8).setWidth 8)

theorem packMem_decoded (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32)
    (hv : v.toNat < radix) : decoded (packMem m p i v) p i = v.toNat := by
  have hn : off p (2 * i) ≠ off p (2 * i + 1) := by
    rw [ne_eq, off_eq_iff p (by omega_using [hi]) (by omega_using [hi])]; omega_using []
  simp only [decoded, byteN, packMem, writeW8_apply, hn, ite_false, ite_true,
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [radix] at hv
  omega_using [hv]

theorem packMem_outside (m : Mem) (p : Addr) {i : Nat} (hi : i < 28) (v : BitVec 32) :
    Outside p (2 * i) 2 m (packMem m p i v) := by
  intro x hx
  rw [packMem, writeW8_outside _ _ _ (by omega_using [hi]) (by omega_using [hx]),
    writeW8_outside _ _ _ (by omega_using [hi]) (by omega_using [hx])]

end VG.Proof.X448.X86
