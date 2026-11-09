module

import VerifiedGarbage.Proof.RsaPss.PPC64LE.Prefix
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Shift
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Cmp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid

/-!
# RSASSA-PSS verification on PPC64LE: the mask of an equality

Untrusted: everything here is checked by Lean. `eq_mask`: the mask of
the equality of two values below `2⁶³`, as the code computes it.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa copyLoop)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view view_w8 sc_in sc_inR sc_inW fx hiRegs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_subi wp_sub wp_xor wp_and wp_lsr wp_lbz wp_stb
  wp_nil wp_countdown)
open VG.Proof.Mgf1 (ifp ifn)

/-- `-((L ⊕ sl) - 1 >>> 63)`: all ones if `L = sl`, zero if not, for `L, sl < 2^63`. -/
theorem eq_mask {L sl : Nat} (hL : L < 2 ^ 63) (hs : sl < 2 ^ 63) :
    BitVec.ofNat 64 0 - (((BitVec.ofNat 64 L ^^^ BitVec.ofNat 64 sl) - BitVec.ofNat 64 1) >>> 63) =
      if L = sl then BitVec.allOnes 64 else 0#64 := by
  have hx : (BitVec.ofNat 64 L ^^^ BitVec.ofNat 64 sl).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    exact Nat.xor_lt_two_pow hL hs
  rw [isz64 hx]
  by_cases e : L = sl
  · subst e; rw [BitVec.xor_self, ifp rfl, ifp rfl]; decide
  · have : BitVec.ofNat 64 L ^^^ BitVec.ofNat 64 sl ≠ 0#64 := fun h => e (by
      have := BitVec.xor_eq_zero_iff.mp h
      have := congrArg BitVec.toNat this
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)] at this)
    rw [ifn this, ifn e]; decide

end VG.Proof.RsaPss.PPC64LE
