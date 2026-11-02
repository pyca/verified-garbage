module

import VerifiedGarbage.Proof.MillerRabin.X86.CallEntry
public import VerifiedGarbage.Proof.MillerRabin.Word32
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Mont.X86.Compact.Arithmetic
public import VerifiedGarbage.Proof.MillerRabin.X86.Modulus
public import VerifiedGarbage.TCB.X86.Target

/-! # The callable Montgomery postcondition gives the round's exact product -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem mulPost {g : Geometry} {s t : State} {capacity b c : Nat}
    (ptrBound : g.W.toNat < 2 ^ 32) (capBound : capacity < 2 ^ 32) (bBound : b < 8)
    (a0 : arg s 0 = BitVec.ofNat 32 g.W.toNat) (a1 : arg s 1 = BitVec.ofNat 32 capacity)
    (a2 : arg s 2 = 6#32) (a3 : arg s 3 = 6#32) (a4 : arg s 4 = BitVec.ofNat 32 b)
    (M : Modulus g c s.mem) (odd : c % 2 = 1)
    (post : (Proof.Rsa.Mont.mulContract abi 56).post s t) :
    val32 t.mem g.W (g.array 6) g.words = Word32.mm c g.w
      (val32 s.mem g.W (g.array 6) g.words) (val32 s.mem g.W (g.array b) g.words) ∧
    Proof.Rsa.Mont.Keeps g.W capacity g.w 6 s.mem t.mem := by
  have ptr : (BitVec.ofNat 32 g.W.toNat).setWidth 64 = g.W := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt g.W.isLt
  sig_post [Proof.Rsa.Mont.mulContract, Proof.Rsa.Mont.sig, abi, argSlots, argVal, argBytes] at post
  simp only [a0, a1, a2, a3, a4, ptr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt capBound,
    Nat.mod_eq_of_lt (by omega : b < 2 ^ 32), M.width] at post
  obtain ⟨low, congruence, keeps⟩ := post
  refine ⟨?_, keeps⟩
  rw [VG.Proof.Mont.X86.Compact.numAt_val32, VG.Proof.Mont.X86.Compact.numAt_val32] at low
  rw [VG.Proof.Mont.X86.Compact.numAt_val32, VG.Proof.Mont.X86.Compact.numAt_val32,
    VG.Proof.Mont.X86.Compact.numAt_val32, VG.Proof.Mont.X86.Compact.numAt_val32] at congruence
  change val32 t.mem g.W (g.array 6) g.words < val32 s.mem g.W (g.array 0) g.words at low
  change val32 t.mem g.W (g.array 6) g.words * 2 ^ (64 * g.w) % val32 s.mem g.W (g.array 0) g.words =
    val32 s.mem g.W (g.array 6) g.words * val32 s.mem g.W (g.array b) g.words %
      val32 s.mem g.W (g.array 0) g.words at congruence
  rw [M.candidate] at low congruence
  exact Word32.mm_eq odd low congruence

end VG.Proof.MillerRabin.X86
