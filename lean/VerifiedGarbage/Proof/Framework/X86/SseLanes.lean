module
public import VerifiedGarbage.TCB.X86.Sse

import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem

/-!
# SSE2 values as their four dword lanes

`L f` is the 128-bit value whose dword lanes are `f 0 … f 3`, and the SSE2
operations on it lane by lane; and the mask of a lane by equality without
`pcmpeqd` (`mask_eq`): for `x ^ j` below 256, `x ^ j - 1` shifted right by 8
is `0x00FFFFFF` if `x = j` and `0` otherwise, and ORed with itself shifted
left by 8 it is all ones or nothing.
-/

@[expose] public section

namespace VG.X86.Lanes

open VG VG.X86

/-! ## Dword lanes -/

/-- The value whose dword lanes are `f 0, f 1, f 2, f 3`. -/
def L (f : Nat → BitVec 32) : BitVec 128 := ofDwords (f 0) (f 1) (f 2) (f 3)

theorem dword_L (f : Nat → BitVec 32) {k : Nat} (hk : k < 4) : dword (L f) k = f k := by
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> simp only [L, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3]

theorem L_dword (x : BitVec 128) : L (dword x ·) = x := ofDwords_dword x

theorem L_congr {f g : Nat → BitVec 32} (h : ∀ k < 4, f k = g k) : L f = L g := by
  simp only [L, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

theorem L_ext {x : BitVec 128} {f : Nat → BitVec 32} (h : ∀ k < 4, dword x k = f k) : x = L f := by
  rw [← L_dword x]; exact L_congr h

theorem dword_pand (a b : BitVec 128) (k : Nat) :
    dword (XBinOp.eval .pand a b) k = dword a k &&& dword b k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [XBinOp.eval, dword, hj]

theorem por_L (f g : Nat → BitVec 32) :
    XBinOp.eval .por (L f) (L g) = L fun k => f k ||| g k :=
  L_ext fun k hk => by rw [dword_por, dword_L _ hk, dword_L _ hk]

theorem pxor_L (f g : Nat → BitVec 32) :
    XBinOp.eval .pxor (L f) (L g) = L fun k => f k ^^^ g k :=
  L_ext fun k hk => by rw [dword_pxor, dword_L _ hk, dword_L _ hk]

theorem pand_L (f g : Nat → BitVec 32) :
    XBinOp.eval .pand (L f) (L g) = L fun k => f k &&& g k :=
  L_ext fun k hk => by rw [dword_pand, dword_L _ hk, dword_L _ hk]

theorem paddd_L (f g : Nat → BitVec 32) :
    XBinOp.eval .paddd (L f) (L g) = L fun k => f k + g k :=
  L_ext fun k hk => by rw [dword_paddd _ _ hk, dword_L _ hk, dword_L _ hk]

theorem psrld_L (f : Nat → BitVec 32) :
    XShiftOp.eval .psrld (L f) 8 = L fun k => f k >>> 8 :=
  L_ext fun k hk => by rw [dword_psrld _ _ (by decide) hk, dword_L _ hk]; rfl

theorem pslld_L (f : Nat → BitVec 32) :
    XShiftOp.eval .pslld (L f) 8 = L fun k => f k <<< 8 :=
  L_ext fun k hk => by rw [dword_pslld _ _ (by decide) hk, dword_L _ hk]; rfl

theorem movdqa_L (a b : BitVec 128) : XBinOp.eval .movdqa a b = b := rfl

/-- A 16-byte load, as its four dwords. -/
theorem readW128_L (m : Mem) (a : Addr) :
    m.readW a 128 = L fun k => m.readW (a + BitVec.ofNat 64 (4 * k)) 32 :=
  L_ext fun _ hk => dword_readW m a hk

/-- `movd` then `pshufd` with order 0: `v` in every lane. -/
theorem bcast_L (v : BitVec 32) : shufDwords ((0 : BitVec 96) ++ v) 0 = L fun _ => v :=
  L_ext fun _ hk => by
    have h := dword_shufDwords_bcast ((0 : BitVec 96) ++ v) (k := 0) (by decide) hk
    rw [show BitVec.ofNat 8 (0x55 * 0) = 0 from rfl] at h
    rw [h]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [dword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
      Nat.mul_zero, Nat.zero_add, ite_true]

/-! ## The mask -/

/-- The mask of an entry: all ones iff the index `x` is `j`. -/
theorem mask_eq {x : BitVec 32} (hx : x.toNat < 256) {j : Nat} (hj : j < 256) :
    (((x ^^^ BitVec.ofNat 32 j) + 0xFFFFFFFF) >>> 8 |||
        ((x ^^^ BitVec.ofNat 32 j) + 0xFFFFFFFF) >>> 8 <<< 8) =
      if x = BitVec.ofNat 32 j then 0xFFFFFFFF else 0 := by
  by_cases h : x = BitVec.ofNat 32 j
  · rw [ite_eq_left h, h, BitVec.xor_self]
    decide
  · rw [ite_eq_right h]
    obtain ⟨z, hz⟩ : ∃ z, x ^^^ BitVec.ofNat 32 j = z := ⟨_, rfl⟩
    have hzl : z.toNat < 256 := by
      rw [← hz, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact Nat.xor_lt_two_pow (n := 8) hx hj
    have hz0 : z ≠ 0 := fun e => h (by
      rw [e] at hz
      have := congrArg (· ^^^ BitVec.ofNat 32 j) hz
      simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at this
      rw [this]; exact BitVec.eq_of_getLsbD_eq (by simp))
    have hz1 : z.toNat ≠ 0 := fun e => hz0 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    rw [hz]
    have hs : (z + 0xFFFFFFFF) >>> 8 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftRight_eq_div_pow,
        show (0xFFFFFFFF : BitVec 32).toNat = 0xFFFFFFFF from rfl, show (0 : BitVec 32).toNat = 0 from rfl]
      omega
    rw [hs]
    rfl

end VG.X86.Lanes
