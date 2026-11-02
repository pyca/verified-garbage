module

import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderRead
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Header

/-! # The initialized header satisfies the existing Montgomery layout contract -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Mont VG.Impl.Bignum.X86.PublicContext

theorem zeroHigh (x : BitVec 32) : 0#32 ++ x = x.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  have := x.isLt
  omega

theorem width_eq {base : Addr} {p : BitVec 32} {w : Nat} {m : Mem} (bound : w < 2 ^ 32) :
    Proof.Rsa.Mont.wOf (headerMemory base p w m) base = w := by
  change ((headerMemory base p w m).readW (off base 48) 64).toNat = w
  rw [header_width, zeroHigh]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem slot_eq (w j : Nat) : slot w j = Proof.Rsa.Mont.arrAt w j := by
  unfold slot stride VG.Impl.Bignum.hdrBytes Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes
  simp only [Nat.mul_add]

theorem layout {base : Addr} {p : BitVec 32} {w wsLen : Nat} {m : Mem}
    (baseEq : p.setWidth 64 = base) (positive : 2 ≤ w) (bound : w < 2 ^ 31)
    (fit : Proof.Rsa.Mont.arrAt w 8 ≤ 8 * wsLen) (nowrap : base.toNat + 8 * wsLen ≤ 2 ^ 32) :
    Proof.Rsa.Mont.Layout (headerMemory base p w m) base wsLen := by
  unfold Proof.Rsa.Mont.Layout
  rw [width_eq (by omega)]
  refine ⟨positive, bound, fit, ?_⟩
  intro j index
  change (headerMemory base p w m).readW (off base (8 * (8 + j))) 64 = _
  rw [show 8 * (8 + j) = 64 + 8 * j by omega, header_pointer index, zeroHigh]
  change addr p (slot w j) = _
  rw [addr_eq, baseEq, slot_eq]
  have pNat : p.toNat = base.toNat := by
    rw [← baseEq, BitVec.toNat_setWidth]
    have := p.isLt
    omega
  have offset : slot w j < Proof.Rsa.Mont.arrAt w 8 := by
    rw [← slot_eq]
    unfold slot stride
    have := Nat.mul_lt_mul_of_pos_right index (by omega : 0 < 8 * w + 16)
    omega
  omega

theorem mr_layout {base : Addr} {p : BitVec 32} {w wsLen : Nat} {m : Mem}
    (baseEq : p.setWidth 64 = base) (positive : 4 ≤ w) (bound : w ≤ 64)
    (fit : Proof.Rsa.Mont.arrAt w 28 ≤ 8 * wsLen) (nowrap : base.toNat + 8 * wsLen ≤ 2 ^ 32) :
    Proof.MillerRabin.Round.Layout Proof.MillerRabin.Round.compact (headerMemory base p w m) base wsLen := by
  unfold Proof.MillerRabin.Round.Layout
  rw [width_eq (by omega)]
  refine ⟨Or.inr rfl, layout baseEq (by omega) (by omega) ?_ nowrap, positive, by omega, ?_, ?_⟩
  · unfold Proof.Rsa.Mont.arrAt Proof.Rsa.Mont.hdrBytes at fit ⊢
    omega
  · exact fit
  · change (headerMemory base p w m).readW (off base 224) 64 = BitVec.ofNat 64 (8 * (w + 2))
    rw [header_stride, zeroHigh]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, stride]
    omega

end VG.Proof.RsaKeyGen.X86.Header
