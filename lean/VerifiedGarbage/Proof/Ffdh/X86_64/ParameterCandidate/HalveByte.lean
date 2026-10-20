module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH parameter candidates on x86-64: one byte of q -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

private theorem half_or (b : Byte) {carry : Nat} (hc : carry ≤ 1) :
    b.toNat / 2 ||| 128 * carry = b.toNat / 2 + 128 * carry := by
  have hb := b.isLt
  have he : carry = 0 ∨ carry = 1 := by omega
  rcases he with rfl | rfl
  · simp
  · simpa only [Nat.mul_one] using Nat.or_two_pow_eq_add_of_lt (show b.toNat / 2 < 2 ^ 7 by omega)

theorem half_machine (b : Byte) {carry : Nat} (hc : carry ≤ 1) :
    (((b.setWidth 64) >>> 1) ||| BitVec.ofNat 64 (128 * carry)).setWidth 8 = halfByte carry b := by
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  rw [halfByte_val hc]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 128 * carry < 2 ^ 64 by omega), half_or b hc,
    Nat.mod_eq_of_lt (show b.toNat / 2 + 128 * carry < 2 ^ 8 by omega)]

theorem carry_machine (b : Byte) :
    ((b.setWidth 64 &&& 1) <<< 7) = BitVec.ofNat 64 (128 * (b.toNat % 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    show (1 : BitVec 64).toNat = 1 from rfl]
  rw [Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by have := b.isLt; omega), Nat.and_one_is_mod]
  congr 1
  omega

theorem halveByte_ok {s : State} {op : Addr} {j k carry : Nat} {b : Byte}
    (hj : j < k) (hk : k < 2 ^ 31) (hc : carry ≤ 1)
    (hp : s.gpr .r10 = off op j) (hn : s.gpr .rcx = BitVec.ofNat 64 (k - j))
    (hcarry : s.gpr .r8 = BitVec.ofNat 64 (128 * carry))
    (hrd : InRegions (s.rd ++ s.wr) (off op j) 1) (hwr : InRegions s.wr (off op j) 1)
    (hb : s.mem (off op j) = b) :
    WP isa (.block halveByte) s fun t =>
      t.mem = s.mem.writeW (off op j) (halfByte carry b) ∧
      t.gpr .r10 = off op (j + 1) ∧ t.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
      t.gpr .r8 = BitVec.ofNat 64 (128 * (b.toNat % 2)) ∧
      t.zf = some (decide (j + 1 = k)) ∧ Keep [.rax, .rdx, .r8, .r10, .rcx] s t := by
  have hsub : BitVec.ofNat 64 (k - j) - 1 = BitVec.ofNat 64 (k - (j + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  have hz : (BitVec.ofNat 64 (k - (j + 1)) == 0) = decide (j + 1 = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
      omega
    · intro h
      rw [h, Nat.sub_self]
      rfl
  have hp' : off op j + 1 = off op (j + 1) := by
    simp only [off, BitVec.add_assoc, ofNat_add_one]
  refine WP.mono (WP.keep [.rax, .rdx, .r8, .r10, .rcx]
    (Q := fun t => t.mem = s.mem.writeW (off op j) (halfByte carry b) ∧
      t.gpr .r10 = off op (j + 1) ∧ t.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
      t.gpr .r8 = BitVec.ofNat 64 (128 * (b.toNat % 2)) ∧ t.zf = some (decide (j + 1 = k)))
    (by unfold halveByte; xrun [State.ea, at0, hp, hn, hcarry,
      show off op j + BitVec.ofInt 64 0 = off op j from by simp,
      hrd, hwr, hb, half_machine b hc, carry_machine b, hsub, hz, hp']) rfl)
    fun _ ⟨⟨hm, hp', hn', hc', hz'⟩, hkeep⟩ => ⟨hm, hp', hn', hc', hz', hkeep⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
