import VerifiedGarbage.Proof.Bignum.X86_64.Exp

/-!
# Multiword arithmetic on x86-64: `vg_rsa_public`'s check of the modulus

`invalid` sets ZF iff the `k` bytes of `m` make a valid modulus
(`Spec.Rsa.modulusValid`), for `64 ≤ k ≤ 1024` (`invalid_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem ofInt_m1 : BitVec.ofInt 64 (-1) = -(1#64) := by decide

/-- The masks of borrows, or'ed. -/
theorem mask_or' (a b : Bool) : (0#64 - BitVec.setWidth 64 (BitVec.ofBool a)) |||
    (0#64 - BitVec.setWidth 64 (BitVec.ofBool b)) = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (a || b)) := by
  cases a <;> cases b <;> decide

theorem mask_beq (a : Bool) : (0#64 - BitVec.setWidth 64 (BitVec.ofBool a) == 0) = !a := by
  cases a <;> decide

theorem sw_toNat (b : Byte) : (BitVec.setWidth 64 b).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem sw_and1 (b : Byte) : (BitVec.setWidth 64 b &&& 1).toNat = b.toNat % 2 := by
  rw [BitVec.toNat_and, sw_toNat, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem sx64 : BitVec.signExtend 64 (64 : BitVec 32) = 64#64 := by decide
theorem sx128 : (BitVec.signExtend 64 (128 : BitVec 32)).toNat = 128 := by decide

theorem ror_k {k : Nat} (hk : 64 ≤ k) (hk' : k ≤ 1024) :
    ((BitVec.ofNat 64 k - 64#64).rotateRight 56).toNat = (k - 64) * 256 := by
  have e : BitVec.ofNat 64 k - 64#64 = BitVec.ofNat 64 (k - 64) := by
    rw [show (64#64) = BitVec.ofNat 64 64 from rfl, show k = (k - 64) + 64 by omega, ← BitVec.ofNat_add_ofNat, BitVec.add_sub_cancel, Nat.add_sub_cancel]
  rw [e, ror56_toNat _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

theorem invalid_ok {s : State} {np : Addr} {k : Nat} {nb : List Byte}
    (hdx : s.gpr .rdx = np) (hcx : s.gpr .rcx = BitVec.ofNat 64 k) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (np + BitVec.ofNat 64 i) 1)
    (hb : ∀ i (h : i < k), s.mem (np + BitVec.ofNat 64 i) = nb[i]'(by omega)) :
    WP isa (.block invalid) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k) ∧ t.mem = s.mem ∧
      Keep [.rax, .rbp, .rsi] s t := by
  refine WP.mono (WP.keep [.rax, .rbp, .rsi] (Q := fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  have hr0 : InRegions (s.rd ++ s.wr) np 1 := by have := hrd 0 (by omega); rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  have hb0 : s.mem np = nb[0]'(by omega) := by have := hb 0 (by omega); rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at this
  have hlast : np + BitVec.ofNat 64 k * BitVec.ofNat 64 1 + BitVec.ofInt 64 (-1) = np + BitVec.ofNat 64 (k - 1) := by
    have e : BitVec.ofNat 64 k = BitVec.ofNat 64 (k - 1) + 1#64 := by
      rw [show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]; congr 1; omega
    rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, e, ofInt_m1, ← BitVec.sub_eq_add_neg,
      ← BitVec.add_assoc, BitVec.add_sub_cancel]
  unfold invalid
  xrun [State.ea, at0, hdx, hcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hr0, hb0, hlast,
    hrd (k - 1) (by omega), hb (k - 1) (by omega)]
  have hn0 := (nb[0]'(by omega)).isLt
  rw [mask_or', mask_or', BitVec.and_self, mask_beq, modulusValid_iff hlen hk hk', sw_toNat, sw_and1,
    show BitVec.toNat (1 : BitVec 64) = 1 from rfl, sx64, sx128, BitVec.toNat_add, ror_k hk hk', sw_toNat, Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega)]

end VG.Proof.Bignum.X86_64
