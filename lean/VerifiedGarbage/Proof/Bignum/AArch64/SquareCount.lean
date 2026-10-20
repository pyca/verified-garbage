module
public import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Public quotient and remainder counters for four-word square rows. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)

theorem shr2_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 2 = BitVec.ofNat 64 (n/4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self n 4) hn)]

theorem mask3_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& (3 : BitVec 64) = BitVec.ofNat 64 (n%4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and,
    show (3 : BitVec 64).toNat = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n%4 < 2 ^ 64 by omega)]

theorem shift_count_ok (s : State) (count : Reg) {n : Nat}
    (hcount : s.gpr count = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    WP isa (.block [.lsr .x .x14 count 2]) s fun t =>
      (t.mem = s.mem ∧ carry t = carry s ∧
        t.gpr .x14 = BitVec.ofNat 64 (n/4)) ∧ Keep [.x14] s t := by
  refine WP.keep [.x14] ?_ rfl rfl rfl
  unfold carry
  brun [hcount, shr2_ofNat hn]

theorem mask_count_ok (s : State) (count : Reg) {n : Nat}
    (hcount : s.gpr count = BitVec.ofNat 64 n) (hn : n < 2 ^ 64)
    (hC : count = .x12 ∨ count = .x13) :
    WP isa (.block [movi .x3 3, .logic .and .x .x14 count .x3]) s fun t =>
      (t.mem = s.mem ∧ carry t = carry s ∧
        t.gpr .x14 = BitVec.ofNat 64 (n%4)) ∧ Keep [.x3, .x14] s t := by
  rcases hC with rfl | rfl <;> refine WP.keep [.x3, .x14] ?_ rfl rfl rfl
  all_goals
    unfold carry
    brun [hcount]
    change BitVec.ofNat 64 n &&& (3 : BitVec 64) = BitVec.ofNat 64 (n%4)
    exact mask3_ofNat hn

end VG.Proof.Bignum.AArch64.Square
