module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The primes' width of `vg_rsa_crt_values` on AArch64

`nCalc`: `⌈max(p_len, q_len) / 8⌉` from the header slots `sPl` and `sQl`,
without a branch (`nmax_eq`), for `inverseAt` (`InvLaw.inverseAt_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The branchless `⌈max(a, b) / 8⌉` of `nCalc`. -/
theorem nmax_eq {la lb : Nat} (hla : la < 2 ^ 62) (hlb : lb < 2 ^ 62) :
    (BitVec.ofNat 64 la - (BitVec.ofNat 64 la - BitVec.ofNat 64 lb &&&
      BitVec.setWidth 64 0#16 - (BitVec.ofNat 64 la - BitVec.ofNat 64 lb) >>> 63) + 7#64) >>> 3 =
      BitVec.ofNat 64 ((max la lb + 7) / 8) := by
  have z : BitVec.setWidth 64 0#16 = 0#64 := rfl
  rw [z]
  by_cases h : lb ≤ la
  · have e : (BitVec.ofNat 64 la - BitVec.ofNat 64 lb) >>> 63 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    rw [e, BitVec.sub_zero, BitVec.and_zero, BitVec.sub_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.max_eq_left h]
    omega
  · have e : (BitVec.ofNat 64 la - BitVec.ofNat 64 lb) >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    have m : 0#64 - 1#64 = BitVec.allOnes 64 := by decide
    rw [e, m, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.max_eq_right (by omega)]
    omega

/-- A value of `l ≤ max(a, b)` bytes fits in `⌈max(a, b) / 8⌉` words. -/
theorem fits_nmax {x l a b : Nat} (hx : x < 256 ^ l) (hl : l ≤ max a b) :
    x < 2 ^ (64 * ((max a b + 7) / 8)) := by
  have : 256 ^ l ≤ 2 ^ (64 * ((max a b + 7) / 8)) := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- `nCalc`: `⌈max(p_len, q_len) / 8⌉` from the header of `vg_rsa_crt_values`. -/
theorem nCalc_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hZ : 8 * 32 ≤ Z)
    {la lb : Nat} (hla : la < 2 ^ 62) (hlb : lb < 2 ^ 62)
    (wa : word s.mem B (8 * CrtValues.sPl) = BitVec.ofNat 64 la)
    (wb : word s.mem B (8 * CrtValues.sQl) = BitVec.ofNat 64 lb) :
    WP isa (.block (nCalc CrtValues.sPl CrtValues.sQl)) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 ((max la lb + 7) / 8) ∧ t.mem = s.mem ∧ t.v = s.v) ∧
        Keep [.x3, .x4, .x5, .x6, .x7, .x12] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  refine WP.keep [.x3, .x4, .x5, .x6, .x7, .x12] ?_ (by decide) (by decide) (by decide +kernel)
  unfold nCalc
  brun [h0, hl CrtValues.sPl (by decide), hl CrtValues.sQl (by decide), RegUpd.v_write]
  rw [show s.mem.readW (B + BitVec.ofNat 64 (8 * CrtValues.sPl)) 64 = BitVec.ofNat 64 la from wa,
    show s.mem.readW (B + BitVec.ofNat 64 (8 * CrtValues.sQl)) 64 = BitVec.ofNat 64 lb from wb]
  exact nmax_eq hla hlb

end VG.Proof.Rsa.AArch64
