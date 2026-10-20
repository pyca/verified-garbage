module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowFive
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtTab
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem digitMask (V shift : Nat) (hV : V < 2 ^ 64) :
    (BitVec.ofNat 64 V >>> shift &&& BitVec.setWidth 64 (31#16)) =
      BitVec.ofNat 64 (V / 2 ^ shift % 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hV, Nat.shiftRight_eq_div_pow,
    show (BitVec.setWidth 64 (31#16)).toNat = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

/-- The digit write preserves every other byte and every register outside
`x3` and `x4`, including the packed group itself. -/
theorem groupDigit_ok {t : State} {P : Addr} {wx : Nat} {mi : BitVec 64}
    {X Xc V shift : Nat} (hc : CExpCtx t P wx mi X Xc)
    (hV : word t.mem P (8 * Crt.sV) = BitVec.ofNat 64 V)
    (hV' : V < 2 ^ 64) (hshift : shift < 64) :
    WP isa (.block (VG.Impl.Rsa.AArch64.WindowFive.groupDigit shift)) t fun t' =>
      t'.mem = t.mem.writeW (off P (8 * Crt.sNib)) (BitVec.ofNat 64 (V / 2 ^ shift % 32)) ∧
      Keep [.x3, .x4] t t' := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [VG.Impl.Rsa.AArch64.WindowFive.groupDigit, hc.good.x0,
    hdr_enc (show Crt.sV < 32 by decide), hdr_enc (show Crt.sNib < 32 by decide),
    hc.ld (i := Crt.sV) (by decide), hc.st (i := Crt.sNib) (by decide),
    hV, hshift, digitMask V shift hV']

/-- Neither the packed group nor the extracted digit influences addresses
or control flow. The shift is fixed by the caller's code. -/
theorem groupDigit_ct (shift : Nat) :
    RelCT isa (Two fun (P : Addr) s => s.gpr .x0 = P)
      (.block (VG.Impl.Rsa.AArch64.WindowFive.groupDigit shift)) (fun _ _ => True) := by
  apply two_taint [.x0] (hc := .block [])
  · intro P s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm
  · rfl

end VG.Proof.Bignum.AArch64.WindowFive
