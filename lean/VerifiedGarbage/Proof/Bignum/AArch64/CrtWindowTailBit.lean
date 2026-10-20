module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Impl.Rsa.AArch64.WindowTail
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! One tail bit extends a bounded pending digit. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (prepareBit)

theorem pendingDigit_value (v V shift : Nat) (hv : v < 16) (hV : V < 256) :
    ((BitVec.ofNat 64 v <<< 1) |||
      (BitVec.ofNat 64 V >>> shift &&& BitVec.setWidth 64 (1#16))) =
      BitVec.ofNat 64 (2 * v + V / 2 ^ shift % 2) := by
  have hb : V / 2 ^ shift % 2 < 2 := Nat.mod_lt _ (by decide)
  have hor : v * 2 ^ 1 ||| (V / 2 ^ shift % 2) = v * 2 ^ 1 + V / 2 ^ shift % 2 := by
    simpa only [Nat.shiftLeft_eq] using
      (Nat.shiftLeft_add_eq_or_of_lt (i := 1) hb v).symm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or,BitVec.toNat_shiftLeft,BitVec.toNat_and,BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show v < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show V < 2 ^ 64 by omega),Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show v * 2 ^ 1 < 2 ^ 64 by omega),
    show (BitVec.setWidth 64 (1#16)).toNat = 2 ^ 1 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod,hor,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 * v + V / 2 ^ shift % 2 < 2 ^ 64 by omega)]
  omega

theorem prepareBit_ok {s : State} {P : Addr} {w b v V i : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hi : i < 8) (hv : v < 16) (hV : V < 256)
    (hn : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v)
    (hcbit : word s.mem P (8 * Crt.sBit) = BitVec.ofNat 64 b)
    (hbyte : word s.mem P (8 * Crt.sV) = BitVec.ofNat 64 V) :
    WP isa (.block (prepareBit i)) s fun t =>
      (t.mem = (s.mem.writeW (off P (8 * Crt.sNib))
        (BitVec.ofNat 64 (2 * v + V / 2 ^ (7 - i) % 2))).writeW
        (off P (8 * Crt.sBit)) (BitVec.ofNat 64 (b + 1)) ∧
        t.gpr .x3 = BitVec.ofNat 64 (b + 1) - BitVec.ofNat 64 5) ∧ Keep [.x3,.x4,.x5] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [prepareBit,hc.good.x0,hdr_enc (show Crt.sNib < 32 by decide),
    hdr_enc (show Crt.sV < 32 by decide),hdr_enc (show Crt.sBit < 32 by decide),
    hc.ld (i := Crt.sNib) (by decide),hc.ld (i := Crt.sV) (by decide),
    hc.ld (i := Crt.sBit) (by decide),hc.st (i := Crt.sNib) (by decide),
    hc.st (i := Crt.sBit) (by decide),hn,hcbit,hbyte,show 7 - i < 64 by omega,
    pendingDigit_value v V (7 - i) hv hV,
    hdrStore_hdr _ _ _ (show Crt.sNib < 32 by decide) (show Crt.sBit < 32 by decide) (by decide),
    ofNat_add_ofNat]

/-- The decision to apply a window depends only on the public pending-bit count. -/
theorem pending_test {b : Nat} (hb : b < 5) :
    (BitVec.ofNat 64 (b + 1) - BitVec.ofNat 64 5 = 0) ↔ b = 4 := by
  bv_omega

theorem prepareBit_ct (i : Nat) :
    RelCT isa (Two fun (P : Addr) s => s.gpr .x0 = P)
      (.block (prepareBit i)) (fun _ _ => True) := by
  apply two_taint [.x0] (hc := .block [])
  · intro P s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.trans ht.symm
  · rfl

end VG.Proof.Bignum.AArch64.WindowFive
