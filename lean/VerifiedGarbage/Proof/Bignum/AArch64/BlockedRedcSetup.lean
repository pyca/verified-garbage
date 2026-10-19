module
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Ed25519.Word64

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

theorem shr3_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hn, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self n 8) hn)]

def columnSetup : List Instr :=
  [.addImm .x .x16 .x8 64, .addImm .x .x17 .x17 64,
    ldh .x15 sW, .lsr .x .x15 .x15 3, .subImm .x .x15 .x15 1]

theorem columnSetup_ok {s : State} {B : Addr} {Z eQ eN k : Nat}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h8 : s.gpr .x8 = off B eQ)
    (h17 : s.gpr .x17 = off B eN) (hZ : 256 ≤ Z)
    (hw : word s.mem B (8 * sW) = BitVec.ofNat 64 (8 * k))
    (hk : 2 ≤ k) (hk' : 8 * k < 2 ^ 64) :
    WP isa (.block columnSetup) s fun t =>
      (t.gpr .x16 = off B (eQ + 64) ∧ t.gpr .x17 = off B (eN + 64) ∧
        t.gpr .x15 = BitVec.ofNat 64 (k - 1) ∧ t.mem = s.mem) ∧
      Keep [.x16, .x17, .x15] s t := by
  have hd : 8 * k / 8 = k := by omega
  have hsub : BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)
  refine WP.keep [.x16, .x17, .x15] ?_ rfl rfl rfl
  brun [columnSetup, h0, h8, h17, hw, hd, shr3_ofNat hk', hsub,
    hs.ld (show 8 * sW + 8 ≤ Z by unfold sW; omega)]

theorem advanceRow_ok {s : State} {B : Addr} {eQ : Nat}
    (h8 : s.gpr .x8 = off B eQ) :
    WP isa (.block [.addImm .x .x8 .x8 64, .subImm .x .x12 .x12 1]) s fun t =>
      (t.gpr .x8 = off B (eQ + 64) ∧ t.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1 ∧
        t.mem = s.mem) ∧ Keep [.x8, .x12] s t := by
  refine WP.keep [.x8, .x12] ?_ rfl rfl rfl
  brun [h8]

theorem redcInit_ok {s : State} {k : Nat}
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (8 * k)) (hk : 8 * k < 2 ^ 64) :
    WP isa (.block [.lsr .x .x12 .x12 3, movi .x10 0]) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 k ∧ t.gpr .x10 = 0 ∧ t.mem = s.mem) ∧
      Keep [.x12, .x10] s t := by
  have hd : 8 * k / 8 = k := by omega
  refine WP.keep [.x12, .x10] ?_ rfl rfl rfl
  brun [h12, shr3_ofNat hk, hd]

end VG.Proof.Bignum.AArch64.BlockedRedc
