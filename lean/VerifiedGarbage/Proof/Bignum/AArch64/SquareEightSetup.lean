module

public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.SquareEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem double_offset {i : Nat} (hi : i < 2 ^ 56) :
    BitVec.ofNat 64 (64*i) <<< 1 = BitVec.ofNat 64 (128*i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show 64*i < 2 ^ 64 by omega), BitVec.toNat_ofNat]
  congr 1
  omega

theorem outputPtr_ok {s : State} {B : Addr} {Z k i a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8*k) minv)
    (hZ : slot (8*k) 8 ≤ Z) (ha : a < 8) (hi : i < 2 ^ 56)
    (h8 : s.gpr .x8 = off B (slot (8*k) a + 64*i)) (twice : Bool) :
    WP isa (.block (ProductEight.outputPtr twice a)) s fun t =>
      (t.gpr .x16 = off B (ProductEight.productBase k + (if twice then 128*i else 64*i)) ∧
       t.gpr .x17 = off B (slot (8*k) a) ∧ t.mem = s.mem) ∧ Keep [.x13, .x16, .x17] s t := by
  have hl : ∀ j < 32, InRegions (s.rd ++ s.wr) (off B (8*j)) 8 :=
    fun j hj => hs.ld (by have := hdr_lt_slot (8*k) 8 hj; omega)
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  cases twice
  all_goals
    refine WP.keep [.x13, .x16, .x17] ?_ rfl rfl rfl
    unfold VG.Impl.Bignum.AArch64.ProductEight.outputPtr
    brun [h0, h8, hdr_enc (sa a ha), hl _ (sa a ha), hl _ (sa Public.aAcc (by decide)),
      hH.harr a ha, hH.harr Public.aAcc (by decide), ProductEight.offset_difference, double_offset hi]
    simp only [ProductEight.productBase, off, BitVec.ofNat_add]
    ac_rfl

theorem clearPending_ok (s : State) :
    WP isa (.block [movi .x10 0]) s fun t =>
      (t.gpr .x10 = 0 ∧ t.mem = s.mem) ∧ Keep [.x10] s t := by
  refine WP.keep [.x10] ?_ rfl rfl rfl
  brun []

theorem rowCount_ok {s : State} {B : Addr} {Z k i : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8*k) minv)
    (hZ : slot (8*k) 8 ≤ Z) (hk : k < 2 ^ 56) (hi : i ≤ k)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (k-i)) :
    WP isa (.block [ldh .x15 sW, .lsr .x .x15 .x15 3, .sub .x .x15 .x15 .x12]) s fun t =>
      (t.gpr .x15 = BitVec.ofNat 64 i ∧ t.mem = s.mem) ∧ Keep [.x15] s t := by
  have hd : 8*k/8 = k := by omega
  have hsub : BitVec.ofNat 64 k - BitVec.ofNat 64 (k-i) = BitVec.ofNat 64 i :=
    (BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)).trans
      (congrArg (BitVec.ofNat 64) (by omega))
  refine WP.keep [.x15] ?_ rfl rfl rfl
  brun [h0, h12, hH.hw, Square.shr3_ofNat (show 8*k < 2 ^ 64 by omega), hd, hsub,
    hs.ld (show 8*sW+8 ≤ Z by have := hdr_lt_slot (8*k) 8 (show sW < 32 by decide); omega)]

end VG.Proof.Bignum.AArch64.SquareEight
