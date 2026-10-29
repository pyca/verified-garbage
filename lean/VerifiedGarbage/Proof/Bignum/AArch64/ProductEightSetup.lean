module
public import VerifiedGarbage.Impl.Bignum.AArch64.ProductEight
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout

import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.ProductEight
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Subtracting the input base recovers the public tile offset. -/
theorem offset_difference (B : Addr) (e j : Nat) :
    off B (e + 64 * j) - off B e = BitVec.ofNat 64 (64 * j) := by
  simp only [off, BitVec.ofNat_add]
  rw [← BitVec.add_assoc, BitVec.add_comm (B + BitVec.ofNat 64 e), BitVec.add_sub_cancel]

theorem rowSetup_ok {s : State} {B : Addr} {Z k i a b : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8 * k) minv)
    (hZ : slot (8 * k) 8 ≤ Z) (ha : a < 8) (hb : b < 8)
    (hk : k < 2 ^ 56) (h8 : s.gpr .x8 = off B (slot (8 * k) a + 64 * i)) :
    WP isa (.block (VG.Impl.Bignum.AArch64.ProductEight.rowSetup a b)) s fun t =>
      (t.gpr .x16 = off B (slot (8 * k) Public.aAcc + 16 + 64 * i) ∧
       t.gpr .x17 = off B (slot (8 * k) b) ∧ t.gpr .x15 = BitVec.ofNat 64 k ∧
       t.gpr .x10 = 0 ∧ t.mem = s.mem) ∧ Keep [.x13, .x16, .x17, .x15, .x10] s t := by
  have hl : ∀ j < 32, InRegions (s.rd ++ s.wr) (off B (8 * j)) 8 :=
    fun j hj => hs.ld (by have := hdr_lt_slot (8 * k) 8 hj; omega)
  have sa : ∀ j < 8, sArr j < 32 := fun j hj => by unfold sArr; omega
  refine WP.keep [.x13, .x16, .x17, .x15, .x10] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.ProductEight.rowSetup VG.Impl.Bignum.AArch64.ProductEight.outputPtr
  brun [h0, h8, hdr_enc (sa a ha), hdr_enc (sa b hb),
    hl _ (sa a ha), hl _ (sa b hb), hl _ (sa Public.aAcc (by decide)), hl sW (by decide),
    hH.harr a ha, hH.harr b hb, hH.harr Public.aAcc (by decide), hH.hw,
    offset_difference, Square.shr3_ofNat (show 8 * k < 2 ^ 64 by omega)]
  constructor
  · simp only [off, BitVec.ofNat_add]
    ac_rfl
  · congr 1
    omega

theorem start_ok {s : State} {B : Addr} {Z k a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hH : Hdr s.mem B (8 * k) minv)
    (hZ : slot (8 * k) 8 ≤ Z) (ha : a < 8) (hk : k < 2 ^ 56)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 (8 * k)) :
    WP isa (.block [ldh .x8 (sArr a), .lsr .x .x12 .x12 3]) s fun t =>
      (t.gpr .x8 = off B (slot (8 * k) a) ∧ t.gpr .x12 = BitVec.ofNat 64 k ∧
        t.mem = s.mem ∧ ∀ v, t.v v = s.v v) ∧ Keep [.x8, .x12] s t := by
  have ha' : sArr a < 32 := by unfold sArr; omega
  refine WP.keep [.x8, .x12] ?_ rfl rfl rfl
  brun [h0, h12, hdr_enc ha', hs.ld (show 8 * sArr a + 8 ≤ Z by
    have := hdr_lt_slot (8 * k) 8 ha'; omega), hH.harr a ha,
    Square.shr3_ofNat (show 8 * k < 2 ^ 64 by omega)]
  constructor
  · congr 1
    omega
  · intro v
    rfl

end VG.Proof.Bignum.AArch64.ProductEight
