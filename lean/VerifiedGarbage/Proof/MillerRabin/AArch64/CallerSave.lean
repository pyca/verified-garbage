module

public import VerifiedGarbage.Impl.MillerRabin.AArch64.Caller
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Save the prepared round caller in Montgomery-one padding -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.MillerRabin.AArch64.Caller VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def pad (w : Nat) : Nat := slot w aOne + 8 * w

def savedMem (s : State) (B : Addr) (w : Nat) : Mem :=
  (s.mem.writeW (off B (pad w)) (s.gpr .x19)).writeW (off B (pad w + 8)) (s.gpr .x30)

theorem saved_outside (s : State) (B : Addr) (w : Nat) (hp : pad w + 16 ≤ 2 ^ 64) :
    Outside B (pad w) 16 s.mem (savedMem s B w) := by
  unfold savedMem
  apply Outside.trans
    ((writeW_outside s.mem B (s.gpr .x19) (d := pad w) (by omega_arith)).mono
      (by omega_arith) (by omega_arith))
  exact (writeW_outside _ B (s.gpr .x30) (d := pad w + 8) (by omega_arith)).mono
    (by omega_arith) (by omega_arith)

theorem save_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (h : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hw : w ≤ 128) :
    WP isa (.block save) s fun t =>
      t.mem = savedMem s B w ∧ t.gpr .x19 = B ∧
      t.gpr .x1 = BitVec.ofNat 64 (32 + 28 * (w + 2)) ∧
      Keep [.x1, .x2, .x3, .x4, .x19] s t := by
  have hl : ∀ j < 16, InRegions (s.rd ++ s.wr) (off B (8 * j)) 8 :=
    fun j hj => h.scr.ld (by have := hdr_lt_slot w 8 (by omega_arith : j < 32); omega_arith)
  have hp : pad w + 16 ≤ Z := by
    simp only [pad, slot, hdrBytes, aOne] at hZ ⊢
    omega_arith
  have hs0 : InRegions s.wr (off B (pad w)) 8 := h.scr.st (by omega_arith)
  have hs8 : InRegions s.wr (off B (pad w + 8)) 8 := h.scr.st (by omega_arith)
  have hshift : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 w * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * w)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have haddr : off B (slot w aOne) + BitVec.ofNat 64 (8 * w) = off B (pad w) := by
    rw [off, Offset.add_ofNat_add_ofNat]
    rfl
  have hnext : off B (pad w) + 8#64 = off B (pad w + 8) := by
    change off B (pad w) + BitVec.ofNat 64 8 = off B (pad w + 8)
    rw [off, Offset.add_ofNat_add_ofNat]
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x4, .x19]
    (Q := fun t => t.mem = savedMem s B w ∧ t.gpr .x19 = B ∧
      t.gpr .x1 = BitVec.ofNat 64 (32 + 28 * (w + 2))) ?_
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨hm, h19, h1⟩, hk⟩ => ⟨hm, h19, h1, hk⟩
  unfold save saveLoad saveTail
  brun [h.x0, hdr_enc (show sArr aOne < 32 by decide), hdr_enc (show sW < 32 by decide),
    hl (sArr aOne) (by decide), hl sW (by decide), h.hdr.harr aOne (by decide),
    h.hdr.hw, hshift, haddr, hnext, hs0, hs8, savedMem]
  have hSaved : word (savedMem s B w) B (8 * sW) = BitVec.ofNat 64 w := by
    rw [(saved_outside s B w (by have := h.scr.nowrap; omega_arith)).word
      (Or.inl (by simp only [pad, slot, hdrBytes, aOne, sW]; omega_arith)) (by simp only [sW]; decide)]
    exact h.hdr.hw
  change (word (savedMem s B w) B (8 * sW) + 2#64) * 28#64 + 32#64 =
    BitVec.ofNat 64 (32 + 28 * (w + 2))
  rw [hSaved]
  bv_omega_arith

end VG.Proof.MillerRabin.AArch64.Caller
