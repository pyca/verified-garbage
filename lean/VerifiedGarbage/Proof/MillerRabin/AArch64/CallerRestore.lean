module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSave
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Restore the prepared round's caller and its mask result -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.MillerRabin.AArch64.Caller VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.MlKem.AArch64 (Keep)

private theorem low_result {v : BitVec 64} {p : Bool}
    (h : (v.setWidth 32).toNat = if p then 1 else 0) :
    v.setWidth 32 = BitVec.ofNat 32 p.toNat := by
  apply BitVec.eq_of_toNat_eq
  cases p <;> simpa using h

private theorem negative_result (p : Bool) :
    0#64 - (BitVec.ofNat 32 p.toNat).setWidth 64 = mask p := by
  cases p <;> decide

theorem restore_ok {s : State} {B : Addr} {Z w : Nat} {p : Bool} {old19 lr : BitVec 64}
    (hs : Scr s B Z) (hZ : slot w 8 ≤ Z) (hw : w ≤ 128)
    (h19 : s.gpr .x19 = B)
    (hW : word s.mem B (8 * sW) = BitVec.ofNat 64 w)
    (hA : word s.mem B (8 * sArr aOne) = off B (slot w aOne))
    (hp : ((s.gpr .x0).setWidth 32).toNat = if p then 1 else 0)
    (hOld : word s.mem B (pad w) = old19) (hLr : word s.mem B (pad w + 8) = lr) :
    WP isa (.block restore) s fun t =>
      t.mem = s.mem.writeW (off B (8 * kFlag)) (mask p) ∧
      t.gpr .x0 = B ∧ t.gpr .x19 = old19 ∧ t.gpr .x30 = lr ∧
      Keep [.x0, .x2, .x3, .x4, .x19, .x30] s t := by
  have hpad : pad w + 16 ≤ Z := by
    simp only [pad, slot, hdrBytes, aOne] at hZ ⊢
    omega_arith
  have hl : ∀ j < 16, InRegions (s.rd ++ s.wr) (off B (8 * j)) 8 :=
    fun j hj => hs.ld (by have := hdr_lt_slot w 8 (by omega_arith : j < 32); omega_arith)
  have ht : InRegions s.wr (off B (8 * kFlag)) 8 :=
    hs.st (by have := hdr_lt_slot w 8 (show kFlag < 32 by decide); omega_arith)
  have h0 : InRegions (s.rd ++ s.wr) (off B (pad w)) 8 := hs.ld (by omega_arith)
  have h8 : InRegions (s.rd ++ s.wr) (off B (pad w + 8)) 8 := hs.ld (by omega_arith)
  have hlow := low_result hp
  have hstore (d : Nat) (hd : 8 * kFlag + 8 ≤ d) (hn : d + 8 ≤ 2 ^ 64) :
      word (s.mem.writeW (off B (8 * kFlag)) (mask p)) B d = word s.mem B d :=
    (writeW_outside s.mem B (mask p) (d := 8 * kFlag) (by decide)).word (Or.inr hd) hn
  have hmaskW : word (s.mem.writeW (off B (8 * kFlag)) (mask p)) B (8 * sW) = BitVec.ofNat 64 w := by
    rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
    exact hW
  have hmaskA : word (s.mem.writeW (off B (8 * kFlag)) (mask p)) B (8 * sArr aOne) = off B (slot w aOne) := by
    rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
    exact hA
  have hmask19 : word (s.mem.writeW (off B (8 * kFlag)) (mask p)) B (pad w) = old19 := by
    rw [hstore _ (by simp only [kFlag, kPlen, sFn, pad, slot, hdrBytes, aOne]; omega_arith)
      (by have := hs.nowrap; omega_arith)]
    exact hOld
  have hmaskLr : word (s.mem.writeW (off B (8 * kFlag)) (mask p)) B (pad w + 8) = lr := by
    rw [hstore _ (by simp only [kFlag, kPlen, sFn, pad, slot, hdrBytes, aOne]; omega_arith)
      (by have := hs.nowrap; omega_arith)]
    exact hLr
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
  refine WP.mono (WP.keep [.x0, .x2, .x3, .x4, .x19, .x30]
    (Q := fun t => t.mem = s.mem.writeW (off B (8 * kFlag)) (mask p) ∧
      t.gpr .x0 = B ∧ t.gpr .x19 = old19 ∧ t.gpr .x30 = lr) ?_
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨hm, hb, ho, hr⟩, hk⟩ => ⟨hm, hb, ho, hr, hk⟩
  unfold restore restoreHead restoreTail
  brun [VG.Proof.RsaKeyGen.AArch64.exec_addImm_w, BitVec.add_zero,
    show (0#16).setWidth 64 = 0#64 from rfl, h19, hlow, negative_result, hdr_enc (show kFlag < 32 by decide),
    hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aOne < 32 by decide), ht,
    hl sW (by decide), hl (sArr aOne) (by decide), hmaskW, hmaskA, hmask19, hmaskLr,
    hshift, haddr, hnext, h0, h8]

end VG.Proof.MillerRabin.AArch64.Caller
