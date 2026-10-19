module
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Zeroing the padded nonce, with an exact memory frame. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def randomClearMem (m : Mem) (B : Addr) : Mem :=
  (((m.writeW (off B 200) (0 : BitVec 64)).writeW (off B 208) (0 : BitVec 64)).writeW
    (off B 216) (0 : BitVec 64)).writeW (off B 224) (0 : BitVec 64)

theorem random_clear_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block Random.clearNonce) s fun t =>
      t.mem = randomClearMem s.mem B ∧ Keep [.x0, .x15] s t := by
  refine WP.keep [.x0, .x15] (Q := fun t => t.mem = randomClearMem s.mem B) ?_ rfl rfl rfl
  unfold Random.clearNonce Random.store randomClearMem
  brun [Random.oNonce, exec_addSp (show 200 < 4096 by decide),
    exec_addSp (show 208 < 4096 by decide), exec_addSp (show 216 < 4096 by decide),
    exec_addSp (show 224 < 4096 by decide), hsp,
    hs.st (d := 200) (by decide), hs.st (d := 208) (by decide),
    hs.st (d := 216) (by decide), hs.st (d := 224) (by decide)]
  rfl

theorem random_clear_outside (m : Mem) (B : Addr) : Outside B 200 32 m (randomClearMem m B) := by
  have h0 := (writeW_outside m B (d := 200) (0 : BitVec 64) (by decide)).mono
    (o' := 200) (n' := 32) (by decide) (by decide)
  have h1 := (writeW_outside (m.writeW (off B 200) (0 : BitVec 64)) B (d := 208) (0 : BitVec 64)
    (by decide)).mono (o' := 200) (n' := 32) (by decide) (by decide)
  have h2 := (writeW_outside ((m.writeW (off B 200) (0 : BitVec 64)).writeW (off B 208) (0 : BitVec 64)) B
    (d := 216) (0 : BitVec 64) (by decide)).mono (o' := 200) (n' := 32) (by decide) (by decide)
  have h3 := (writeW_outside (((m.writeW (off B 200) (0 : BitVec 64)).writeW (off B 208) (0 : BitVec 64)).writeW
    (off B 216) (0 : BitVec 64)) B (d := 224) (0 : BitVec 64) (by decide)).mono
    (o' := 200) (n' := 32) (by decide) (by decide)
  exact ((h0.trans h1).trans h2).trans h3

private theorem zeroWord_at (m : Mem) (B : Addr) (d i : Nat) (hi : i < 8) :
    (m.writeW (off B d) (0 : BitVec 64)) (off B (d + i)) = 0 := by
  have he : off B (d + i) = off B d + BitVec.ofNat 64 i := by
    simp only [off, BitVec.ofNat_add, BitVec.add_assoc]
  rw [he]
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, Mem.sub_ofNat_toNat (off B d) (i := i) (by omega),
    show 64 / 8 = 8 from rfl, hi, ite_true]
  exact BitVec.extractLsb'_zero

theorem random_clear_byte (m : Mem) (B : Addr) (i : Nat) (hi : i < 32) :
    randomClearMem m B (off B (200 + i)) = 0 := by
  unfold randomClearMem
  by_cases h24 : 24 ≤ i
  · rw [show 200 + i = 224 + (i - 24) by omega]
    exact zeroWord_at _ B 224 (i - 24) (by omega)
  · rw [(writeW_outside _ B (d := 224) (0 : BitVec 64) (by decide)) _ (by
      rw [show off B (200 + i) = off B (200 + i) + BitVec.ofNat 64 0 by simp,
        ofs_off B (by omega)]; omega)]
    by_cases h16 : 16 ≤ i
    · rw [show 200 + i = 216 + (i - 16) by omega]
      exact zeroWord_at _ B 216 (i - 16) (by omega)
    · rw [(writeW_outside _ B (d := 216) (0 : BitVec 64) (by decide)) _ (by
        rw [show off B (200 + i) = off B (200 + i) + BitVec.ofNat 64 0 by simp,
          ofs_off B (by omega)]; omega)]
      by_cases h8 : 8 ≤ i
      · rw [show 200 + i = 208 + (i - 8) by omega]
        exact zeroWord_at _ B 208 (i - 8) (by omega)
      · rw [(writeW_outside _ B (d := 208) (0 : BitVec 64) (by decide)) _ (by
          rw [show off B (200 + i) = off B (200 + i) + BitVec.ofNat 64 0 by simp,
            ofs_off B (by omega)]; omega)]
        exact zeroWord_at m B 200 i (by omega)

end VG.Proof.Dsa.AArch64
