module

import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Execution and frame of one diagonal-square pair. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem diagonalHead_ok {s : State} {B : Addr} {Z e ea : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (h11 : s.gpr .x11 = off B ea) (he : e+16 ≤ Z) (ha : ea+8 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.Square.diagonalHead) s fun t =>
      (t.gpr .x1 = BitVec.ofNat 64 ((word s.mem B ea).toNat*(word s.mem B ea).toNat / 2 ^ 64) ∧
       t.gpr .x2 = word s.mem B ea * word s.mem B ea ∧
       t.gpr .x3 = word s.mem B e ∧ t.gpr .x4 = word s.mem B (e+8) ∧ t.mem = s.mem) ∧
      Keep [.x1, .x2, .x3, .x4] s t := by
  refine WP.keep [.x1, .x2, .x3, .x4] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.Square.diagonalHead
  brun [h16, h11, hs.ld ha, hs.ld (show e+8 ≤ Z by omega), hs.ld he]

theorem diagonalTail_ok {s : State} {B : Addr} {Z e ea : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (h11 : s.gpr .x11 = off B ea) (he : e+16 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.Square.diagonalTail) s fun t =>
      (t.mem = (s.mem.writeW (off B e) (s.gpr .x3)).writeW (off B (e+8)) (s.gpr .x4) ∧
       t.gpr .x16 = off B (e+16) ∧ t.gpr .x11 = off B (ea+8)) ∧ Keep [.x16, .x11] s t := by
  refine WP.keep [.x16, .x11] ?_ rfl rfl rfl
  unfold VG.Impl.Bignum.AArch64.Square.diagonalTail
  brun [h16, h11, hs.st (show e+8 ≤ Z by omega), hs.st he]

theorem diagonalStep_ok {s : State} {B : Addr} {Z e ea : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (h11 : s.gpr .x11 = off B ea) (h7 : s.gpr .x7 = 0)
    (he : e+16 ≤ Z) (ha : ea+8 ≤ Z) :
    WP isa (.block VG.Impl.Bignum.AArch64.Square.diagonalStep) s fun t =>
      (∃ lo hi : BitVec 64,
        t.mem = (s.mem.writeW (off B e) lo).writeW (off B (e+8)) hi ∧
        lo.toNat + 2 ^ 64 * hi.toNat + 2 ^ 128 * (t.gpr .x5).toNat =
          2*((word s.mem B e).toNat + 2 ^ 64*(word s.mem B (e+8)).toNat) +
          (word s.mem B ea).toNat*(word s.mem B ea).toNat + (s.gpr .x5).toNat ∧
        (t.gpr .x5).toNat ≤ 3 ∧ t.gpr .x16 = off B (e+16) ∧
        t.gpr .x11 = off B (ea+8)) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x16, .x11] s t := by
  unfold VG.Impl.Bignum.AArch64.Square.diagonalStep
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (diagonalHead_ok hs h16 h11 he ha) fun u ⟨⟨h1, h2, h3, h4, hm⟩, k1⟩ => ?_
  have u7 := (k1.gpr .x7 (by decide)).trans h7
  refine WP.mono (diagonalCore_ok u u7) fun v ⟨⟨hv, hc, vm0⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have v16 := (k12.gpr .x16 (by decide)).trans h16
  have v11 := (k12.gpr .x11 (by decide)).trans h11
  refine WP.mono (diagonalTail_ok (hs.congr k12.wr) v16 v11 he)
    fun t ⟨⟨htm, ht16, ht11⟩, kt⟩ => ?_
  have vm : v.mem = s.mem := vm0.trans hm
  have t5 : t.gpr .x5 = v.gpr .x5 := kt.gpr .x5 (by decide)
  refine ⟨⟨v.gpr .x3, v.gpr .x4, ?_, ?_, ?_, ht16, ht11⟩, (k12.trans kt).mono (by decide)⟩
  · rw [htm, vm]
  · rw [t5]
    rw [h1, h2, h3, h4, k1.gpr .x5 (by decide)] at hv
    have hp := square_halves (word s.mem B ea)
    omega_arith
  · rw [t5]; exact hc

end VG.Proof.Bignum.AArch64.Square
