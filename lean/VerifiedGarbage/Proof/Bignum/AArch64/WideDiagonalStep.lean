module

import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalCore
import VerifiedGarbage.Impl.Bignum.AArch64.WideLoops
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal

/-! Execution and frame of one diagonal-square pair. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.WideLoops
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.Square
open VG.Proof.MlKem.AArch64 (Keep)

def diagonalHead (i : Nat) : List Instr :=
 [ld .x1 .x11 (8*i), .mul .x .x2 .x1 .x1, .umulh .x1 .x1 .x1,
  ld .x3 .x16 (16*i), ld .x4 .x16 (16*i+8)]

def diagonalTail (i : Nat) : List Instr := [st .x3 .x16 (16*i), st .x4 .x16 (16*i+8)]

theorem diagonalHead_ok {s : State} {B : Addr} {Z e ea i : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (h11 : s.gpr .x11 = off B ea) (he : e+16*i+16 ≤ Z) (hi : i < 4) (ha : ea+8*i+8 ≤ Z) :
    WP isa (.block (diagonalHead i)) s fun t =>
      (t.gpr .x1 = BitVec.ofNat 64 ((word s.mem B (ea+8*i)).toNat*(word s.mem B (ea+8*i)).toNat / 2 ^ 64) ∧
       t.gpr .x2 = word s.mem B (ea+8*i) * word s.mem B (ea+8*i) ∧
       t.gpr .x3 = word s.mem B (e+16*i) ∧ t.gpr .x4 = word s.mem B (e+16*i+8) ∧ t.mem = s.mem) ∧
      Keep [.x1, .x2, .x3, .x4] s t := by
  refine WP.keep [.x1, .x2, .x3, .x4] ?_ rfl rfl rfl
  unfold diagonalHead
  have enc : (8*i) % 8 = 0 ∧ 8*i < 32768 ∧ (16*i) % 8 = 0 ∧ 16*i < 32768 ∧ (16*i+8) % 8 = 0 ∧ 16*i+8 < 32768 := by omega
  brun [h16, h11, enc, hs.ld ha, hs.ld (show e+16*i+8 ≤ Z by omega), hs.ld (show e+(16*i+8)+8 ≤ Z by omega), Nat.add_assoc]

theorem diagonalTail_ok {s : State} {B : Addr} {Z e i : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (he : e+16*i+16 ≤ Z) (hi : i < 4) :
    WP isa (.block (diagonalTail i)) s fun t =>
      (t.mem = (s.mem.writeW (off B (e+16*i)) (s.gpr .x3)).writeW (off B (e+16*i+8)) (s.gpr .x4)) ∧ Keep [] s t := by
  refine WP.keep [] ?_ rfl rfl rfl
  unfold diagonalTail
  have enc : (16*i) % 8 = 0 ∧ 16*i < 32768 ∧ (16*i+8) % 8 = 0 ∧ 16*i+8 < 32768 := by omega
  brun [h16, enc, hs.st (show e+16*i+8 ≤ Z by omega), hs.st (show e+(16*i+8)+8 ≤ Z by omega), Nat.add_assoc]

theorem diagonalStep_ok {s : State} {B : Addr} {Z e ea i : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (h11 : s.gpr .x11 = off B ea) (h7 : s.gpr .x7 = 0)
    (he : e+16*i+16 ≤ Z) (hi : i < 4) (ha : ea+8*i+8 ≤ Z) :
    WP isa (.block (VG.Impl.Bignum.AArch64.WideLoops.step i)) s fun t =>
      (∃ lo hi : BitVec 64,
        t.mem = (s.mem.writeW (off B (e+16*i)) lo).writeW (off B (e+16*i+8)) hi ∧
        lo.toNat + 2 ^ 64 * hi.toNat + 2 ^ 128 * (t.gpr .x5).toNat =
          2*((word s.mem B (e+16*i)).toNat + 2 ^ 64*(word s.mem B (e+16*i+8)).toNat) +
          (word s.mem B (ea+8*i)).toNat*(word s.mem B (ea+8*i)).toNat + (s.gpr .x5).toNat ∧
        (t.gpr .x5).toNat ≤ 3) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6] s t := by
  change WP isa (.block (diagonalHead i ++ VG.Impl.Bignum.AArch64.Square.diagonalCore ++ diagonalTail i)) s _
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (diagonalHead_ok hs h16 h11 he hi ha) fun u ⟨⟨h1, h2, h3, h4, hm⟩, k1⟩ => ?_
  have u7 := (k1.gpr .x7 (by decide)).trans h7
  refine WP.mono (diagonalCore_ok u u7) fun v ⟨⟨hv, hc, vm0⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have v16 := (k12.gpr .x16 (by decide)).trans h16
  refine WP.mono (diagonalTail_ok (hs.congr k12.wr) v16 he hi)
    fun t ⟨htm, kt⟩ => ?_
  have vm : v.mem = s.mem := vm0.trans hm
  have t5 : t.gpr .x5 = v.gpr .x5 := kt.gpr .x5 (by decide)
  refine ⟨⟨v.gpr .x3, v.gpr .x4, ?_, ?_, ?_⟩, (k12.trans kt).mono (by decide)⟩
  · rw [htm, vm]
  · rw [t5]
    rw [h1, h2, h3, h4, k1.gpr .x5 (by decide)] at hv
    have hp := square_halves (word s.mem B (ea+8*i))
    omega_arith
  · rw [t5]; exact hc

end VG.Proof.Bignum.AArch64.WideLoops
