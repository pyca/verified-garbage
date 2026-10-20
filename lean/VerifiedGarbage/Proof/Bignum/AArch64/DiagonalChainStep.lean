module

import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonal

import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainCore
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Impl.Bignum.AArch64.DiagonalChain
public import VerifiedGarbage.Proof.Bignum.AArch64.DiagonalChainMath
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Execution and frame of one diagonal-square pair. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.DiagonalChain
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.Bignum.AArch64.Square
open VG.Proof.MlKem.AArch64 (Keep)

def diagonalHead (i : Nat) : List Instr :=
 [ld .x1 .x11 (8*i), .mul .x .x2 .x1 .x1, .umulh .x1 .x1 .x1,
  ld .x3 .x16 (16*i), ld .x4 .x16 (16*i+8)]

def diagonalTail (i : Nat) : List Instr := [st .x3 .x16 (16*i), st .x6 .x16 (16*i+8)]

theorem diagonalHead_ok {s : State} {B : Addr} {Z e ea i : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (h11 : s.gpr .x11 = off B ea) (he : e+16*i+16 ≤ Z) (hi : i < 4) (ha : ea+8*i+8 ≤ Z) :
    WP isa (.block (diagonalHead i)) s fun t =>
      (t.gpr .x1 = BitVec.ofNat 64 ((word s.mem B (ea+8*i)).toNat*(word s.mem B (ea+8*i)).toNat / 2 ^ 64) ∧
       t.gpr .x2 = word s.mem B (ea+8*i) * word s.mem B (ea+8*i) ∧
       t.gpr .x3 = word s.mem B (e+16*i) ∧ t.gpr .x4 = word s.mem B (e+16*i+8) ∧ t.mem = s.mem ∧ t.c = s.c) ∧
      Keep [.x1, .x2, .x3, .x4] s t := by
  refine WP.keep [.x1, .x2, .x3, .x4] ?_ rfl rfl rfl
  unfold diagonalHead
  have enc : (8*i) % 8 = 0 ∧ 8*i < 32768 ∧ (16*i) % 8 = 0 ∧ 16*i < 32768 ∧ (16*i+8) % 8 = 0 ∧ 16*i+8 < 32768 := by omega
  brun [h16, h11, enc, hs.ld ha, hs.ld (show e+16*i+8 ≤ Z by omega), hs.ld (show e+(16*i+8)+8 ≤ Z by omega), Nat.add_assoc]

theorem diagonalTail_ok {s : State} {B : Addr} {Z e i : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (he : e+16*i+16 ≤ Z) (hi : i < 4) :
    WP isa (.block (diagonalTail i)) s fun t =>
      (t.mem = (s.mem.writeW (off B (e+16*i)) (s.gpr .x3)).writeW (off B (e+16*i+8)) (s.gpr .x6) ∧ t.c = s.c) ∧ Keep [] s t := by
  refine WP.keep [] ?_ rfl rfl rfl
  unfold diagonalTail
  have enc : (16*i) % 8 = 0 ∧ 16*i < 32768 ∧ (16*i+8) % 8 = 0 ∧ 16*i+8 < 32768 := by omega
  brun [h16, enc, hs.st (show e+16*i+8 ≤ Z by omega), hs.st (show e+(16*i+8)+8 ≤ Z by omega), Nat.add_assoc]

theorem diagonalStep_ok {s : State} {B : Addr} {Z e ea i : Nat}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B e)
    (h11 : s.gpr .x11 = off B ea) (_h7 : s.gpr .x7 = 0)
    (he : e+16*i+16 ≤ Z) (hi : i < 4) (ha : ea+8*i+8 ≤ Z) :
    WP isa (.block (VG.Impl.Bignum.AArch64.DiagonalChain.step i)) s fun t =>
      (∃ lo hi : BitVec 64,
        t.mem = (s.mem.writeW (off B (e+16*i)) lo).writeW (off B (e+16*i+8)) hi ∧
        lo.toNat + 2 ^ 64 * hi.toNat + 2 ^ 128 * carry t =
          2*((word s.mem B (e+16*i)).toNat + 2 ^ 64*(word s.mem B (e+16*i+8)).toNat) +
          (word s.mem B (ea+8*i)).toNat*(word s.mem B (ea+8*i)).toNat + carry s ∧
        carry t ≤ 3) ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6] s t := by
  change WP isa (.block (diagonalHead i ++ VG.Impl.Bignum.AArch64.DiagonalChain.core ++ diagonalTail i)) s _
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (diagonalHead_ok hs h16 h11 he hi ha) fun u ⟨⟨h1, h2, h3, h4, hm, huc⟩, k1⟩ => ?_
  refine WP.mono (core_ok u) fun v ⟨⟨hv, vm0⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have v16 := (k12.gpr .x16 (by decide)).trans h16
  refine WP.mono (diagonalTail_ok (hs.congr k12.wr) v16 he hi)
    fun t ⟨⟨htm, htc⟩, kt⟩ => ?_
  have vm : v.mem = s.mem := vm0.trans hm
  have tc : carry t = carry v := by unfold carry; rw [kt.gpr .x5 (by decide), htc]
  have uc : carry u = carry s := by unfold carry; rw [k1.gpr .x5 (by decide), huc]
  refine ⟨⟨v.gpr .x3, v.gpr .x6, ?_, ?_, ?_⟩, (k12.trans kt).mono (by decide)⟩
  · rw [htm, vm]
  · rw [tc]
    rw [h1, h2, h3, h4, uc] at hv
    have hp := square_halves (word s.mem B (ea+8*i))
    omega_arith
  · rw [tc]; have h := carry_bound v; omega

end VG.Proof.Bignum.AArch64.DiagonalChain
