module
public import VerifiedGarbage.Impl.Bignum.AArch64.SquareEightRaw
public import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRows

import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightSetup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightFinish
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowSparse
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.ProductEight (productBase)

open VG.Proof.Bignum.AArch64.SquareEight

abbrev rowTailRegs : List Reg := [.x13, .x16, .x17, .x8, .x12]

theorem rowTail_ok {s : State} {B : Addr} {Z k i a : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (h7 : s.gpr .x7 = 0)
    (hH : Hdr s.mem B (8*k) minv) (hZ : slot (8*k) 8 ≤ Z) (ha : a < 8)
    (hk : k < 2 ^ 56) (hi : i < k) (h8 : s.gpr .x8 = off B (slot (8*k) a+64*i)) :
    WP isa (.block (SquareEightRaw.rowTail a)) s fun t =>
      wv t.mem B (productBase k) (16*(i+1)) + 2 ^ (64*(16*i+15))*t.c.toNat =
        wv s.mem B (productBase k) (16*(i+1)) + 2 ^ (64*(16*i+8))*(s.gpr .x10).toNat ∧
      t.gpr .x8 = off B (slot (8*k) a+64*(i+1)) ∧ t.gpr .x12 = s.gpr .x12 - BitVec.ofNat 64 1 ∧
      Outside B (productBase k) (8*(16*(i+1))) s.mem t.mem ∧ Keep rowTailRegs s t := by
  have hP : productBase k+8*(16*(i+1)) ≤ Z := by
    unfold productBase slot Public.aAcc at *
    omega
  unfold SquareEightRaw.rowTail
  rw [List.append_assoc]
  apply WP.block_append
  refine WP.mono (outputPtr_ok hs h0 hH hZ ha (by omega) h8 true) fun u ⟨⟨hu16, _, hum⟩, ku⟩ => ?_
  apply WP.block_append
  refine WP.mono (finishCarry_full (hs.congr ku.wr) hu16 ((ku.gpr _ (by decide)).trans h7)
    hP (by omega)) fun v ⟨hvv, hvo, kv⟩ => ?_
  have huv := ku.trans kv
  have hp := ProductEight.rowEnd_ok ((huv.gpr _ (by decide)).trans h8)
  refine WP.mono (WP.keep [.x8, .x12] (Q := fun t =>
      t.gpr .x8 = off B (slot (8*k) a+64*i+64) ∧ t.gpr .x12 = v.gpr .x12 - BitVec.ofNat 64 1 ∧
        t.mem = v.mem ∧ t.c = v.c)
    (by brun [(huv.gpr .x8 (by decide)).trans h8]) rfl rfl rfl)
    fun t ⟨⟨ht8, ht12, htm, htc⟩, kt⟩ => ?_
  refine ⟨?_, ht8.trans (congrArg (off B) (by omega)),
    ht12.trans (congrArg (· - BitVec.ofNat 64 1) (huv.gpr _ (by decide))), ?_,
    (huv.trans kt).mono (by decide)⟩
  · rw [htm, htc]
    simpa only [hum, ku.gpr .x10 (by decide)] using hvv
  · intro x hx
    exact (congrArg (fun m : Mem => m x) htm).trans
      (((hvo.mono (by omega) (by omega)) x hx).trans (congrArg (fun m : Mem => m x) hum))

end VG.Proof.Bignum.AArch64.WindowSparse
