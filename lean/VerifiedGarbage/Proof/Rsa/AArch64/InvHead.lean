module
-- separate module: a batch's divsteps build in parallel with its updates (`InvStage`)

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Divstep.BatchBasic
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.Rsa.AArch64.InvBase
import VerifiedGarbage.Proof.Weierstrass.AArch64.InvPacked
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# RSA private keys on AArch64: the start of a batch of divsteps

`batchHead f g` (`batchHead_ok`): `d` from lane 0 of `v18` and the low
words of `f` and `g`, the `59` packed divsteps of the Weierstrass inverse
(`Weierstrass.AArch64.pwords_ok`), and `d` and the matrix into the lanes of
`v18`, `v16`, `v17`. The divsteps leave only `x0`, `x14` and `x15`: the
stride and the width are packed into `x14` across them (`pack_unpack`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The stride and the width, packed into a word and back. -/
theorem pack_unpack (S N : Nat) (hS : S < 2 ^ 32) (hN : N < 2 ^ 32) :
    (BitVec.ofNat 64 S <<< 32 + BitVec.ofNat 64 N) >>> 32 = BitVec.ofNat 64 S ∧
    BitVec.ofNat 64 S <<< 32 + BitVec.ofNat 64 N - BitVec.ofNat 64 S <<< 32 = BitVec.ofNat 64 N := by
  refine ⟨?_, by rw [BitVec.add_comm, BitVec.add_sub_cancel]⟩
  rw [shl_ofNat (show S * 2 ^ 32 < 2 ^ 64 by omega), BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The batch head's tail: `d` and the matrix into lanes, `x11`, `x12` back, `x15` counted. -/
theorem headTail_ok' (s : State) {S N : Nat} (hS : S < 2 ^ 32) (hN : N < 2 ^ 32)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 S <<< 32 + BitVec.ofNat 64 N) :
    WP isa (.block (([.vop (.ins .d2 .v18 0 .x1), .vop (.ins .d2 .v16 0 .x4), .vop (.ins .d2 .v16 1 .x5),
      .vop (.ins .d2 .v17 0 .x6), .vop (.ins .d2 .v17 1 .x7)] : List Instr) ++ (unpackW ++ ([.subImm .x .x15 .x15 1] : List Instr)))) s
      fun t => (laneOf t .v18 0 = s.gpr .x1 ∧ laneOf t .v18 1 = laneOf s .v18 1 ∧ laneOf t .v16 0 = s.gpr .x4 ∧
        laneOf t .v16 1 = s.gpr .x5 ∧ laneOf t .v17 0 = s.gpr .x6 ∧ laneOf t .v17 1 = s.gpr .x7 ∧
        (∀ r, r ≠ .v16 → r ≠ .v17 → r ≠ .v18 → t.v r = s.v r) ∧ t.gpr .x11 = BitVec.ofNat 64 S ∧
        t.gpr .x12 = BitVec.ofNat 64 N ∧ t.gpr .x15 = s.gpr .x15 - 1#64 ∧ t.mem = s.mem) ∧
        Keep [.x11, .x12, .x13, .x15] s t := by
  refine WP.keep [.x11, .x12, .x13, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  rw [← List.append_assoc]; unfold unpackW
  brun [exec_ins, h14, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_write, RegUpd.v_setV, (pack_unpack S N hS hN).1]
  simp only [laneOf, RegUpd.v_write, RegUpd.v_setV, (pack_unpack S N hS hN).2]
  simp only [reduceCtorEq, ↓reduceIte, extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide), extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide), extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide), extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide), true_and, and_true]
  intro r h1 h2 h3
  simp only [h1, h2, h3, ite_false]

/-- A batch's start: `59` divsteps from `d` (lane 0 of `v18`) and the low
words of `f` and `g` (arrays `iF`, `iG`), and `d` and the matrix into the
lanes of `v18`, `v16` and `v17`. -/
theorem batchHead_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iF iG : Nat} (hF : iF < 16) (hG : iG < 16)
    {d f g : Int} (hd : |d| ≤ 2 ^ 30) (hf : f % 2 = 1) (hv : laneOf s .v18 0 = BitVec.ofInt 64 d)
    (hfw : ((word s.mem B (slot w iF)).toNat : Int) % 2 ^ 64 = f % 2 ^ 64)
    (hgw : ((word s.mem B (slot w iG)).toNat : Int) % 2 ^ 64 = g % 2 ^ 64) :
    WP isa (.block (batchHead iF iG)) s fun t =>
      laneOf t .v18 0 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).d ∧
      laneOf t .v18 1 = laneOf s .v18 1 ∧
      laneOf t .v16 0 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).u ∧
      laneOf t .v16 1 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).v ∧
      laneOf t .v17 0 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).q ∧
      laneOf t .v17 1 = BitVec.ofInt 64 (Divstep.msteps 59 (Divstep.MSt.init d f g)).r ∧
      (∀ r, r ≠ .v16 → r ≠ .v17 → r ≠ .v18 → t.v r = s.v r) ∧ t.gpr .x11 = s.gpr .x11 ∧
      t.gpr .x12 = s.gpr .x12 ∧ t.gpr .x15 = s.gpr .x15 - 1#64 ∧ t.mem = s.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17] s t := by
  have hn' := hs.nowrap
  have sF := Nat.le_trans (slot_lt (w := w) hF) hZ
  have sG := Nat.le_trans (slot_lt (w := w) hG) hZ
  unfold batchHead
  simp only [List.append_assoc]
  have bv : ∀ j r, (Code.block (base j r) : Prog isa).allInstrs (fun i => (vdstOf i).isNone) = true := fun j r => by
    simp only [Code.allInstrs_eq, instrs, base_vnone]
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iF .x2 h0 h11) (bv _ _)) fun s₁ ⟨⟨⟨h2, m₁, _⟩, k₁⟩, v₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (WP.keep [.x2] (Q := fun t => t.gpr .x2 = word s.mem B (slot w iF) ∧
      t.mem = s₁.mem ∧ t.v = s₁.v) (by brun [h2, m₁, (hs.congr k₁.wr).ld (show slot w iF + 8 ≤ Z by omega), RegUpd.v_write]) (by decide) (by decide)
      (by decide +kernel)) fun s₂ ⟨⟨h2', m₂, v₂⟩, k₂⟩ =>
    WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iG .x3 ((k₁.trans k₂ |>.gpr .x0 (by decide)).trans h0)
      ((k₁.trans k₂ |>.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₃ ⟨⟨⟨h3, m₃, _⟩, k₃⟩, v₃⟩ => ?_)))
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x1, .x3] (Q := fun t => t.gpr .x3 = word s.mem B (slot w iG) ∧
      t.gpr .x1 = laneOf s .v18 0 ∧ t.mem = s₃.mem ∧ t.v = s₃.v)
      (by brun [h3, m₃, m₂, m₁, (hs.congr k13.wr).ld (show slot w iG + 8 ≤ Z by omega), RegUpd.v_write, exec_umov,
        laneOf, v₃, v₂, v₁]) (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h3', h1', m₄, v₄⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  have e11 : s₄.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k14.gpr .x11 (by decide)).trans h11
  have e12 : s₄.gpr .x12 = BitVec.ofNat 64 n := (k14.gpr .x12 (by decide)).trans h12
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x14] (Q := fun t =>
      t.gpr .x14 = BitVec.ofNat 64 (8 * (w + 2)) <<< 32 + BitVec.ofNat 64 n ∧ t.mem = s₄.mem ∧ t.v = s₄.v)
      (by unfold packW; brun [e11, e12, RegUpd.v_write]) (by decide) (by decide) (by decide +kernel))
    fun s₅ ⟨⟨h14, m₅, v₅⟩, k₅⟩ => ?_)
  have e2 : s₅.gpr .x2 = word s.mem B (slot w iF) := (k₅.gpr .x2 (by decide)).trans ((k₄.gpr .x2 (by decide)).trans
    ((k₃.gpr .x2 (by decide)).trans h2'))
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (Weierstrass.AArch64.pwords_ok s₅ (g := g) hd hf
    (by rw [k₅.gpr .x1 (by decide), h1', hv]) (by rw [e2]; exact hfw)
    (by rw [k₅.gpr .x3 (by decide), h3']; exact hgw)) (by decide +kernel)) fun s₆ ⟨⟨d₆, u₆, v₆, q₆, r₆, k₆⟩, vv₆⟩ => ?_)
  refine WP.mono (headTail_ok' s₆ (S := 8 * (w + 2)) (N := n) (by omega) (by omega)
    (by rw [k₆.gpr .x14 (by decide)]; exact h14)) fun t ⟨⟨l1, l2, l3, l4, l5, l6, lv, t11, t12, t15, tm⟩, kt⟩ => ?_
  have v06 : s₆.v = s.v := by rw [vv₆, v₅, v₄, v₃, v₂, v₁]
  refine ⟨by rw [l1, d₆], by rw [l2, laneOf, laneOf, v06], by rw [l3, u₆], by rw [l4, v₆], by rw [l5, q₆],
    by rw [l6, r₆], fun r a b c => by rw [lv r a b c, v06], by rw [t11, h11], by rw [t12, h12], ?_, ?_, ?_⟩
  · rw [t15, k₆.gpr .x15 (by decide), k₅.gpr .x15 (by decide), k14.gpr .x15 (by decide)]
  · rw [tm, k₆.mem, m₅, m₄, m₃, m₂, m₁]
  · have k6 : Keep Weierstrass.AArch64.chunkRegs s₅ s₆ := ⟨k₆.gpr, k₆.rd, k₆.wr, k₆.sp, fun r _ => by rw [vv₆]⟩
    exact (((k14.trans k₅).trans k6).trans kt).mono (by decide)
end VG.Proof.Rsa.AArch64
