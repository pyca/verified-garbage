module

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Framework.AArch64.LaneRestore
public import VerifiedGarbage.Proof.Rsa.AArch64.InvBase
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave

/-!
# RSA private keys on AArch64: pieces of the batched inverse's start and end

The masked addition in place (`addMIP_ok`, `addMBody`'s loop with its output
the addend), the address of word `n` of an array (`topAt_ok`) and its
clearing (`zeroTop_ok`) and sign (`signMask_ok`), and the blocks of
`Keys.batchInit` (`initHead_ok`, `initLast_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A step of `addMBody`'s loop, `[x5]` possibly `[x8]`. -/
theorem maStepIP_ok {s₀ : State} {B : Addr} {Z w eo eN eA : Nat} {c : Bool} (h15 : s₀.gpr .x15 = mask c)
    (ho : eo + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) (hA : eA + 8 * w ≤ Z)
    (sN : eN + 8 * w ≤ eo ∨ eo + 8 * w ≤ eN) (sA : eo ≤ eA ∨ eA + 8 * w ≤ eo)
    {j : Nat} (hj : j < w) {t : State} (hI : MaInv s₀ B Z eo eN eA c j t) :
    WP isa (.block ([ld .x3 .x10, .logic .and .x .x3 .x3 .x15, ld .x4 .x8, .adcs .x .x3 .x3 .x4, st .x3 .x5,
        next .x10, next .x8, next .x5] ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => MaInv s₀ B Z eo eN eA c (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t15 : t.gpr .x15 = mask c := (hI.keep.gpr .x15 (by decide)).trans h15
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x4, .x5, .x8, .x10] (Q := fun t₁ =>
      t₁.mem = t.mem.writeW (off B (eo + 8 * j)) ((word t.mem B (eN + 8 * j) &&& mask c) +
        word t.mem B (eA + 8 * j) + BitVec.ofNat 64 t.c.toNat) ∧
      t₁.c = decide (2 ^ 64 ≤ (word t.mem B (eN + 8 * j) &&& mask c).toNat + (word t.mem B (eA + 8 * j)).toNat +
        t.c.toNat) ∧
      t₁.gpr .x10 = off B (eN + 8 * j + 8) ∧ t₁.gpr .x8 = off B (eA + 8 * j + 8) ∧
      t₁.gpr .x5 = off B (eo + 8 * j + 8))
    (by brun [hI.x10, hI.x8, hI.x5, t15, hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega_using [hN, hj]),
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega_using [hA, hj]), hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega_using [ho, hj])])
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨hm, hc, h10, h8, h5⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', hc'⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega_using [sN, hj]) (by omega_using [hN, hj, hn])
  have hy : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega_using [sA, hj]) (by omega_using [hA, hj, hn])
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x10 (by decide), h10, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x8 (by decide), h8, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x5 (by decide), h5, Nat.mul_succ, Nat.add_assoc], ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega_using [ho, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega_using [ho, hj, hn]), hc', hc]
    have hs := adcs_toNat (word t.mem B (eN + 8 * j) &&& mask c) (word t.mem B (eA + 8 * j)) t.c
    rw [hx, hy, and_mask] at hs
    have hval := hI.val
    simp only [wv]
    rw [pow64_succ, hx, hy, and_mask]
    cases c
    · simp only [ite_false, Bool.false_eq_true] at hs hval ⊢
      grind
    · simp only [ite_true] at hs hval ⊢
      grind


/-- `addMBody`'s loop, `[x5]` possibly `[x8]`. -/
theorem addMIP_ok {s : State} {B : Addr} {Z N eo eN eA : Nat} {c : Bool} (hs : Scr s B Z)
    (h10 : s.gpr .x10 = off B eN) (h8 : s.gpr .x8 = off B eA) (h5 : s.gpr .x5 = off B eo)
    (h14 : s.gpr .x14 = BitVec.ofNat 64 N) (h15 : s.gpr .x15 = mask c) (hc : s.c = false)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 31) (ho : eo + 8 * N ≤ Z) (hM : eN + 8 * N ≤ Z) (hA : eA + 8 * N ≤ Z)
    (sN : eN + 8 * N ≤ eo ∨ eo + 8 * N ≤ eN) (sA : eo ≤ eA ∨ eA + 8 * N ≤ eo) :
    WP isa (countLoop .x14 addMBody) s fun t =>
      wv t.mem B eo N + 2 ^ (64 * N) * t.c.toNat = (if c then wv s.mem B eN N else 0) + wv s.mem B eA N ∧
      t.gpr .x5 = off B (eo + 8 * N) ∧ Outside B eo (8 * N) s.mem t.mem ∧
      Keep [.x3, .x4, .x5, .x8, .x10, .x14] s t := by
  have h0 : MaInv s B Z eo eN eA c 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h10]; rfl, by rw [h8]; rfl, by rw [h5]; rfl, Outside.refl _ _ _ _,
      by rw [hc]; cases c <;> rfl⟩
  refine WP.mono (wp_countdown (N := N) (by omega_using [hN']) (by omega_using [hN]) (MaInv s B Z eo eN eA c)
    (fun j hj t hI _ => maStepIP_ok h15 ho hM hA sN sA hj hI) h0 h14) fun t hI => ⟨hI.val, hI.x5, hI.out, hI.keep⟩



/-- `topAt j x16`: the address of word `n` of array `j`. -/
theorem topAt_ok {s : State} {B : Addr} {w n : Nat} (j : Nat) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n < 2 ^ 24) :
    WP isa (.block (topAt j .x16)) s fun t =>
      (t.gpr .x16 = off B (slot w j + 8 * n) ∧ t.mem = s.mem ∧ t.v = s.v ∧ t.c = s.c) ∧ Keep [.x3, .x16] s t := by
  unfold topAt
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok j .x16 h0 h11)
    (by simp only [Code.allInstrs_eq, instrs, base_vnone])) fun s₁ ⟨⟨⟨h16, m₁, c₁⟩, k₁⟩, v₁⟩ => ?_)
  refine WP.mono (WP.keep [.x3, .x16] (Q := fun t => t.gpr .x16 = off B (slot w j + 8 * n) ∧ t.mem = s₁.mem ∧
      t.v = s₁.v ∧ t.c = s₁.c)
    (by brun [h16, (k₁.gpr .x12 (by decide)).trans h12, shl_ofNat (show n * 2 ^ 3 < 2 ^ 64 by omega),
      RegUpd.v_write, off_add]; congr 2; omega) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h, m, v, c⟩, k⟩ => ⟨⟨h, m.trans m₁, v.trans v₁, c.trans c₁⟩, (k₁.trans k).mono (by decide)⟩

/-- `zeroTop j`: word `n` of array `j` cleared. -/
theorem zeroTop_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (j : Nat) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n ≤ w)
    (hw : w < 2 ^ 24) (hj : j < 16) (hZ : slot w 16 ≤ Z) :
    WP isa (.block (zeroTop j)) s fun t =>
      (t.mem = s.mem.writeW (off B (slot w j + 8 * n)) 0#64 ∧ t.v = s.v ∧ t.c = s.c) ∧ Keep [.x3, .x16] s t := by
  have sj := Nat.le_trans (slot_lt (w := w) hj) hZ
  unfold zeroTop
  refine WP.block_append_iff.mpr (WP.mono (topAt_ok j h0 h11 h12 (by omega)) fun s₁ ⟨⟨h16, m₁, v₁, c₁⟩, k₁⟩ => ?_)
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (slot w j + 8 * n)) 0#64 ∧
      t.v = s₁.v ∧ t.c = s₁.c)
    (by brun [h16, (hs.congr k₁.wr).st (show slot w j + 8 * n + 8 ≤ Z by omega), m₁, RegUpd.v_write]; rfl)
    (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨m, v, c⟩, k⟩ => ⟨⟨m, v.trans v₁, c.trans c₁⟩, (k₁.trans k).mono (by decide)⟩

/-- `signMask j`: the sign mask of word `n` of array `j` into `x15`, `x7 := 0`. -/
theorem signMask_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (j : Nat) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn : n ≤ w)
    (hw : w < 2 ^ 24) (hj : j < 16) (hZ : slot w 16 ≤ Z) :
    WP isa (.block (signMask j)) s fun t =>
      (t.gpr .x15 = 0#64 - (word s.mem B (slot w j + 8 * n) >>> 63) ∧ t.gpr .x7 = 0 ∧ t.mem = s.mem ∧
        t.v = s.v) ∧ Keep [.x3, .x7, .x15, .x16] s t := by
  have sj := Nat.le_trans (slot_lt (w := w) hj) hZ
  unfold signMask
  refine WP.block_append_iff.mpr (WP.mono (topAt_ok j h0 h11 h12 (by omega)) fun s₁ ⟨⟨h16, m₁, v₁, c₁⟩, k₁⟩ => ?_)
  refine WP.mono (WP.keep [.x3, .x7, .x15] (Q := fun t => t.gpr .x15 = 0#64 - (word s.mem B (slot w j + 8 * n) >>> 63) ∧
      t.gpr .x7 = 0 ∧ t.mem = s₁.mem ∧ t.v = s₁.v)
    (by brun [h16, (hs.congr k₁.wr).ld (show slot w j + 8 * n + 8 ≤ Z by omega), m₁, RegUpd.v_write,
      show BitVec.setWidth 64 0#16 = 0#64 from rfl]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h15, h7, m, v⟩, k⟩ => ⟨⟨h15, h7, m.trans m₁, v.trans v₁⟩, (k₁.trans k).mono (by decide)⟩

/-- The mask of a word even. -/
theorem mask_even (x : BitVec 64) : (x &&& BitVec.setWidth 64 1#16) - 1#64 = mask (decide (x.toNat % 2 = 0)) := by
  have h2 : x &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The start's first block: `x1`, `x2` into `v19`, words `n` of `f` and `g`
cleared, and what `g`'s masked addition needs. -/
theorem initHead_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iF iG iM : Nat} (hF : iF < 16) (hG : iG < 16)
    (dFG : iF ≠ iG) :
    WP isa (.block ([.vop (.ins .d2 .v19 0 .x1), .vop (.ins .d2 .v19 1 .x2)] ++ zeroTop iF ++ zeroTop iG ++
      base iG .x8 ++ ([ld .x3 .x8, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1, movi .x7 0,
        mov .x14 .x12, .adds .x .x3 .x7 .x7] : List Instr) ++ base iM .x10 ++ base iG .x5)) s fun t =>
      (t.mem = (s.mem.writeW (off B (slot w iF + 8 * n)) 0#64).writeW (off B (slot w iG + 8 * n)) 0#64 ∧
        laneOf t .v19 0 = s.gpr .x1 ∧ laneOf t .v19 1 = s.gpr .x2 ∧ (∀ r, r ≠ .v19 → t.v r = s.v r) ∧
        t.gpr .x8 = off B (slot w iG) ∧ t.gpr .x5 = off B (slot w iG) ∧ t.gpr .x10 = off B (slot w iM) ∧
        t.gpr .x15 = mask (decide ((word s.mem B (slot w iG)).toNat % 2 = 0)) ∧ t.gpr .x7 = 0 ∧
        t.gpr .x14 = BitVec.ofNat 64 n ∧ t.c = false) ∧
      Keep [.x3, .x4, .x5, .x7, .x8, .x10, .x14, .x15, .x16] s t := by
  have hn' := hs.nowrap
  have sF := Nat.le_trans (slot_lt (w := w) hF) hZ
  have sG := Nat.le_trans (slot_lt (w := w) hG) hZ
  have bv : ∀ j r, (Code.block (base j r) : Prog isa).allInstrs (fun i => (vdstOf i).isNone) = true := fun j r => by
    simp only [Code.allInstrs_eq, instrs, base_vnone]
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [] (Q := fun t => laneOf t .v19 0 = s.gpr .x1 ∧
      laneOf t .v19 1 = s.gpr .x2 ∧ (∀ r, r ≠ .v19 → t.v r = s.v r) ∧ t.mem = s.mem ∧ t.c = s.c)
    (by brun [exec_ins, RegUpd.gpr_setV, RegUpd.mem_setV]
        simp (config := { decide := true }) only [laneOf, RegUpd.v_setV, ite_true, Nat.mul_zero, Nat.mul_one,
          extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide),
          extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide),
          extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide),
          extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide), ite_false, true_and]
        exact ⟨fun r h => by simp only [h, ite_false], rfl⟩) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨l0, l1, lv, m₁, c₁⟩, k₁⟩ => ?_)
  have g0 : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  have g11 : s₁.gpr .x11 = _ := (k₁.gpr .x11 (by decide)).trans h11
  have g12 : s₁.gpr .x12 = _ := (k₁.gpr .x12 (by decide)).trans h12
  refine WP.block_append_iff.mpr (WP.mono (zeroTop_ok (hs.congr k₁.wr) iF g0 g11 g12 hn hw hF hZ)
    fun s₂ ⟨⟨m₂, v₂, c₂⟩, k₂⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (zeroTop_ok (hs.congr (k₁.trans k₂).wr) iG
    ((k₂.gpr .x0 (by decide)).trans g0) ((k₂.gpr .x11 (by decide)).trans g11) ((k₂.gpr .x12 (by decide)).trans g12)
    hn hw hG hZ) fun s₃ ⟨⟨m₃, v₃, c₃⟩, k₃⟩ => ?_)
  have k13 := (k₁.trans k₂).trans k₃
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iG .x8 ((k13.gpr .x0 (by decide)).trans h0)
    ((k13.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₄ ⟨⟨⟨h8, m₄, c₄⟩, k₄⟩, v₄⟩ => ?_)
  have k14 := k13.trans k₄
  have hm₄ : s₄.mem = (s.mem.writeW (off B (slot w iF + 8 * n)) 0#64).writeW (off B (slot w iG + 8 * n)) 0#64 := by
    rw [m₄, m₃, m₂, m₁]
  have sepFG := slot_apart (w := w) (a := 8) (b := 8 * (n + 1)) dFG.symm (by omega) (by omega)
  have w0 : word s₄.mem B (slot w iG) = word s.mem B (slot w iG) := by
    rw [hm₄, (writeW_outside _ B _ (by omega)).word (by omega) (by omega),
      (writeW_outside _ B _ (by omega)).word (by rcases sepFG with h | h <;> omega) (by omega)]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x4, .x7, .x14, .x15] (Q := fun t =>
      t.gpr .x15 = mask (decide ((word s.mem B (slot w iG)).toNat % 2 = 0)) ∧ t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 n ∧ t.c = false ∧ t.mem = s₄.mem ∧ t.v = s₄.v)
    (by brun [h8, (hs.congr k14.wr).ld (show slot w iG + 8 ≤ Z by omega), (k14.gpr .x12 (by decide)).trans h12,
        RegUpd.v_write, mask_even, w0]
        rfl) (by decide) (by decide) (by decide +kernel)) fun s₅ ⟨⟨h15, h7, h14, c₅, m₅, v₅⟩, k₅⟩ => ?_)
  have k15 := k14.trans k₅
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iM .x10 ((k15.gpr .x0 (by decide)).trans h0)
    ((k15.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₆ ⟨⟨⟨h10, m₆, c₆⟩, k₆⟩, v₆⟩ => ?_)
  have k16 := k15.trans k₆
  refine WP.mono (WP.vfix (base_ok iG .x5 ((k16.gpr .x0 (by decide)).trans h0)
    ((k16.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun t ⟨⟨⟨h5, m₇, c₇⟩, k₇⟩, v₇⟩ =>
    ⟨⟨by rw [m₇, m₆, m₅, hm₄], by rw [laneOf, v₇, v₆, v₅, v₄, v₃, v₂]; exact l0,
      by rw [laneOf, v₇, v₆, v₅, v₄, v₃, v₂]; exact l1, fun r hr => by rw [v₇, v₆, v₅, v₄, v₃, v₂]; exact lv r hr,
      (k₇.gpr .x8 (by decide)).trans ((k₆.gpr .x8 (by decide)).trans ((k₅.gpr .x8 (by decide)).trans h8)), h5,
      (k₇.gpr .x10 (by decide)).trans h10, (k₇.gpr .x15 (by decide)).trans ((k₆.gpr .x15 (by decide)).trans h15),
      (k₇.gpr .x7 (by decide)).trans ((k₆.gpr .x7 (by decide)).trans h7),
      (k₇.gpr .x14 (by decide)).trans ((k₆.gpr .x14 (by decide)).trans h14), by rw [c₇, c₆, c₅]⟩,
      ((k16.trans k₇)).mono (by decide)⟩

/-- The start's last block: `b`'s word 0 set, `-(m | 1)⁻¹` into lane 1 of
`v18` and `d = 1` into lane 0, `f`'s word 0 or'ed with 1, and
`x15 := 3 n + 2`. -/
theorem initLast_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {iB iM iF : Nat} (hB : iB < 16) (hM : iM < 16)
    (hF : iF < 16) (dBM : iB ≠ iM) (dFB : iF ≠ iB) :
    WP isa (.block (base iB .x16 ++ ([movi .x3 1, st .x3 .x16] : List Instr) ++ base iM .x3 ++
      ([ld .x3 .x3, movi .x4 1, .logic .orr .x .x3 .x3 .x4] : List Instr) ++ minv ++
      [.vop (.ins .d2 .v18 1 .x15), movi .x3 1, .vop (.ins .d2 .v18 0 .x3)] ++ base iF .x16 ++
      ([ld .x4 .x16, .logic .orr .x .x4 .x4 .x3, st .x4 .x16] : List Instr) ++ batchCount)) s fun t =>
      (t.mem = (s.mem.writeW (off B (slot w iB)) 1#64).writeW (off B (slot w iF))
          (word s.mem B (slot w iF) ||| 1#64) ∧ laneOf t .v18 0 = 1#64 ∧
        ((word s.mem B (slot w iM) ||| 1#64).toNat * (laneOf t .v18 1).toNat + 1) % 2 ^ 64 = 0 ∧
        (∀ r, r ≠ .v18 → t.v r = s.v r) ∧ t.gpr .x15 = BitVec.ofNat 64 (3 * n + 2)) ∧
      Keep [.x3, .x4, .x5, .x6, .x15, .x16] s t := by
  have hn' := hs.nowrap
  have sB := Nat.le_trans (slot_lt (w := w) hB) hZ
  have sM := Nat.le_trans (slot_lt (w := w) hM) hZ
  have sF := Nat.le_trans (slot_lt (w := w) hF) hZ
  have bv : ∀ j r, (Code.block (base j r) : Prog isa).allInstrs (fun i => (vdstOf i).isNone) = true := fun j r => by
    simp only [Code.allInstrs_eq, instrs, base_vnone]
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iB .x16 h0 h11) (bv _ _))
    fun s₁ ⟨⟨⟨h16, m₁, _⟩, k₁⟩, v₁⟩ => ?_)
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3] (Q := fun t =>
      t.mem = s.mem.writeW (off B (slot w iB)) 1#64 ∧ t.v = s₁.v)
    (by brun [h16, (hs.congr k₁.wr).st (show slot w iB + 8 ≤ Z by omega), m₁, RegUpd.v_write]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨⟨m₂, v₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iM .x3 ((k12.gpr .x0 (by decide)).trans h0)
    ((k12.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₃ ⟨⟨⟨h3, m₃, _⟩, k₃⟩, v₃⟩ => ?_)
  have k13 := k12.trans k₃
  have wM : word s₃.mem B (slot w iM) = word s.mem B (slot w iM) := by
    rw [m₃, m₂, (writeW_outside _ B _ (by omega)).word (by
      rcases slot_apart (w := w) (a := 8) (b := 8) dBM.symm (by omega) (by omega) with h | h <;> omega) (by omega)]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3, .x4] (Q := fun t =>
      t.gpr .x3 = word s.mem B (slot w iM) ||| 1#64 ∧ t.mem = s₃.mem ∧ t.v = s₃.v)
    (by brun [h3, (hs.congr k13.wr).ld (show slot w iM + 8 ≤ Z by omega), wM, RegUpd.v_write]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h3', m₄, v₄⟩, k₄⟩ => ?_)
  have k14 := k13.trans k₄
  have odd : (s₄.gpr .x3).toNat % 2 = 1 := by
    rw [h3', BitVec.toNat_or, BitVec.toNat_ofNat]
    exact Nat.or_mod_two_eq_one.mpr (.inr rfl)
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (minv_ok s₄ odd) (by decide +kernel))
    fun s₅ ⟨⟨hmi, k₅, m₅⟩, v₅⟩ => ?_)
  have k15 := k14.trans k₅
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x3] (Q := fun t => laneOf t .v18 0 = 1#64 ∧
      laneOf t .v18 1 = s₅.gpr .x15 ∧ (∀ r, r ≠ .v18 → t.v r = s₅.v r) ∧ t.mem = s₅.mem ∧ t.gpr .x3 = 1#64)
    (by
      brun [exec_ins, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.v_write]
      simp (config := { decide := true }) only [laneOf, RegUpd.v_write, RegUpd.v_setV, ite_true, Nat.mul_zero,
        Nat.mul_one, extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide),
        extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (0 : Nat) < 2 by decide),
        extract_setLane64 _ _ (show (0 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide),
        extract_setLane64 _ _ (show (1 : Nat) < 2 by decide) (show (1 : Nat) < 2 by decide), ite_false, true_and]
      exact fun r h => by simp only [h, ite_false]) (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨⟨l0, l1, lv, m₆, h3₆⟩, k₆⟩ => ?_)
  have k16 := k15.trans k₆
  refine WP.block_append_iff.mpr (WP.mono (WP.vfix (base_ok iF .x16 ((k16.gpr .x0 (by decide)).trans h0)
    ((k16.gpr .x11 (by decide)).trans h11)) (bv _ _)) fun s₇ ⟨⟨⟨h16₇, m₇, _⟩, k₇⟩, v₇⟩ => ?_)
  have k17 := k16.trans k₇
  have hm₇ : s₇.mem = s.mem.writeW (off B (slot w iB)) 1#64 := by rw [m₇, m₆, m₅, m₄, m₃, m₂]
  have wF : word s₇.mem B (slot w iF) = word s.mem B (slot w iF) := by
    rw [hm₇, (writeW_outside _ B _ (by omega)).word (by
      rcases slot_apart (w := w) (a := 8) (b := 8) dFB (by omega) (by omega) with h | h <;> omega) (by omega)]
  refine WP.mono (WP.keep [.x4, .x15] (Q := fun t => t.mem = s₇.mem.writeW (off B (slot w iF))
      (word s.mem B (slot w iF) ||| 1#64) ∧ t.v = s₇.v ∧ t.gpr .x15 = BitVec.ofNat 64 (3 * n + 2))
    (by
      unfold batchCount
      brun [h16₇, (hs.congr k17.wr).ld (show slot w iF + 8 ≤ Z by omega),
        (hs.congr k17.wr).st (show slot w iF + 8 ≤ Z by omega), wF, (k₇.gpr .x3 (by decide)).trans h3₆,
        RegUpd.v_write, (k17.gpr .x12 (by decide)).trans h12]
      simp only [off, BitVec.ofNat_add_ofNat]
      congr 1; omega) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨m₈, v₈, h15⟩, k₈⟩ =>
    ⟨⟨by rw [m₈, hm₇], by rw [laneOf, v₈, v₇, ← laneOf]; exact l0,
      by rw [laneOf, v₈, v₇, ← laneOf, l1, ← h3']; exact hmi,
      fun r hr => by rw [v₈, v₇, lv r hr, v₅, v₄, v₃, v₂, v₁], h15⟩, (k17.trans k₈).mono (by decide)⟩
end VG.Proof.Rsa.AArch64
