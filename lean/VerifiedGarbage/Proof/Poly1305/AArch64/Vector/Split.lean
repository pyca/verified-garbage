import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Lanes
import VerifiedGarbage.Proof.Poly1305.Limbs26

/-!
# Poly1305 on AArch64 in AdvSIMD: two blocks into limbs

Untrusted: everything here is checked by Lean. `split off` leaves in lane `e`
of `iV i` limb `i` of the block at `x2 + off + 16 e`, with the pad bit
(`blk`).
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Poly1305.Limbs26 (val)

/-- The limbs of the block `lo + 2⁶⁴ hi`, with the pad bit `2¹²⁸`. -/
def blk (lo hi : Nat) : Nat → Nat
  | 0 => lo % 2 ^ 26
  | 1 => lo / 2 ^ 26 % 2 ^ 26
  | 2 => (hi * 2 ^ 12 % 2 ^ 64 + lo / 2 ^ 52) % 2 ^ 26
  | 3 => hi / 2 ^ 14 % 2 ^ 26
  | _ => hi / 2 ^ 40 + 2 ^ 24

theorem blk_val {lo hi : Nat} (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64) :
    val (blk lo hi) = lo + 2 ^ 64 * hi + 2 ^ 128 := by
  have := hlo; have := hhi
  simp only [val, blk]
  omega

theorem blk_lt (lo : Nat) {hi : Nat} (hhi : hi < 2 ^ 64) : ∀ i < 5, blk lo hi i < 2 ^ 26 := by
  intro i hi'
  have := hhi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [blk] <;> omega

/-- The block at `p`: its words. -/
abbrev blo (m : Mem) (p : Addr) : Nat := ln (m.read p 16) 0
abbrev bhi (m : Mem) (p : Addr) : Nat := ln (m.read p 16) 1

/-- The address of block `e` of a pair at `x2 + off`. -/
abbrev bAddr (s : State) (off e : Nat) : Addr := s.gpr .x2 + BitVec.ofNat 64 (off + 16 * e)

/-- Reads of the vector registers through the writes of the steps so far. -/
macro "vstep" : tactic =>
  `(tactic| simp (disch := decide) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne])

theorem iV_ne : ∀ i < 5, ∀ j < 5, i ≠ j → iV i ≠ iV j := by decide

/-- What `split` keeps. -/
structure SKeep (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : ∀ r, (∀ i < 5, r ≠ iV i) → t.v r = s.v r

theorem split_ok {s : State} {off : Nat} (ho : off % 16 = 0) (ho' : off + 16 < 4096 * 16)
    (hm : ∀ e < 2, ln (s.v maskV) e = 2 ^ 26 - 1) (hp : ∀ e < 2, ln (s.v padV) e = 2 ^ 24)
    (hr : ∀ e < 2, InRegions (s.rd ++ s.wr) (bAddr s off e) 16) :
    WP isa (.block (split off)) s fun t =>
      (∀ i < 5, ∀ e < 2, ln (t.v (iV i)) e =
        blk (blo s.mem (bAddr s off e)) (bhi s.mem (bAddr s off e)) i) ∧ SKeep s t := by
  have r0 := hr 0 (by decide)
  have r1 := hr 1 (by decide)
  simp only [bAddr, Nat.mul_zero, Nat.add_zero, Nat.mul_one] at r0 r1
  simp only [split]
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq ⟨ho, by omega⟩ r0, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ldrq ⟨by omega, by omega⟩ (by simpa only [RegUpd.gpr_setV,
    RegUpd.rd_setV, RegUpd.wr_setV] using r1), ?_⟩
  simp only [RegUpd.gpr_setV, RegUpd.mem_setV]
  generalize hA : s.mem.read (s.gpr .x2 + BitVec.ofNat 64 off) 16 = A
  generalize hB : s.mem.read (s.gpr .x2 + BitVec.ofNat 64 (off + 16)) 16 = B
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_cons_iff.mpr ⟨_, exec_vo rfl, ?_⟩
  vstep
  refine WP.block_nil_iff.mpr ⟨fun i hi e he => ?_, ?_⟩
  · have hM := hm e he
    have hP := hp e he
    have hZ1 : ln (VPermOp.eval .zip1 .d2 A B) e = blo s.mem (bAddr s off e) := by
      rw [ln, zip1_ln _ _ he]
      rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
      · simp only [ite_true, ← hA, bAddr, Nat.mul_zero, Nat.add_zero]
      · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ← hB, bAddr, Nat.mul_one]
    have hZ2 : ln (VPermOp.eval .zip2 .d2 A B) e = bhi s.mem (bAddr s off e) := by
      rw [ln, zip2_ln _ _ he]
      rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
      · simp only [ite_true, ← hA, bAddr, Nat.mul_zero, Nat.add_zero]
      · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ← hB, bAddr, Nat.mul_one]
    have hlo : blo s.mem (bAddr s off e) < 2 ^ 64 := (vdword _ 0).isLt
    have hhi : bhi s.mem (bAddr s off e) < 2 ^ 64 := (vdword _ 1).isLt
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [RegUpd.v_setV_self, RegUpd.v_setV_of_ne]
    · rw [ln_and_mask _ _ hM, hZ1]; simp only [blk]
    · rw [ln_and_mask _ _ hM, ln_ushr _ _ _ he, hZ1]; simp only [blk]
    · rw [ln_and_mask _ _ hM, ln_sli _ _ he (by rw [ln_ushr _ _ _ he, hZ1]; omega), ln_ushr _ _ _ he,
        hZ1, hZ2]
      simp only [blk]
    · rw [ln_and_mask _ _ hM, ln_ushr _ _ _ he, hZ2]; simp only [blk]
    · rw [ln_or_pad _ _ hP (by rw [ln_ushr _ _ _ he, hZ2]; omega), ln_ushr _ _ _ he, hZ2]; simp only [blk]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
    · simp only [RegUpd.gpr_setV]
    · simp only [RegUpd.mem_setV]
    · simp only [RegUpd.rd_setV]
    · simp only [RegUpd.wr_setV]
    · simp only [RegUpd.sp_setV]
    · have := hr 0 (by decide); have := hr 1 (by decide); have := hr 2 (by decide)
      have := hr 3 (by decide); have := hr 4 (by decide)
      simp (disch := assumption) only [RegUpd.v_setV_of_ne]

end VG.Proof.Poly1305.AArch64.Vector
