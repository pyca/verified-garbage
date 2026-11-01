module

public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.Round
public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
public import VerifiedGarbage.Proof.Sha3.X2Contract
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Store
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.Round
meta import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
meta import VerifiedGarbage.Proof.Sha3.X2Contract
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Store
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Permute
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.TCB.Axioms

/-!
# `vg_keccak_f1600_x3_sha3` on AArch64

Untrusted: everything here is checked by Lean. The function
(`Impl/Sha3/AArch64/Hybrid/X3.lean`) opens a frame of 128 bytes at
`S = sp - 128`, saves the callee-saved registers and the three pointers in
its slots (`slots_ok`, `SlotsAt`) and `q8`–`q15` in `scratch`
(`scr_save_ok`), loads the two interleaved states into `v0`–`v24` and the
third into the general registers, runs the 24 rounds (`rounds_ok`), and
then, from the pointers it reloads from the frame, stores the states
(`b2_ok`, `b3_ok`) and restores the registers (`b4_ok`); the frame's
slots keep what they hold through the rounds and the stores (`SlotsAt.frame`). `verified`: its
contract (`Proof/Sha3/X2Contract.lean`).

The taint analysis does not track the frame, so the constant-time proof
(`ct`) checks the code in pieces: the saves, loads and rounds from the three
public pointers, and each piece after a reload of a pointer from the frame
from that pointer, which the correctness proofs show is the same public value
in both runs. The code is checked only here, so it has no literal.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Hybrid.X3

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Sha3.Vector (exec_strq exec_ldrq read_write16 vreg_inj)
open VG.Proof.Sha3.AArch64.Neon (Pairs PairAt pairR wordAddr pair_contains)
open VG.Proof.Sha3.AArch64.Neon.X2 (scr_contains Saved pairAt_stateX2 stateX2_of_pairAt)
open VG.Proof.Sha3.AArch64.Scalar (exec_strSp)
open VG.Proof.Sha3.AArch64.Scalar.Boundary (laneReg_ne_x30 laneReg_inj store_words_ok)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint ct_of RelCT.block_split)
open VG.Spec.Sha3 (stateAt keccakF)
open VG.Proof.Sha3 (stateX2At)

abbrev X3code := VG.Impl.Sha3.AArch64.Hybrid.X3.code

/-- The working space. -/
abbrev scrR (q : Addr) : Region := Neon.X2.scrR q

abbrev Lanes := Scalar.Boundary.Lanes

/-! ## The frame's slots -/

/-- The registers the frame's slots `[S + 16 + 8 j]` hold: the callee-saved
registers, then the three pointers. -/
def slotReg (j : Nat) : Reg :=
  [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30, .x0, .x1, .x2].getD j .x19

theorem savedReg_slot : ∀ i < 11, Impl.Sha3.AArch64.Hybrid.X3.savedReg i = slotReg i := by decide

theorem savedReg_inj : ∀ i < 11, ∀ j < 11,
    Impl.Sha3.AArch64.Hybrid.X3.savedReg i = Impl.Sha3.AArch64.Hybrid.X3.savedReg j ↔ i = j := by
  decide

theorem preserved_saved : ∀ r ∈ preserved, ∃ i < 11, r = Impl.Sha3.AArch64.Hybrid.X3.savedReg i := by
  decide

/-- The slots. -/
def slotR (S : Addr) : Region := ⟨S + BitVec.ofNat 64 16, 112⟩

/-- The slots of the frame at `S` hold the registers of `s₀`. -/
def SlotsAt (S : Addr) (s₀ : State) (m : Mem) : Prop :=
  ∀ j < 14, m.readW (S + BitVec.ofNat 64 (16 + 8 * j)) 64 = s₀.gpr (slotReg j)

theorem SlotsAt.frame {S : Addr} {s₀ : State} {m m' : Mem} {rs : List Region} (h : SlotsAt S s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotR S).Disjoint r) : SlotsAt S s₀ m' := by
  intro j hj
  rw [hf.readW (r := slotR S) (Offset.contains S (by omega) (by omega) (by omega)) hd (by decide)]
  exact h j hj

theorem Saved.frame {s₀ : State} {q : Addr} {m m' : Mem} {rs : List Region} (h : Saved s₀ q m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (scrR q).Disjoint r) : Saved s₀ q m' := by
  intro i hi
  rw [hf.read (scr_contains q hi) hd (by decide)]
  exact h i hi

theorem pairAt_frame {p : Addr} {A B : Spec.Sha3.State} {m m' : Mem} {rs : List Region}
    (h : PairAt m p A B) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (pairR p).Disjoint r) :
    PairAt m' p A B := fun i hi => by
  rw [hf.read (pair_contains p hi) hd (by decide)]; exact h i hi

/-- The third state's region. -/
def stR (q : Addr) : Region := ⟨q, 200⟩

theorem stateAt_frame {q : Addr} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (stR q).Disjoint r) : stateAt m' q = stateAt m q := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (r := stR q) (Offset.contains_base q (by omega) (by omega)) hd (by decide)

/-- `str x<slotReg j>, [sp, #16 + 8 j]` for each slot. -/
theorem slots_ok {u : State} (hw : ∀ j < 14, InRegions u.wr (u.sp + BitVec.ofNat 64 (16 + 8 * j)) 8) :
    WP isa (.block ((List.range 14).map fun j => Instr.strSp (slotReg j) (16 + 8 * j))) u fun u' =>
      u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      Frame [slotR u.sp] u.mem u'.mem ∧ SlotsAt u.sp u u'.mem := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k x => x.gpr = u.gpr ∧ x.v = u.v ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
      Frame [slotR u.sp] u.mem x.mem ∧
      ∀ j < k, x.mem.readW (u.sp + BitVec.ofNat 64 (16 + 8 * j)) 64 = u.gpr (slotReg j))
    (fun k x hk ⟨hg, hv, hr, hwr, hsp, hf, hvals⟩ => ?_) 14 (Nat.le_refl _) u
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.cons (exec_strSp ⟨by omega, by omega⟩ (by rw [hwr, hsp]; exact hw k hk))
    (WP.block_nil ⟨hg, hv, hr, hwr, hsp, ?_, fun j hj => ?_⟩)
  · change Frame _ _ (x.mem.writeW _ _)
    rw [hsp]
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains u.sp (by omega) (by omega) (by omega))
  · change (x.mem.writeW _ _).readW _ 64 = _
    rw [hsp, hg]
    by_cases he : j = k
    · subst j; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hvals j (by omega)

/-- `q8`–`q15` saved at `x2`. -/
theorem scr_save_ok {u : State} {q : Addr} (hq : u.gpr .x2 = q)
    (hw : ∀ i < 8, InRegions u.wr (q + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 8).map fun i => Instr.strq (vreg (8 + i)) .x2 (16 * i))) u fun u' =>
      u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      Frame [scrR q] u.mem u'.mem ∧ Saved u q u'.mem := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k x => x.gpr = u.gpr ∧ x.v = u.v ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
      Frame [scrR q] u.mem x.mem ∧
      ∀ i < k, x.mem.read (q + BitVec.ofNat 64 (16*i)) 16 = u.v (vreg (8+i)))
    (fun k x hk ⟨hg, hv, hr, hwr, hsp, hf, hvals⟩ => ?_) 8 (Nat.le_refl _) u
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  refine WP.cons (exec_strq ⟨by omega, by omega⟩ (by rw [hwr, hg, hq]; exact hw k hk))
    (WP.block_nil_iff.mpr ⟨hg, hv, hr, hwr, hsp, ?_, fun i hi => ?_⟩)
  · change Frame _ _ (x.mem.write _ 16 _)
    rw [hg, hq]
    exact hf.write (List.mem_singleton_self _) _ (scr_contains q hk)
  · change (x.mem.write _ 16 _).read _ 16 = _
    rw [hg, hq, hv]
    by_cases he : i = k
    · subst i
      exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact hvals i (by omega)

/-- The third state's lanes into the general registers, from `x1`. -/
theorem lanes_ok (u : State)
    (hin : ∀ i < 25, InRegions (u.rd ++ u.wr) (u.gpr .x1 + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block (([.addImm .x .x30 .x1 0] : List Instr) ++
        (List.range 25).map fun i => .ldr .x (laneReg i) .x30 (8*i))) u fun u' =>
      u'.mem = u.mem ∧ u'.v = u.v ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      Lanes u' (stateAt u.mem (u.gpr .x1)) := by
  refine WP.cons (exec_addImm_x (by decide)) ?_
  have hb : (u.write .x .x30 (u.read .x .x1 + BitVec.ofNat _ 0)).gpr .x30 = u.gpr .x1 := by
    simp only [RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq,
      show BitVec.ofNat 64 0 = 0 by rfl]
    exact BitVec.add_zero _
  rw [List.map_eq_flatMap]
  refine (wp_range_flatMap (M := isa)
    (fun k x => x.mem = u.mem ∧ x.v = u.v ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
      x.gpr .x30 = u.gpr .x1 ∧
      ∀ j < k, x.gpr (laneReg j) = u.mem.readW (u.gpr .x1 + BitVec.ofNat 64 (8*j)) 64)
    (fun k x hk ⟨hm, hv, hr, hwr, hsp, h30, hl⟩ => ?_) 25 (Nat.le_refl _) (u.write .x .x30 (u.read .x .x1 + BitVec.ofNat _ 0))
    ⟨rfl, rfl, rfl, rfl, rfl, hb, fun _ h => absurd h (by omega)⟩).mono
    fun x ⟨hm, hv, hr, hwr, hsp, _, hl⟩ => ⟨hm, hv, hr, hwr, hsp, fun i hi => ?_⟩
  · refine WP.cons (exec_ldr_x ⟨by omega, by omega⟩ (by rw [hr, hwr, h30]; exact hin k hk))
      (WP.block_nil ⟨hm, hv, hr, hwr, hsp, ?_, fun j hj => ?_⟩)
    · rw [RegUpd.gpr_write_of_ne _ _ _ (Ne.symm (laneReg_ne_x30 k hk)), h30]
    · by_cases he : j = k
      · subst j
        simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, hm, h30]
      · rw [RegUpd.gpr_write_of_ne _ _ _ (fun h => he ((laneReg_inj j (by omega) k hk).mp h))]
        exact hl j (by omega)
  · simpa only [stateAt, Vector.getElem_ofFn] using hl i hi

/-- `q8`–`q15` back from `x2`. -/
theorem scr_restore_ok {s₀ u : State} {q : Addr} (hq : u.gpr .x2 = q) (hs : Saved s₀ q u.mem)
    (hin : ∀ i < 8, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 8).map fun i => Instr.ldrq (vreg (8 + i)) .x2 (16 * i))) u fun u' =>
      u'.gpr = u.gpr ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      ∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 := by
  have hh : WP isa (.block ((List.range 8).map fun i => Instr.ldrq (vreg (8 + i)) .x2 (16 * i))) u
      fun u' => u'.gpr = u.gpr ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
        ∀ i < 8, u'.v (vreg (8+i)) = s₀.v (vreg (8+i)) := by
    rw [List.map_eq_flatMap]
    refine wp_range_flatMap (M := isa)
      (fun k x => x.gpr = u.gpr ∧ x.mem = u.mem ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
        ∀ i < k, x.v (vreg (8+i)) = s₀.v (vreg (8+i)))
      (fun k x hk ⟨hg, hm, hr, hwr, hsp, hvals⟩ => ?_) 8 (Nat.le_refl _) u
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩
    refine WP.cons (exec_ldrq ⟨by omega, by omega⟩ ?_) (WP.block_nil ?_)
    · rw [hr, hwr, hg, hq]; exact hin k hk
    refine ⟨by rw [RegUpd.gpr_setV, hg], by rw [RegUpd.mem_setV, hm], by rw [RegUpd.rd_setV, hr],
      by rw [RegUpd.wr_setV, hwr], by rw [RegUpd.sp_setV, hsp], fun i hi => ?_⟩
    rw [RegUpd.v_setV]
    simp only [vreg_inj (8+i) (by omega) (8+k) (by omega), Nat.add_left_cancel_iff]
    by_cases he : i = k
    · subst i
      simp only [ite_true, hm, hg, hq]
      exact hs k hk
    · rw [ite_eq_right (by omega)]
      exact hvals i (by omega)
  refine hh.mono fun u' ⟨hg, hm, hr, hwr, hsp, hv⟩ => ⟨hg, hm, hr, hwr, hsp, fun r hr' => ?_⟩
  have hv' : ∀ r ∈ preservedV, ∃ i : Fin 8, r = vreg (8+i.val) := by decide
  obtain ⟨i, rfl⟩ := hv' r hr'
  exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv i.val i.isLt)

/-- The callee-saved registers back from the frame. -/
theorem regs_restore_ok {s₀ u : State}
    (hs : ∀ i < 11, u.mem.readW (u.sp + BitVec.ofNat 64 (16 + 8 * i)) 64 =
      s₀.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i))
    (hin : ∀ i < 11, InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (16 + 8 * i)) 8) :
    WP isa (.block ((List.range 11).map fun i =>
        Instr.ldrSp (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) (16 + 8 * i))) u fun u' =>
      u'.v = u.v ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      ∀ i < 11, u'.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) =
        s₀.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k x => x.v = u.v ∧ x.mem = u.mem ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
      ∀ i < k, x.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) =
        s₀.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i))
    (fun k x hk ⟨hv, hm, hr, hwr, hsp, hvals⟩ => ?_) 11 (Nat.le_refl _) u
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega)⟩
  refine WP.cons (exec_ldrSp ⟨by omega, by omega⟩ (by rw [hr, hwr, hsp]; exact hin k hk))
    (WP.block_nil ⟨hv, hm, hr, hwr, hsp, fun i hi => ?_⟩)
  by_cases he : i = k
  · subst i
    simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, hm, hsp]
    exact hs k hk
  · rw [RegUpd.gpr_write_of_ne _ _ _ (fun h => he ((savedReg_inj i (by omega) k hk).mp h))]
    exact hvals i (by omega)

/-! ## The layout -/

/-- The frame. -/
def frR (sp : Addr) : Region := ⟨sp - BitVec.ofNat 64 128, 128⟩

/-- The frame's base. -/
abbrev Sb (s : State) : Addr := s.sp - BitVec.ofNat 64 128

/-- What the contract gives. -/
structure Lay (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [pairR (s.gpr .x0), stR (s.gpr .x1), scrR (s.gpr .x2)]
  d01 : (pairR (s.gpr .x0)).Disjoint (stR (s.gpr .x1))
  d02 : (pairR (s.gpr .x0)).Disjoint (scrR (s.gpr .x2))
  d12 : (stR (s.gpr .x1)).Disjoint (scrR (s.gpr .x2))
  sp : 128 ≤ s.sp.toNat
  f0 : (frR s.sp).Disjoint (pairR (s.gpr .x0))
  f1 : (frR s.sp).Disjoint (stR (s.gpr .x1))
  f2 : (frR s.sp).Disjoint (scrR (s.gpr .x2))

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem inP {i : Nat} (hi : i < 25) : InRegions s.wr (wordAddr (s.gpr .x0) i) 16 :=
  ⟨_, by rw [h.wr]; simp, pair_contains _ hi⟩

theorem inQ {i : Nat} (hi : i < 25) : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨stR (s.gpr .x1), by rw [h.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem inR {i : Nat} (hi : i < 8) : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (16 * i)) 16 :=
  ⟨scrR (s.gpr .x2), by rw [h.wr]; simp, scr_contains _ hi⟩

theorem sP : (slotR (Sb s)).Disjoint (pairR (s.gpr .x0)) := h.f0.sub_left (Offset.sub_base _ (by decide))
theorem sQ : (slotR (Sb s)).Disjoint (stR (s.gpr .x1)) := h.f1.sub_left (Offset.sub_base _ (by decide))
theorem sR : (slotR (Sb s)).Disjoint (scrR (s.gpr .x2)) := h.f2.sub_left (Offset.sub_base _ (by decide))

end Lay

theorem inF {s : State} {d n : Nat} (hd : d + n ≤ 128) :
    InRegions (frR s.sp :: s.wr) (Sb s + BitVec.ofNat 64 d) n :=
  ⟨frR s.sp, List.mem_cons_self .., Offset.contains_base _ hd (by omega)⟩

theorem inW {s u : State} (hw : u.wr = frR s.sp :: s.wr) {a : Addr} {n : Nat} (h : InRegions s.wr a n) :
    InRegions u.wr a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, by rw [hw]; exact List.mem_cons_of_mem _ hr, hc⟩

theorem inW0 {r : Region} {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    InRegions (r :: rs) a n := by
  obtain ⟨r', hr, hc⟩ := h
  exact ⟨r', List.mem_cons_of_mem _ hr, hc⟩

theorem inRW {rd rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) : InRegions (rd ++ rs) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem slot_val {S : Addr} {s₀ : State} {m : Mem} (h : SlotsAt S s₀ m) (j : Nat) (hj : j < 14) {off : Nat}
    (ho : 16 + 8 * j = off) : m.readW (S + BitVec.ofNat 64 off) 64 = s₀.gpr (slotReg j) :=
  ho ▸ h j hj

/-! ## The phases -/

/-- After the saves, the loads and the rounds. -/
structure Mid (s u : State) : Prop where
  sp : u.sp = Sb s
  rd : u.rd = s.rd
  wr : u.wr = frR s.sp :: s.wr
  pairs : Pairs u (keccakF (stateX2At s.mem (s.gpr .x0) 0)) (keccakF (stateX2At s.mem (s.gpr .x0) 1))
  lanes : Lanes u (keccakF (stateAt s.mem (s.gpr .x1)))
  slots : SlotsAt (Sb s) s u.mem
  saved : Saved s (s.gpr .x2) u.mem

theorem save_eq : Impl.Sha3.AArch64.Hybrid.X3.save =
    (List.range 14).map (fun j => Instr.strSp (slotReg j) (16 + 8 * j)) ++
      (List.range 8).map (fun i => Instr.strq (vreg (8 + i)) .x2 (16 * i)) := by
  rfl

theorem front_ok {s : State} (h : Lay s) :
    WP isa (.block (Impl.Sha3.AArch64.Hybrid.X3.save ++ Impl.Sha3.AArch64.Hybrid.X3.load ++
      Impl.Sha3.AArch64.Hybrid.rounds 0)) (allocated 128 s) (Mid s) := by
  rw [show Impl.Sha3.AArch64.Hybrid.X3.save ++ Impl.Sha3.AArch64.Hybrid.X3.load ++
      Impl.Sha3.AArch64.Hybrid.rounds 0 =
      (List.range 14).map (fun j => Instr.strSp (slotReg j) (16 + 8 * j)) ++
      ((List.range 8).map (fun i => Instr.strq (vreg (8 + i)) .x2 (16 * i)) ++
      (Impl.Sha3.AArch64.Neon.Pair.load .x0 ++
      ((([.addImm .x .x30 .x1 0] : List Instr) ++
        (List.range 25).map fun i => .ldr .x (laneReg i) .x30 (8*i)) ++
      Impl.Sha3.AArch64.Hybrid.rounds 0))) from by
    rw [save_eq]; simp only [Impl.Sha3.AArch64.Hybrid.X3.load, List.append_assoc]]
  rw [WP.block_append_iff]
  refine (slots_ok (u := allocated 128 s) (fun j hj => inF (by omega))).mono
    fun u₁ ⟨g₁, v₁, r₁, w₁, sp₁, f₁, sl₁⟩ => ?_
  rw [WP.block_append_iff]
  refine (scr_save_ok (q := s.gpr .x2) (by rw [g₁]; rfl) (fun i hi => by rw [w₁]; exact inW0 (h.inR hi))).mono
    fun u₂ ⟨g₂, v₂, r₂, w₂, sp₂, f₂, sv₂⟩ => ?_
  have f₁' : Frame [slotR (Sb s)] s.mem u₁.mem := f₁
  have sl₂ : SlotsAt (Sb s) s u₂.mem := SlotsAt.frame sl₁ f₂ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sR
  have sv₂' : Saved s (s.gpr .x2) u₂.mem := fun i hi => (sv₂ i hi).trans (by rw [v₁]; rfl)
  have wr₂ : u₂.wr = frR s.sp :: s.wr := by rw [w₂, w₁]; rfl
  have hpair : PairAt u₂.mem (s.gpr .x0) (stateX2At s.mem (s.gpr .x0) 0) (stateX2At s.mem (s.gpr .x0) 1) :=
    pairAt_frame (pairAt_frame (pairAt_stateX2 s.mem _) f₁' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sP.symm) f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d02
  rw [WP.block_append_iff]
  refine (Neon.load_ok (r := .x0) (by rw [g₂, g₁]; rfl) hpair
    (fun i hi => inRW (inW wr₂ (h.inP hi)))).mono fun u₃ ⟨c₃, ps₃⟩ => ?_
  rw [WP.block_append_iff]
  have hq₃ : u₃.gpr .x1 = s.gpr .x1 := by rw [c₃.gpr, g₂, g₁]; rfl
  refine (lanes_ok u₃ (fun i hi => by rw [hq₃, c₃.rd, c₃.wr]; exact inRW (inW wr₂ (h.inQ hi)))).mono
    fun u₄ ⟨m₄, v₄, r₄, w₄, sp₄, ln₄⟩ => ?_
  have hst : stateAt u₃.mem (u₃.gpr .x1) = stateAt s.mem (s.gpr .x1) := by
    rw [hq₃, c₃.mem, stateAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d12),
      stateAt_frame f₁' (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sQ.symm)]
  rw [hst] at ln₄
  have sp₄' : u₄.sp = Sb s := by rw [sp₄, c₃.sp, sp₂, sp₁]; rfl
  have wr₄ : u₄.wr = frR s.sp :: s.wr := by rw [w₄, c₃.wr, wr₂]
  have ps₄ : Pairs u₄ (stateX2At s.mem (s.gpr .x0) 0) (stateX2At s.mem (s.gpr .x0) 1) :=
    fun i hi => by rw [v₄]; exact ps₃ i hi
  refine (rounds_ok (off := 0) ps₄ ln₄ ⟨by decide, by decide, fun k hk => by
    rw [wr₄, sp₄']; exact inF (by omega)⟩).mono fun t ⟨pt, lt, spt, rdt, wrt, ft⟩ => ?_
  rw [sp₄'] at ft
  have m₄' : u₄.mem = u₂.mem := by rw [m₄, c₃.mem]
  exact ⟨by rw [spt, sp₄'], by rw [rdt, r₄, c₃.rd, r₂, r₁]; rfl, by rw [wrt, wr₄], pt, lt,
    SlotsAt.frame (m₄' ▸ sl₂) ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by decide) (by decide),
    Saved.frame (m₄' ▸ sv₂') ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.f2.symm.sub_right (Region.sub_prefix (by decide))⟩
/-- The state's pointer back in `x30`. -/
theorem b1_ok {s u : State} (m : Mid s u) :
    WP isa (.block [.ldrSp .x30 112]) u fun u' => Mid s u' ∧ u'.gpr .x30 = s.gpr .x1 := by
  refine WP.cons (exec_ldrSp ⟨by decide, by decide⟩ (by rw [m.sp, m.wr]; exact inRW (inF (d := _) (n := 8) (by decide))))
    (WP.block_nil ⟨⟨m.sp, m.rd, m.wr, m.pairs, fun i hi => ?_, m.slots, m.saved⟩, ?_⟩)
  · rw [RegUpd.gpr_write_of_ne _ _ _ (laneReg_ne_x30 i hi)]; exact m.lanes i hi
  · simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, m.sp]
    exact slot_val m.slots 12 (by decide) rfl

/-- After the store of the third state. -/
structure Mid2 (s u : State) : Prop where
  sp : u.sp = Sb s
  rd : u.rd = s.rd
  wr : u.wr = frR s.sp :: s.wr
  pairs : Pairs u (keccakF (stateX2At s.mem (s.gpr .x0) 0)) (keccakF (stateX2At s.mem (s.gpr .x0) 1))
  slots : SlotsAt (Sb s) s u.mem
  saved : Saved s (s.gpr .x2) u.mem
  st : stateAt u.mem (s.gpr .x1) = keccakF (stateAt s.mem (s.gpr .x1))

/-- The third state stored, and the states' pointer back in `x0`. -/
theorem b2_ok {s u : State} (h : Lay s) (m : Mid s u) (h30 : u.gpr .x30 = s.gpr .x1) :
    WP isa (.block ((List.range 25).map (fun i => Instr.str .x (laneReg i) .x30 (8 * i)) ++
      ([.ldrSp .x0 104] : List Instr))) u fun u' => Mid2 s u' ∧ u'.gpr .x0 = s.gpr .x0 := by
  rw [WP.block_append_iff]
  refine (store_words_ok u _ m.lanes (fun i hi => by rw [h30, m.wr]; exact inW0 (h.inQ hi))).mono
    fun x hx => ?_
  have fx : Frame [stR (s.gpr .x1)] u.mem x.mem := by rw [← h30]; exact hx.frame
  have sl : SlotsAt (Sb s) s x.mem := SlotsAt.frame m.slots fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sQ
  have sv : Saved s (s.gpr .x2) x.mem := Saved.frame m.saved fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.d12.symm
  have spx : x.sp = Sb s := by rw [hx.keep.sp, m.sp]
  have wrx : x.wr = frR s.sp :: s.wr := by rw [hx.keep.wr, m.wr]
  refine WP.cons (exec_ldrSp ⟨by decide, by decide⟩ (by rw [spx, wrx]; exact inRW (inF (d := _) (n := 8) (by decide))))
    (WP.block_nil ⟨⟨spx, by rw [RegUpd.rd_write, hx.keep.rd, m.rd], wrx,
      fun i hi => by rw [RegUpd.v_write, hx.vec]; exact m.pairs i hi, sl, sv, ?_⟩, ?_⟩)
  · apply Vector.ext
    intro i hi
    simpa only [stateAt, Vector.getElem_ofFn, h30, RegUpd.mem_write] using hx.vals i hi hi
  · simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, spx]
    exact slot_val sl 11 (by decide) rfl

/-- After the store of the interleaved states. -/
structure Mid3 (s u : State) : Prop where
  sp : u.sp = Sb s
  rd : u.rd = s.rd
  wr : u.wr = frR s.sp :: s.wr
  slots : SlotsAt (Sb s) s u.mem
  saved : Saved s (s.gpr .x2) u.mem
  st : stateAt u.mem (s.gpr .x1) = keccakF (stateAt s.mem (s.gpr .x1))
  pa : PairAt u.mem (s.gpr .x0) (keccakF (stateX2At s.mem (s.gpr .x0) 0))
    (keccakF (stateX2At s.mem (s.gpr .x0) 1))

/-- The interleaved states stored, and the working space's pointer back in `x2`. -/
theorem b3_ok {s u : State} (h : Lay s) (m : Mid2 s u) (h0 : u.gpr .x0 = s.gpr .x0) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.store .x0 ++ ([.ldrSp .x2 120] : List Instr))) u
      fun u' => Mid3 s u' ∧ u'.gpr .x2 = s.gpr .x2 := by
  rw [WP.block_append_iff]
  refine (Neon.store_ok h0 m.pairs (fun i hi => by rw [m.wr]; exact inW0 (h.inP hi))).mono
    fun x ⟨vx, pax, fx⟩ => ?_
  have sl : SlotsAt (Sb s) s x.mem := SlotsAt.frame m.slots fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sP
  have sv : Saved s (s.gpr .x2) x.mem := Saved.frame m.saved fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.d02.symm
  have spx : x.sp = Sb s := by rw [vx.sp, m.sp]
  have wrx : x.wr = frR s.sp :: s.wr := by rw [vx.wr, m.wr]
  refine WP.cons (exec_ldrSp ⟨by decide, by decide⟩ (by rw [spx, wrx]; exact inRW (inF (d := _) (n := 8) (by decide))))
    (WP.block_nil ⟨⟨spx, by rw [RegUpd.rd_write, vx.rd, m.rd], wrx, sl, sv, ?_, pax⟩, ?_⟩)
  · rw [RegUpd.mem_write, stateAt_frame fx (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d01.symm)]
    exact m.st
  · simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, spx]
    exact slot_val sl 13 (by decide) rfl

/-- `q8`–`q15` and the callee-saved registers restored. -/
theorem b4_ok {s u : State} (h : Lay s) (m : Mid3 s u) (h2 : u.gpr .x2 = s.gpr .x2) :
    WP isa (.block ((List.range 8).map (fun i => Instr.ldrq (vreg (8 + i)) .x2 (16 * i)) ++
      (List.range 11).map (fun i =>
        Instr.ldrSp (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) (16 + 8 * i)))) u fun t =>
      t.sp = Sb s ∧ t.mem = u.mem ∧
      (∀ i < 11, t.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) =
        s.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i)) ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  rw [WP.block_append_iff]
  refine (scr_restore_ok h2 m.saved (fun i hi => by rw [m.wr]; exact inRW (inW0 (h.inR hi)))).mono
    fun x ⟨_, mx, rx, wx, spx, vx⟩ => ?_
  refine (regs_restore_ok (s₀ := s) (fun i hi => ?_) (fun i hi => ?_)).mono
    fun t ⟨vt, mt, _, _, spt, gt⟩ => ⟨by rw [spt, spx, m.sp], by rw [mt, mx], gt,
      fun r hr => by rw [vt]; exact vx r hr⟩
  · rw [mx, spx, m.sp, savedReg_slot i hi]; exact m.slots i (by omega)
  · rw [rx, wx, spx, m.wr, m.sp]; exact inRW (inF (by omega))

theorem body_eq : Impl.Sha3.AArch64.Hybrid.X3.body =
    (Impl.Sha3.AArch64.Hybrid.X3.save ++ Impl.Sha3.AArch64.Hybrid.X3.load ++
      Impl.Sha3.AArch64.Hybrid.rounds 0) ++
    (([.ldrSp .x30 112] : List Instr) ++
    (((List.range 25).map (fun i => Instr.str .x (laneReg i) .x30 (8 * i)) ++
      ([.ldrSp .x0 104] : List Instr)) ++
    ((Impl.Sha3.AArch64.Neon.Pair.store .x0 ++ ([.ldrSp .x2 120] : List Instr)) ++
    ((List.range 8).map (fun i => Instr.ldrq (vreg (8 + i)) .x2 (16 * i)) ++
      (List.range 11).map (fun i =>
        Instr.ldrSp (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) (16 + 8 * i)))))) := by
  simp only [Impl.Sha3.AArch64.Hybrid.X3.body, Impl.Sha3.AArch64.Hybrid.X3.store,
    Impl.Sha3.AArch64.Hybrid.X3.restore, List.append_assoc]

/-! ## The contract -/

/-- The contract on the states at `x0` and `x1`, the working space at `x2` and
the 128 bytes of stack below `sp`. -/
def K : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [pairR (s.gpr .x0), stR (s.gpr .x1), scrR (s.gpr .x2)] ∧
    (pairR (s.gpr .x0)).Disjoint (stR (s.gpr .x1)) ∧ (pairR (s.gpr .x0)).Disjoint (scrR (s.gpr .x2)) ∧
    (stR (s.gpr .x1)).Disjoint (scrR (s.gpr .x2)) ∧ 128 ≤ s.sp.toNat ∧
    (frR s.sp).Disjoint (pairR (s.gpr .x0)) ∧ (frR s.sp).Disjoint (stR (s.gpr .x1)) ∧
    (frR s.sp).Disjoint (scrR (s.gpr .x2))
  post s s' := stateX2At s'.mem (s.gpr .x0) 0 = keccakF (stateX2At s.mem (s.gpr .x0) 0) ∧
    stateX2At s'.mem (s.gpr .x0) 1 = keccakF (stateX2At s.mem (s.gpr .x0) 1) ∧
    stateAt s'.mem (s.gpr .x1) = keccakF (stateAt s.mem (s.gpr .x1))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

theorem lay {s : State} (h : K.pre s) : Lay s :=
  let ⟨a, b, c, d, e, f, g, i, j⟩ := h
  ⟨a, b, c, d, e, f, g, i, j⟩

/-- The body, in the frame. -/
theorem body_ok {s : State} (h : Lay s) :
    WP isa (.block Impl.Sha3.AArch64.Hybrid.X3.body) (allocated 128 s) fun t =>
      abiPreserved s (freed 128 t) ∧ K.post s (freed 128 t) := by
  rw [body_eq, WP.block_append_iff]
  refine (front_ok h).mono fun u m => ?_
  rw [WP.block_append_iff]
  refine (b1_ok m).mono fun u₁ ⟨m₁, h30⟩ => ?_
  rw [WP.block_append_iff]
  refine (b2_ok h m₁ h30).mono fun u₂ ⟨m₂, h0⟩ => ?_
  rw [WP.block_append_iff]
  refine (b3_ok h m₂ h0).mono fun u₃ ⟨m₃, h2⟩ => ?_
  refine (b4_ok h m₃ h2).mono fun t ⟨spt, mt, gt, vt⟩ => ⟨⟨fun r hr => ?_, ?_, vt⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := preserved_saved r hr
    exact gt i hi
  · show t.sp + BitVec.ofNat 64 128 = s.sp
    rw [spt]
    exact BitVec.sub_add_cancel _ _
  · obtain ⟨e0, e1⟩ := stateX2_of_pairAt m₃.pa
    show stateX2At t.mem _ 0 = _ ∧ stateX2At t.mem _ 1 = _ ∧ stateAt t.mem _ = _
    rw [mt]
    exact ⟨e0, e1, m₃.st⟩

theorem correct (s : State) (hs : K.pre s) :
    ∃ tr t, Exec isa X3code s tr t ∧ abiPreserved s t ∧ K.post s t :=
  WP.alloc ⟨by decide, by decide, by decide⟩ (lay hs).sp (body_ok (lay hs))

theorem allocated_gpr (n : Nat) (s : State) : (allocated n s).gpr = s.gpr := rfl

theorem ct : ConstantTime isa K.pre K.pub X3code := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ ⟨q0, q1, q2, qsp⟩ => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  have hS : Sb σ₁ = Sb σ₂ := by simp only [Sb, qsp]
  refine (RelCT.alloc (P := Eq2 σ₁ σ₂) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocated 128 σ₁) (allocated 128 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rw [body_eq]
  -- The saves, the loads and the rounds, from the three pointers.
  refine RelCT.block_split (rel_seq
    (rel_taint (c := (Code.block (Impl.Sha3.AArch64.Hybrid.X3.save ++
      Impl.Sha3.AArch64.Hybrid.X3.load ++ Impl.Sha3.AArch64.Hybrid.rounds 0) : Prog isa))
      (σ₁ := allocated 128 σ₁) (σ₂ := allocated 128 σ₂) [.x0, .x1, .x2]
      (by show σ₁.sp - _ = σ₂.sp - _; rw [qsp])
      (by agree_tac [allocated_gpr, q0, q1, q2]) ⟨_, by taint_decide⟩)
    (front_ok h₁) (front_ok h₂) fun u₁ u₂ m₁ m₂ => ?_)
  -- The state's pointer, from the frame.
  refine RelCT.block_split (rel_seq (rel_taint [] (by rw [m₁.sp, m₂.sp, hS]) (by agree_tac [])
    ⟨_, by taint_decide⟩) (b1_ok m₁) (b1_ok m₂) fun x₁ x₂ ⟨n₁, a₁⟩ ⟨n₂, a₂⟩ => ?_)
  -- The third state's store, from it.
  refine RelCT.block_split (rel_seq (rel_taint [.x30] (by rw [n₁.sp, n₂.sp, hS])
    (by agree_tac [a₁, a₂, q1]) ⟨_, by taint_decide⟩) (b2_ok h₁ n₁ a₁) (b2_ok h₂ n₂ a₂)
    fun y₁ y₂ ⟨k₁, c₁⟩ ⟨k₂, c₂⟩ => ?_)
  -- The interleaved states' store.
  refine RelCT.block_split (rel_seq (rel_taint [.x0] (by rw [k₁.sp, k₂.sp, hS])
    (by agree_tac [c₁, c₂, q0]) ⟨_, by taint_decide⟩) (b3_ok h₁ k₁ c₁) (b3_ok h₂ k₂ c₂)
    fun z₁ z₂ ⟨l₁, d₁⟩ ⟨l₂, d₂⟩ => ?_)
  -- The restores.
  exact rel_taint [.x2] (by rw [l₁.sp, l₂.sp, hS]) (by agree_tac [d₁, d₂, q2]) ⟨_, by taint_decide⟩

/-- A state the precondition holds in. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 400⟩, ⟨0x2000, 200⟩, ⟨0x3000, 128⟩]

theorem verified :
    Verified AArch64.target X3code (Proof.Sha3.permuteX3Contract AArch64.abi 128) :=
  Verified.of_correct correct ct (by
    sig_implies [Proof.Sha3.permuteX3Contract, Proof.Sha3.permuteX3Sig, K, pairR, stR, scrR,
      Neon.X2.scrR, frR, AArch64.abi, AArch64.argRegs] [satState] using satState)

end VG.Proof.Sha3.AArch64.Hybrid.X3
