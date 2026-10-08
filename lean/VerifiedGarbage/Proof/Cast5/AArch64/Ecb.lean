import VerifiedGarbage.Proof.Cast5.AArch64.Block

/-!
# CAST5 on AArch64: ECB

`ecb blk` runs the block function `blk` once for each block (`ecb_ok`).
-/

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64
open VG.Impl.Cast5 (table s1234 s5678 s1234Sym s5678Sym ecbConsts)
open VG.Proof.MlKem.AArch64 (Keep eval_zero eval_nonzero)

/-- The facts of the ECB functions' precondition on this target (the shared
contract's, `Spec.Cast5.ecbContract`, with the table `VG_CAST5_S1234`). -/
structure EPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x0, 128⟩, ⟨s.syms s1234Sym, 4096⟩]
  wr : s.wr = [⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩, ⟨s.gpr .x4, 256⟩]
  held : ∀ i < 512, s.mem.readW (s.syms s1234Sym + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 64
  dTD : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩
  dTS : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.gpr .x4, 256⟩
  dKD : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩
  dKS : Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x4, 256⟩
  dDS : Region.Disjoint ⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩ ⟨s.gpr .x4, 256⟩
  fK : (s.gpr .x0).toNat + 128 ≤ 2 ^ 64
  fD : (s.gpr .x2).toNat + (s.gpr .x3).toNat * 8 ≤ 2 ^ 64
  fS : (s.gpr .x4).toNat + 256 ≤ 2 ^ 64
  rounds : (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 16

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (p : Addr)
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : Spec.Cast5.blockAt m' p = Spec.Cast5.blockAt m p := by
  apply Vector.ext
  intro i hi
  rw [blockAt_get _ _ hi, blockAt_get _ _ hi]
  exact hf.bytes hd (by change 8 ≤ 2 ^ 64; decide) hi

/-- The state of the ECB loop with `b` blocks done, from `s`, each block `x`
replaced with `f x`. -/
structure LInv (s : State) (f : Spec.Cast5.Block → Spec.Cast5.Block) (b : Nat) (u : State) : Prop where
  x0 : u.gpr .x0 = s.gpr .x0
  x1 : u.gpr .x1 = s.gpr .x1
  x2 : u.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 (8 * b)
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms
  frame : Frame [⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩] s.mem u.mem
  data : ∀ j < (s.gpr .x3).toNat,
    Spec.Cast5.blockAt u.mem (s.gpr .x2 + BitVec.ofNat 64 (8 * j)) =
      if j < b then f (Spec.Cast5.blockAt s.mem (s.gpr .x2 + BitVec.ofNat 64 (8 * j)))
      else Spec.Cast5.blockAt s.mem (s.gpr .x2 + BitVec.ofNat 64 (8 * j))

theorem one_disj {R D : Region} (h : R.Disjoint D) : ∀ r ∈ [D], R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hr]; exact h

/-- A block's precondition, inside the loop. -/
theorem LInv.bpre {s u : State} (h : EPre s) {f : Spec.Cast5.Block → Spec.Cast5.Block} {b : Nat}
    (hu : LInv s f b u) (hb : b < (s.gpr .x3).toNat) :
    BPre u (Spec.Cast5.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x1).toNat := by
  refine ⟨⟨?_, fun j hj => ?_, ?_, fun i hi => ?_⟩, h.rounds, ?_, ?_⟩
  · rw [hu.rd, hu.wr, hu.x0, h.rd]
    exact ⟨_, List.mem_append_left _ List.mem_cons_self, Region.contains_self _ _⟩
  · rw [hu.x0, scheduleAt_getD _ _ hj, hu.frame.readW (r := ⟨s.gpr .x0, 128⟩)
      (Offset.contains_base _ (by omega) (by omega)) (one_disj h.dKD) (by decide)]
  · unfold Readable; rw [hu.rd, hu.wr, hu.syms, h.rd]
    exact ⟨_, List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self), Region.contains_self _ _⟩
  · rw [s1234_length] at hi
    rw [hu.syms, hu.frame.readW (r := ⟨s.syms s1234Sym, 4096⟩)
      (Offset.contains_base _ (by omega) (by omega)) (one_disj h.dTD) (by decide)]
    exact h.held i hi
  · rw [hu.x1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hu.wr, hu.x2, h.wr]
    exact ⟨_, List.mem_cons_self, Offset.contains_base _ (by omega) (by have := h.fD; omega)⟩

/-- The loop's step: a block function run on block `b`. -/
theorem LInv.step {s u v : State} (h : EPre s) {f : Spec.Cast5.Block → Spec.Cast5.Block} {b : Nat}
    (hu : LInv s f b u) (hb : b < (s.gpr .x3).toNat)
    (hv : BPost u (f (Spec.Cast5.blockAt u.mem (u.gpr .x2))) v) : LInv s f (b + 1) v := by
  obtain ⟨vout, vf, vdx, _, vrd, vwr, vsy, vg⟩ := hv
  have hN := h.fD
  have sD : Region.Sub ⟨u.gpr .x2, 8⟩ ⟨s.gpr .x2, (s.gpr .x3).toNat * 8⟩ := by
    rw [hu.x2]; exact Offset.sub_base _ (by omega)
  refine ⟨(vg .x0 (by decide) (by decide) (by decide)).trans hu.x0,
    (vg .x1 (by decide) (by decide) (by decide)).trans hu.x1, ?_, vrd.trans hu.rd,
    vwr.trans hu.wr, vsy.trans hu.syms, ?_, fun j hj => ?_⟩
  · rw [vdx, hu.x2, add_ofNat_add, Nat.mul_succ]
  · refine hu.frame.trans (vf.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]
    exact ⟨_, List.mem_cons_self, sD⟩
  · by_cases hjb : j = b
    · subst hjb
      have hd := hu.data j hj
      rw [ite_eq_right (Nat.lt_irrefl _)] at hd
      rw [ite_eq_left (Nat.lt_succ_self _), ← hd, ← hu.x2, vout]
    · rw [blockAt_frame vf _ (one_disj (by rw [hu.x2]; exact Offset.disjoint _ (by omega) (by omega) (by omega))),
        hu.data j hj]
      by_cases hjl : j < b
      · rw [ite_eq_left hjl, ite_eq_left (by omega)]
      · rw [ite_eq_right hjl, ite_eq_right (by omega)]

theorem toNat_eq_zero_of_beq {x : BitVec 64} (h : (x == 0) = true) : x.toNat = 0 := by
  rw [beq_iff_eq] at h; rw [h]; rfl

/-- `ecb blk`, for a block function `blk` that replaces the block `x` at `x2`
with `f k n x`. -/
theorem ecb_ok {blk : Prog isa} {f : Spec.Cast5.Schedule → Nat → Spec.Cast5.Block → Spec.Cast5.Block}
    (hblk : ∀ u k n, BPre u k n → WP isa blk u (BPost u (f k n (Spec.Cast5.blockAt u.mem (u.gpr .x2)))))
    (s : State) (h : EPre s) :
    WP isa (ecb blk) s fun t =>
      Spec.Cast5.blocksAt t.mem (s.gpr .x2) (s.gpr .x3).toNat =
        (Spec.Cast5.blocksAt s.mem (s.gpr .x2) (s.gpr .x3).toNat).map
          (f (Spec.Cast5.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x1).toNat) := by
  let F := f (Spec.Cast5.scheduleAt s.mem (s.gpr .x0)) (s.gpr .x1).toNat
  have h0 : LInv s F 0 s :=
    ⟨rfl, rfl, by rw [Nat.mul_zero, BitVec.add_zero], rfl, rfl, rfl, Frame.refl _ _,
      fun j _ => by rw [ite_eq_right (Nat.not_lt_zero _)]⟩
  have loop : WP isa (ecb blk) s (LInv s F (s.gpr .x3).toNat) := by
    unfold ecb
    refine WP.ite (s.gpr .x3 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
    · rw [toNat_eq_zero_of_beq hz]
      exact WP.block_nil h0
    · have hpos : 0 < (s.gpr .x3).toNat := by
        apply Nat.pos_of_ne_zero
        intro e
        have : s.gpr .x3 = 0 := BitVec.eq_of_toNat_eq e
        rw [this] at hz
        exact absurd hz (by decide)
      refine wp_countdown (cnt := .x3) (N := (s.gpr .x3).toNat) (s.gpr .x3).isLt hpos (LInv s F)
        (fun i hi v hv _ => WP.mono (hblk v _ _ (hv.bpre h hi)) fun w hw' => ?_) h0
        (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      exact ⟨hv.step h hi hw', hw'.2.2.2.1⟩
  refine WP.mono loop fun v hv => ?_
  simp only [Spec.Cast5.blocksAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  rw [Function.comp_apply, hv.data j (List.mem_range.mp hj), ite_eq_left (List.mem_range.mp hj)]

end VG.Proof.Cast5.AArch64
