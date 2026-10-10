import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentMask

/-! ## From `ResidentSaveG.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64 (wp_str Mupd)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

/-- Save the ten nonvolatile scalar registers in the selected scratch tail. -/
theorem saveG_ok (s : State)
    (hw : ∀ i<10, InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (7968+8*i)) 8) :
    WP isa (.block ((List.range 10).map fun i => .str .x (saved[i]!) .x4 (7968+8*i))) s
      fun t => Mupd s t t.mem ∧ Frame [⟨s.gpr .x4+7968,80⟩] s.mem t.mem ∧
        ∀ i<10, t.mem.readW (s.gpr .x4+BitVec.ofNat 64 (7968+8*i)) 64=s.gpr (saved[i]!) := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Mupd s t t.mem ∧ Frame [⟨s.gpr .x4+7968,80⟩] s.mem t.mem ∧
      ∀ i<k, t.mem.readW (s.gpr .x4+BitVec.ofNat 64 (7968+8*i)) 64=s.gpr (saved[i]!))
    (fun k t hk ⟨ht,hf,hvals⟩ => ?_) 10 (Nat.le_refl _) s
    ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_str (a := s.gpr .x4+BitVec.ofNat 64 (7968+8*k)) ⟨by omega,by omega⟩
    (by rw [ht.gpr]) (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨hu.gpr.trans ht.gpr,rfl,hu.rd.trans ht.rd,hu.wr.trans ht.wr,
      hu.sp.trans ht.sp,hu.vec.trans ht.vec⟩
  · rw [hu.mem]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains (s.gpr .x4) (d := 7968+8*k) (e := 7968) (n := 8) (k := 80)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hu.mem,ht.gpr]
    by_cases he : i=k
    · subst i; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .x4)
        (d := 7968+8*i) (e := 7968+8*k) (n := 8) (k := 8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact hvals i (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentSaveV.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (Upd wp_str WP.cons)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

private theorem saveV_step (s : State) {i : Nat} (hi : i<8)
    (hw : InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x4 (8048+8*i)]) s fun t =>
      RegKeep [.x8] s t ∧ t.v=s.v ∧
      t.mem=s.mem.writeW (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) (vdword (s.v (vreg (8+i))) 0) := by
  refine WP.cons (s' := s.write .x .x8 (vdword (s.v (vreg (8+i))) 0)) rfl ?_
  have h1 := Upd.write64 s .x8 (vdword (s.v (vreg (8+i))) 0)
  refine wp_str ⟨by omega,by omega⟩ (by rw [h1.other .x4 (by decide)])
    (by rw [h1.wr]; exact hw) fun t h2 => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact (RegKeep.upd h1).trans (RegKeep.mupd h2) |>.mono (by simp)
  · exact h2.vec.trans h1.vec
  · rw [h2.mem,h1.mem,h1.gpr]

theorem saveV_ok (s : State)
    (hw : ∀ i<8, InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block ((List.range 8).flatMap fun i =>
      [.umov .x .x8 (vreg (8+i)) 0,.str .x .x8 .x4 (8048+8*i)])) s fun t =>
      RegKeep [.x8] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x4+8048,64⟩] s.mem t.mem ∧
      ∀ i<8, t.mem.readW (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) 64=vdword (s.v (vreg (8+i))) 0 := by
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x4+8048,64⟩] s.mem t.mem ∧
      ∀ i<k, t.mem.readW (s.gpr .x4+BitVec.ofNat 64 (8048+8*i)) 64=vdword (s.v (vreg (8+i))) 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (saveV_step t hk (by rw [ht.wr,ht.gpr .x4 (by decide)]; exact hw k hk)) ?_
  intro u ⟨hu,hvu,hm⟩
  rw [ht.gpr .x4 (by decide)] at hm
  refine ⟨(ht.trans hu).mono (by simp),hvu.trans hv,?_,?_⟩
  · rw [hm]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains (s.gpr .x4) (d := 8048+8*k) (e := 8048) (n := 8) (k := 64)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hm,hv]
    by_cases he : i=k
    · subst i; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .x4)
        (d := 8048+8*i) (e := 8048+8*k) (n := 8) (k := 8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact hvals i (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentRestoreV.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Proof.MlKem.AArch64 (wp_vop)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

private theorem low_setLane (v : BitVec 128) (a : BitVec 64) :
    vdword (setLane v 64 0 a) 0=a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword,setLane,BitVec.getLsbD_extractLsb',BitVec.getLsbD_or,
    BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth,BitVec.getLsbD_allOnes]
  simp (disch := omega) [hi,decide_eq_true]

private theorem restoreV_step (s : State) {i : Nat} (hi : i<8)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block [.ldr .x .x8 .x19 (8048+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)]) s
      fun t => RegKeep [.x8] s t ∧ t.mem=s.mem ∧
        vdword (t.v (vreg (8+i))) 0=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 64 ∧
        ∀ r, r≠vreg (8+i) → t.v r=s.v r := by
  refine wp_ldr ⟨by omega,by omega⟩ rfl hin fun u h1 => ?_
  refine wp_vop (d := vreg (8+i)) rfl fun t h2 => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact ((RegKeep.upd h1).trans (RegKeep.vupd h2)).mono (by simp)
  · exact h2.mem.trans h1.mem
  · rw [h2.v,low_setLane,h1.gpr]
  · intro r hr; rw [h2.other r hr,h1.vec]

/-- Restore precisely the ABI-preserved low halves of v8 through v15. -/
theorem restoreV_ok (s : State)
    (hr : ∀ i<8, InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 8) :
    WP isa (.block ((List.range 8).flatMap fun i =>
      [.ldr .x .x8 .x19 (8048+8*i),.vop (.ins .d2 (vreg (8+i)) 0 .x8)])) s
      fun t => RegKeep [.x8] s t ∧ t.mem=s.mem ∧
        ∀ i<8, vdword (t.v (vreg (8+i))) 0=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 64 := by
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.mem=s.mem ∧
      ∀ i<k, vdword (t.v (vreg (8+i))) 0=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (8048+8*i)) 64)
    (fun k t hk ⟨ht,hm,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (restoreV_step t hk (by rw [ht.rd,ht.wr,ht.gpr .x19 (by decide)]; exact hr k hk)) ?_
  intro u ⟨hu,hmu,hvu,hother⟩
  refine ⟨(ht.trans hu).mono (by simp),hmu.trans hm,fun i hi => ?_⟩
  by_cases heq : i=k
  · subst i; rw [hvu,hm,ht.gpr .x19 (by decide)]
  · rw [hother (vreg (8+i)) (fun he => heq (by
      have hv := (vreg_inj (8+i) (by omega) (8+k) (by omega)).mp he
      omega))]
    exact hvals i (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentRestoreG.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only wp_ldrx)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (saved)

private theorem saved_inj : ∀ i<10, ∀ j<10, saved[i]! = saved[j]! ↔ i=j := by decide
private theorem saved_ne19 : ∀ i<9, saved[i+1]! ≠ Reg.x19 := by decide

/-- Restore x20 through x28 before restoring the scratch base in x19. -/
theorem restoreG_ok (s : State)
    (hr : ∀ i<9, InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (7976+8*i)) 8) :
    WP isa (.block ((List.range 9).map fun i => .ldr .x (saved[i+1]!) .x19 (7976+8*i))) s
      fun t => Only (saved.drop 1) s t ∧
        ∀ i<9, t.gpr (saved[i+1]!)=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (7976+8*i)) 64 := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Only (saved.drop 1) s t ∧
      ∀ i<k, t.gpr (saved[i+1]!)=s.mem.readW (s.gpr .x19+BitVec.ofNat 64 (7976+8*i)) 64)
    (fun k t hk ⟨ht,hvals⟩ => ?_) 9 (Nat.le_refl _) s
    ⟨Only.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  have h19 : t.gpr .x19=s.gpr .x19 := ht.get .x19 (by decide)
  refine wp_ldrx ⟨by omega,by omega⟩ (by rw [h19])
    (by rw [ht.rd,ht.wr]; exact hr k hk) fun u hu eu => WP.block_nil_iff.mpr ⟨?_,fun i hi => ?_⟩
  · exact (ht.trans hu).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · rw [List.mem_singleton.mp hr]
        have hm : ∀ j<9, saved[j+1]! ∈ saved.drop 1 := by decide
        exact hm k hk)
  · by_cases heq : i=k
    · subst i; rw [eu,ht.mem]
    · rw [hu.get (saved[i+1]!) (by
        simp only [List.mem_singleton,saved_inj (i+1) (by omega) (k+1) (by omega)]
        omega)]
      exact hvals i (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
