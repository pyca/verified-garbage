import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentMask

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
