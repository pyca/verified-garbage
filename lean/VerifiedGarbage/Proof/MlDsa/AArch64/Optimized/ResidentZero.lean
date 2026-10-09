import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentMask

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq VMem)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask (zero)

theorem zeros_ok {s : State} {p : Addr} (hp : s.gpr .x19 = p)
    (hw : ∀ i < 25, InRegions s.wr (wordAddr p i) 16) :
    WP isa (.block zero) s fun t => RegKeep [] s t ∧
      Frame [pairR p] s.mem t.mem ∧ ∀ i < 25, t.mem.read (wordAddr p i) 16 = 0 := by
  unfold zero
  rw [List.cons_append,WP.block_cons_iff]
  refine ⟨s.setV .v0 0,rfl,?_⟩
  have hz := VG.Proof.MlKem.AArch64.vupd_setV s .v0 0
  rw [List.nil_append,List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => RegKeep [] s t ∧ t.v .v0 = 0 ∧ Frame [pairR p] s.mem t.mem ∧
      ∀ i < k, t.mem.read (wordAddr p i) 16 = 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 25 (Nat.le_refl _) (s.setV .v0 0)
    ⟨RegKeep.vupd hz,hz.v,by rw [hz.mem]; exact Frame.refl _ _,
      fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun t ⟨ht,_,hf,hvals⟩ => ⟨ht,hf,hvals⟩
  refine wp_strq (a := wordAddr p k) (by omega)
    (by rw [ht.gpr .x19 (by simp),hp]; rfl)
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_,?_⟩
  · exact (ht.trans (RegKeep.vmem hu)).mono (by simp)
  · rw [hu.v]; exact hv
  · rw [hu.mem]
    exact hf.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))
  · intro i hi
    rw [hu.mem,hv]
    by_cases he : i = k
    · subst i; rw [read_write16]
    · have hsep : Mem.Sep (wordAddr p i) 16 (wordAddr p k) 16 :=
        Offset.sep p (d := 16*i) (e := 16*k) (n := 16) (k := 16) (by omega) (by omega) (by omega)
      rw [Mem.read_write_sep hsep (by decide)]
      exact hvals i (by omega)
end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
