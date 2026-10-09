import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallTry

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq VMem)
open VG.Impl.MlDsa.AArch64.Optimized.Ball (zeroWide)

def outputR (p : Addr) : Region := ⟨p,1024⟩

theorem zeroWide_ok {s : State} {p : Addr} (hp : s.gpr .x26 = p)
    (hw : ∀ i < 64, InRegions s.wr (wordAddr p i) 16) :
    WP isa zeroWide s fun t => RegKeep [] s t ∧
      Frame [outputR p] s.mem t.mem ∧ ∀ i < 64, t.mem.read (wordAddr p i) 16 = 0 := by
  unfold zeroWide
  rw [List.cons_append,WP.block_cons_iff]
  refine ⟨s.setV .v0 0,rfl,?_⟩
  have hz := VG.Proof.MlKem.AArch64.vupd_setV s .v0 0
  rw [List.nil_append,List.map_eq_flatMap]
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k t => RegKeep [] s t ∧ t.v .v0 = 0 ∧ Frame [outputR p] s.mem t.mem ∧
      ∀ i < k, t.mem.read (wordAddr p i) 16 = 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 64 (Nat.le_refl _) (s.setV .v0 0)
    ⟨RegKeep.vupd hz,hz.v,by rw [hz.mem]; exact Frame.refl _ _,
      fun _ h => False.elim (Nat.not_lt_zero _ h)⟩)
    fun t ⟨ht,_,hf,hvals⟩ => ⟨ht,hf,hvals⟩
  refine wp_strq (a := wordAddr p k) (by omega)
    (by rw [ht.gpr .x26 (by simp),hp]; rfl)
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

/-- The SIMD clear preserves the complete calling-convention frame. -/
theorem zeroWide_coeffs {s : State} {p : Addr} (hp : s.gpr .x26 = p)
    (hw : ∀ i<64, InRegions s.wr (wordAddr p i) 16) :
    WP isa zeroWide s fun t => VG.Proof.MlKem.AArch64.Keep [] s t ∧
      Frame [VG.Proof.MlDsa.Sample.polyR p] s.mem t.mem ∧
      ∀ i<256, VG.Spec.MlDsa.coeffAt t.mem p i = 0 := by
  refine WP.mono (WP.preservedV (zeroWide_ok hp hw) (hc := by lit_decide))
    fun t ⟨⟨hk,hf,hz⟩,hv⟩ => ?_
  refine ⟨⟨hk.gpr,hk.rd,hk.wr,hk.sp,hv⟩,hf,fun i hi => ?_⟩
  have hword := hz (i/4) (by omega)
  have hread : t.mem.read (p+BitVec.ofNat 64 (4*i)) 4 = 0 := by
    apply Mem.read_eq_of_bytes
    intro j hj
    have hbyte := Mem.extractLsb'_read t.mem (wordAddr p (i/4))
      (n := 16) (j := 4*(i%4)+j) (by omega)
    rw [hword] at hbyte
    have ha : wordAddr p (i/4)+BitVec.ofNat 64 (4*(i%4)+j) =
        p+BitVec.ofNat 64 (4*i)+BitVec.ofNat 64 j := by
      simp only [wordAddr,BitVec.add_assoc,← BitVec.ofNat_add]
      congr 2
      have := Nat.mod_add_div i 4
      omega
    rw [ha] at hbyte
    simpa [BitVec.extractLsb'] using hbyte.symm
  simp only [VG.Spec.MlDsa.coeffAt,Mem.readW,hread]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Ball
