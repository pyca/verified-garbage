import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailOutput

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem.AArch64 (wp_strq)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- The selected prologue preserves all 128 bits of each callee-saved vector. -/
theorem saveV_ok {s : State}
    (hout : ∀i<8, InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block save) s fun t => RegKeep [] s t ∧ t.v=s.v ∧
      Frame [⟨s.gpr .x3,128⟩] s.mem t.mem ∧
      ∀i<8,t.mem.read (s.gpr .x3+BitVec.ofNat 64 (16*i)) 16=s.v (vreg (8+i)) := by
  unfold save
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x3,128⟩] s.mem t.mem ∧
      ∀i<k,t.mem.read (s.gpr .x3+BitVec.ofNat 64 (16*i)) 16=s.v (vreg (8+i)))
    (fun k t hk ht => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,Frame.refl _ _,fun _ h => by omega⟩
  refine wp_strq ⟨by omega,by omega⟩ (by rw [ht.1.gpr .x3 (by simp)])
    (by rw [ht.1.wr]; exact hout k hk) fun u hu => WP.block_nil_iff.mpr ?_
  have hm : u.mem=t.mem.write (s.gpr .x3+BitVec.ofNat 64 (16*k)) 16 (s.v (vreg (8+k))) := by
    rw [hu.mem,ht.2.1]
  refine ⟨(ht.1.trans (RegKeep.vmem hu)).mono (by simp),hu.v.trans ht.2.1,?_,?_⟩
  · rw [hm]
    exact ht.2.2.1.write (r:=⟨s.gpr .x3,128⟩) (by simp) _
      (Offset.contains_base _ (by omega) (by omega))
  · intro i hi
    rw [hm]
    by_cases he : i=k
    · subst i; exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep (s.gpr .x3) (d:=16*i) (n:=16) (e:=16*k) (k:=16)
        (by omega) (by omega) (by omega)) (by decide)]
      exact ht.2.2.2 i (by omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
