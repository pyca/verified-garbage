import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSaveV

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_str)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

/-- Saves precisely the nonvolatile scalar registers used by this helper. -/
theorem saveG_ok {s : State}
    (hout : ∀i<4, InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block ((List.range 4).map fun i => .str .x saved[i]! .x3 (128+8*i))) s fun t =>
      RegKeep [] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x3+128,32⟩] s.mem t.mem ∧
      ∀i<4,t.mem.readW (s.gpr .x3+BitVec.ofNat 64 (128+8*i)) 64=s.gpr saved[i]! := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep [] s t ∧ t.v=s.v ∧ Frame [⟨s.gpr .x3+128,32⟩] s.mem t.mem ∧
      ∀i<k,t.mem.readW (s.gpr .x3+BitVec.ofNat 64 (128+8*i)) 64=s.gpr saved[i]!)
    (fun k t hk ht => ?_) 4 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,Frame.refl _ _,fun _ h => by omega⟩
  refine wp_str ⟨by omega,by omega⟩ (by rw [ht.1.gpr .x3 (by simp)])
    (by rw [ht.1.wr]; exact hout k hk) fun u hu => WP.block_nil_iff.mpr ?_
  have hm : u.mem=t.mem.writeW (s.gpr .x3+BitVec.ofNat 64 (128+8*k)) (s.gpr saved[k]!) := by
    rw [hu.mem,ht.1.gpr _ (by simp)]
  refine ⟨(ht.1.trans (RegKeep.mupd hu)).mono (by simp),hu.vec.trans ht.2.1,?_,?_⟩
  · rw [hm]
    exact ht.2.2.1.writeW (r:=⟨s.gpr .x3+128,32⟩) (by simp) _
      (Offset.contains (s.gpr .x3) (d:=128+8*k) (e:=128) (n:=8) (k:=32)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hm]
    by_cases he : i=k
    · subst i; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (Offset.sep (s.gpr .x3) (d:=128+8*i) (n:=8) (e:=128+8*k) (k:=8)
        (by omega) (by omega) (by omega)) (by decide)]
      exact ht.2.2.2 i (by omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
