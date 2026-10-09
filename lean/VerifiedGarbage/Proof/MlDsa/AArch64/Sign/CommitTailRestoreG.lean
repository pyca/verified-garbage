import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailRestoreV

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (wp_ldr)
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

private theorem saved_mem : ∀i<4,saved[i]!∈saved := by decide
private theorem saved_inj : ∀i<4,∀j<4,saved[i]! =saved[j]! ↔ i=j := by decide

/-- Restores all four scalar saves, including the incoming return address. -/
theorem restoreG_ok {σ s : State} (hs : Saved σ s.mem) (hptr : s.gpr .x3=σ.gpr .x3)
    (hin : ∀i<4, InRegions (s.rd++s.wr) (σ.gpr .x3+BitVec.ofNat 64 (128+8*i)) 8) :
    WP isa (.block ((List.range 4).map fun i => .ldr .x saved[i]! .x3 (128+8*i))) s fun t =>
      RegKeep saved s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      ∀i<4,t.gpr saved[i]! =σ.gpr saved[i]! := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M:=isa)
    (fun k t => RegKeep saved s t ∧ t.mem=s.mem ∧ t.v=s.v ∧
      ∀i<k,t.gpr saved[i]! =σ.gpr saved[i]!)
    (fun k t hk ht => ?_) 4 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,rfl,fun _ h => by omega⟩
  refine wp_ldr ⟨by omega,by omega⟩ (by rw [ht.1.gpr .x3 (by decide),hptr])
    (by rw [ht.1.rd,ht.1.wr]; exact hin k hk) fun u hu => WP.block_nil_iff.mpr ?_
  refine ⟨(ht.1.trans (RegKeep.upd hu)).mono ?_,hu.mem.trans ht.2.1,hu.vec.trans ht.2.2.1,?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · rcases List.mem_singleton.mp hr with rfl
      exact saved_mem k hk
  · intro i hi
    by_cases he : i=k
    · subst i
      rw [hu.gpr,ht.2.1,hs.regs k hk]
    · have hne : saved[i]!≠saved[k]! := by
        rw [ne_eq,saved_inj i (by omega) k hk]; exact he
      rw [hu.other _ hne]
      exact ht.2.2.2 i (by omega)

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
