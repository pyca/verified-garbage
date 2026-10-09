import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitTable

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour

def initTableRegion (p : Addr) : Region := ⟨p+BitVec.ofNat 64 6000,1024⟩

theorem initEntryMemory_tableFrame (m : Mem) (p : Addr) {mask : Nat} (hm : mask<16) :
    Frame [initTableRegion p] m (initEntryMemory m p mask) := by
  rw [initEntryMemory_eq m p hm]
  have h16 : (initTableRegion p).Contains (p+BitVec.ofNat 64 (6000+64*mask)) 16 :=
    Offset.contains p (by omega) (by omega) (by decide)
  have h32 : (initTableRegion p).Contains (p+BitVec.ofNat 64 (6000+64*mask+32)) 8 :=
    Offset.contains p (by omega) (by omega) (by decide)
  exact ((Frame.refl _ m).write (by simp) _ h16).writeW (by simp) _ h32

theorem tableMemory_frame (m : Mem) (p : Addr) {n : Nat} (hn : n≤16) :
    Frame [initTableRegion p] m (tableMemory m p n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih => exact (ih (by omega)).trans (initEntryMemory_tableFrame _ p (by omega))

/-- The selected fast initializer builds all sixteen entries, changes only x6,
and confines writes to the 1024-byte table at scratch+6000. -/
theorem tableInit_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (hw : ∀a n,InRegions [initTableRegion (s.gpr .x19)] a n → InRegions s.wr a n)
    (k : ∀t,Keep [.x6] s t → t.v=s.v →
      TableAt t.mem (s.gpr .x19+6000) →
      Frame [initTableRegion (s.gpr .x19)] s.mem t.mem → WP isa (.block rest) t Q) :
    WP isa (.block (tableInit true++rest)) s Q := by
  change WP isa (.block (tablePrefixCode 16++rest)) s Q
  refine tablePrefixCode_ok (by decide) (by
    intro mask hm off hoff
    apply hw
    refine ⟨initTableRegion (s.gpr .x19),by simp,?_⟩
    have ho : off=0 ∨ off=8 ∨ off=32 := by simpa using hoff
    exact Offset.contains _ (by omega) (by omega) (by decide)) fun t ht hv hm => k t ht hv ?_ ?_
  · rw [hm]
    exact tableMemory_table _ _
  · rw [hm]
    exact tableMemory_frame _ _ (by decide)
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
