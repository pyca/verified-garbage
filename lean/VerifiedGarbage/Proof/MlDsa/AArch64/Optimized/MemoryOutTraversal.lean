import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOut
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryTraversal

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The separate-source outer pass stores exactly the reference field result. -/
theorem outerOutPass_field {m : Mem} {p src : Addr} {w : Poly}
    (h : PolyIs m src w) (hd : (polyRegion src).Disjoint (polyRegion p)) :
    SignedPolyIs (outerOutPassMem m p src ordinaryRoot 8) p
      (Traversal.run Traversal.outerSchedule w) (-(15*8380417)) (15*8380417) := by
  apply (outerPass_all h).congr
  intro k hk
  exact outerOutPass_processed hd (by decide) hk (by omega)

/-- A disjoint-source optimized transform implements the standard NTT. -/
theorem outMemory_field_disjoint {m : Mem} {p src : Addr} {w : Poly}
    (h : PolyIs m src w) (hd : (polyRegion src).Disjoint (polyRegion p)) :
    PosPolyIs (outMemory m p src ordinaryRoot innerRoot tailRoot) p (ntt w) := by
  have ho := outerOutPass_field h hd
  have hi := fivePassMem_field (by simpa only [Int.neg_mul] using ho)
  simpa only [outMemory,Traversal.traversal_ntt] using hi

/-- The caller may use either exact aliasing or disjoint polynomial buffers. -/
theorem outMemory_field {m : Mem} {p src : Addr} {w : Poly}
    (h : PolyIs m src w) (hd : src=p ∨ (polyRegion src).Disjoint (polyRegion p)) :
    PosPolyIs (outMemory m p src ordinaryRoot innerRoot tailRoot) p (ntt w) := by
  rcases hd with he | hs
  · subst src
    rw [outMemory_self]
    exact nttMemory_field h
  · exact outMemory_field_disjoint h hs

end VG.Proof.MlDsa.AArch64.Optimized
