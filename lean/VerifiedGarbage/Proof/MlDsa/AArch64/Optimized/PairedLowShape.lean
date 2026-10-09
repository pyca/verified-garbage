import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowPair

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.PairedBase (vr)

/-- Every scheduled raw-register pair is distinct and outside the reserved constants/scratch. -/
theorem lowPair_registers {p j : Nat} (hp : p<2) (hj : j<4) :
    vr (8*p+2*j)∉lowReserved ∧ vr (8*p+2*j+1)∉lowReserved ∧
      vr (8*p+2*j)≠vr (8*p+2*j+1) := by
  have h : ∀p : Fin 2,∀j : Fin 4,
      vr (8*p.val+2*j.val)∉lowReserved ∧ vr (8*p.val+2*j.val+1)∉lowReserved ∧
      vr (8*p.val+2*j.val)≠vr (8*p.val+2*j.val+1) := by decide
  exact h ⟨p,hp⟩ ⟨j,hj⟩

/-- Both vectors remain in their bank's polynomial region. -/
theorem lowPair_offsets {p j : Nat} (hp : p<2) (hj : j<4) :
    (1024*p+256*j)%16=0 ∧ 1024*p+256*j+128<65536 ∧
      1024*p≤1024*p+256*j ∧ 1024*p+256*j+128+16≤1024*p+1024 := by
  constructor
  · omega
  · omega
end VG.Proof.MlDsa.AArch64.Optimized.Paired
