import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLoopState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejBytes

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Spec.MlDsa (Zq)

/-- Equality of the meaningful three-byte candidates only.  Ignored overread
bytes and unwritten output coefficients are deliberately absent. -/
def InputEq (s t : State) (b : Addr) (n : Nat) : Prop :=
  ∀i<3*n,s.mem (b+BitVec.ofNat 64 i)=t.mem (b+BitVec.ofNat 64 i)

theorem parsed_eq {s t : State} {b : Addr} {n d : Nat} (h : InputEq s t b n)
    (hd : d≤n) (L : List Zq) : parsed s b L d=parsed t b L d := by
  unfold parsed
  rw [candidateBytes_eq_bytesAt,candidateBytes_eq_bytesAt]
  congr 1
  unfold Spec.Sha3.bytesAt
  apply List.map_congr_left
  intro i hi
  exact h i (by have := List.mem_range.mp hi; omega)

theorem ParseInv.publicRegs {σ τ s t : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (he : InputEq σ τ b n) (hsp : σ.sp=τ.sp)
    (hs : ParseInv σ b p n L d s) (ht : ParseInv τ b p n L d t) :
    s.sp=t.sp ∧ ∀r∈[Reg.x2,.x3,.x4,.x5],s.gpr r=t.gpr r := by
  have hL := parsed_eq he hs.bound L
  refine ⟨hs.keep.sp.trans (hsp.trans ht.keep.sp.symm),?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hs.x2,ht.x2]
  · rw [hs.x3,ht.x3,hL]
  · apply BitVec.eq_of_toNat_eq
    rw [hs.x4,ht.x4,hL]
  · apply BitVec.eq_of_toNat_eq
    rw [hs.x5,ht.x5]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
