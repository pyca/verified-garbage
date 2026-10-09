import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryFinalField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryFirstPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalBankField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem finalPass_field {m : Mem} {p : Addr} {w : Poly} {qv : BitVec 128}
    (h : SignedPolyIs m p w (-268173344) 268173344)
    (hq : ∀ e<4, vword qv e=8380417#32) :
    PolyIs (finalPassMem m p qv 8) p ((InverseTraversal.run InverseTraversal.stridedSchedule w).map (· * 16382)) := by
  have bank (u : Nat) (hu : u<8) := fun (i : Fin 8) (e : Nat) (he : e<4) =>
    finalValues_field (readBank m (coeffAddr p (4*u)) 128) qv w hu
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        exact h.bound _ (by change 4*u+32*j.val+e<256; omega))
      (fun j e he => by
        rw [readBank_coeff m p (4*u) 32 j he]
        simpa only [Traversal.loc,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
          h.value (4*u+32*j.val+e) (by change 4*u+32*j.val+e<256; omega)) hq i he
  exact finalPass_field_of_banks (fun u hu i e he => (bank u hu i e he).1)
    (fun u hu i e he => (bank u hu i e he).2)

/-- Exact selected two-pass inverse, valid also for centered raw products. -/
theorem inverseMem_field_signed {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-8380417) 8380417) :
    PolyIs (inverseMem m p) p (montgomeryNttInv w) := by
  have hp := finalPass_field (firstPass_field h) (qv := HighPack.repeatedWord 8380417)
    (fun e he => HighPack.repeatedWord_lane _ he)
  simpa only [inverseMem,InverseTraversal.traversal_montgomery] using hp

theorem inverseMem_field {m : Mem} {p : Addr} {w : Poly} (h : PolyIs m p w) :
    PolyIs (inverseMem m p) p (montgomeryNttInv w) := by
  apply inverseMem_field_signed
  constructor
  · intro k hk
    rw [VG.Proof.MlDsa.AArch64.Optimized.canonicalWord_int _ (h.1 k hk)]
    have hb := h.1 k hk
    change (coeffAt m p k).toNat<8380417 at hb
    omega
  · intro k hk
    rw [VG.Proof.MlDsa.AArch64.Optimized.canonicalWord_field _ (h.1 k hk),← polyAt_get _ _ hk,h.2]

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
