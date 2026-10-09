import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseMemoryField
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankField

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem firstPass_field_prefix {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-8380417) 8380417) {u : Nat} (hu : u≤8) :
    SignedPolyIs (firstPassMem m p u) p
      (InverseTraversal.run ((List.range u).flatMap InverseTraversal.localSlice) w)
      (-268173344) 268173344 := by
  induction u with
  | zero => exact h.mono (by decide) (by decide)
  | succ u ih =>
    have hp := ih (by omega)
    have hf : InnerBankField u
        (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16)
        (InverseTraversal.run ((List.range u).flatMap InverseTraversal.localSlice) w) := by
      intro i e he
      rw [readBank_coeff _ p (32*u) 4 i he]
      exact hp.value _ (by change 32*u+4*i.val+e<256; omega)
    have hb : BankBound (readBank (firstPassMem m p u) (coeffAddr p (32*u)) 16) 8380417 :=
      fun i e he => firstPass_bank_bound (by omega) h.bound i he
    have hs := fiveValues_field _ _ (by omega : u<8) hb hf
    have hm := firstMemStep_field (by omega : u<8) hp hs.1 hs.2
    simpa only [firstPassMem_step,List.range_succ,List.flatMap_append,
      List.flatMap_singleton,InverseTraversal.run_append] using hm

/-- All eight local blocks implement the first five inverse layers, retaining
bounded signed representatives for the subsequent strided pass. -/
theorem firstPass_field {m : Mem} {p : Addr} {w : Poly}
    (h : SignedPolyIs m p w (-8380417) 8380417) :
    SignedPolyIs (firstPassMem m p 8) p
      (InverseTraversal.run InverseTraversal.localSchedule w) (-268173344) 268173344 :=
  firstPass_field_prefix h (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
