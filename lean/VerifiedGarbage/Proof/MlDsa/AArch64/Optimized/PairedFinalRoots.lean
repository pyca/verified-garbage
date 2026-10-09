import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirstRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFinalRoots

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (finalZ finalValue reciprocal_nat)

theorem tailRoot_final (i : Fin 7) : PairedTable.tailRoot i.val=finalValue i.val := by
  fin_cases i <;> rfl

theorem final_tableReady {s : State} {p : Addr}
    (h : PairedTable.Words s.mem p)
    (hr : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 off) 16)
    (hx : s.gpr .x1=p+BitVec.ofNat 64 3840) (i : Fin 7) : RootReady s (32*i.val) (finalZ i.val) := by
  refine ⟨by omega,by omega,?_,?_,fun e _ => Inverse.finalZ_range i.val e,?_,?_⟩
  · rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hr _ (by omega)
  · rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact hr _ (by omega)
  · intro e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    rw [(h.tail (j:=i.val) (by omega) he).1,tailRoot_final i]
    exact (BitVec.ofInt_natCast ..).symm
  · intro e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add,← Nat.add_assoc]
    rw [(h.tail (j:=i.val) (by omega) he).2,tailRoot_final i]
    exact reciprocal_nat _

theorem scale_tableReady {s : State} {p : Addr}
    (h : PairedTable.Words s.mem p)
    (hr : ∀off,off+16≤4096 → InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 off) 16)
    (hx : s.gpr .x1=p+BitVec.ofNat 64 3840) : RootReady s 224 (fun _ => 16382) := by
  refine ⟨by decide,by decide,?_,?_,by intro e he; decide,?_,?_⟩
  · rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]; exact hr 4064 (by decide)
  · rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]; exact hr 4080 (by decide)
  · intro e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact (h.tail (j:=7) (by decide) he).1
  · intro e he
    rw [hx,BitVec.add_assoc,← BitVec.ofNat_add]
    exact (h.tail (j:=7) (by decide) he).2

end VG.Proof.MlDsa.AArch64.Optimized.Paired
