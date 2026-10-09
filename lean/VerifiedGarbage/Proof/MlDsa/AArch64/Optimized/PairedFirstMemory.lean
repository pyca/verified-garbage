import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStoreMemory
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Inverse (fiveValues)

def valuesAt (m : Mem) (a b : Addr) : Values := fun p => Vector.ofFn fun j =>
  let aa := m.read (a+BitVec.ofNat 64 (16*j.val)) 16
  let bb := m.read (b+BitVec.ofNat 64 (1024*p.val+16*j.val)) 16
  ofVWords (centeredProduct (vword aa 0) (vword bb 0))
    (centeredProduct (vword aa 1) (vword bb 1))
    (centeredProduct (vword aa 2) (vword bb 2))
    (centeredProduct (vword aa 3) (vword bb 3))

theorem inputValues_eq (s : State) : inputValues s=valuesAt s.mem (s.gpr .x13) (s.gpr .x14) := rfl

def firstPassMem (m : Mem) (p a b : Addr) : Nat → Mem
  | 0 => m
  | u+1 =>
    let prev := firstPassMem m p a b u
    let v := valuesAt prev (a+BitVec.ofNat 64 (128*u)) (b+BitVec.ofNat 64 (128*u))
    writePair (fun j => fiveValues u (v j)) (p+BitVec.ofNat 64 (128*u)) 16 prev

theorem firstPass_frame {m : Mem} {p a b : Addr} {u : Nat} (hu : u≤8) :
    Frame [⟨p,2048⟩] m (firstPassMem m p a b u) := by
  induction u with
  | zero => exact Frame.refl _ _
  | succ u ih =>
    simp only [firstPassMem]
    refine writePair_frame _ _ _ (r:=⟨p,2048⟩) (by simp) ?_ (ih (by omega))
    intro poly j
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact Offset.contains_base p (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.Paired
