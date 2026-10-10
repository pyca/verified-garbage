import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedStore
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.SliceFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFirst
import VerifiedGarbage.Proof.Framework.Offset

/-! ## From `PairedStoreMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64

theorem writePair_split (v : Values) (base : Addr) (stride : Nat) (m : Mem) :
    writePair v base stride m=writeBank (v 1) (base+1024) stride (writeBank (v 0) base stride m) := by
  simp only [writePair,show List.finRange 2=[0,1] by rfl,List.foldl_cons,List.foldl_nil,
    Fin.val_zero,Fin.val_one,Nat.mul_zero,Nat.zero_add,Nat.mul_one,writeBank]
  simp only [BitVec.ofNat_add,BitVec.add_assoc,show (1024 : Addr)=1024#64 by rfl]

theorem writePair_frame (v : Values) (base : Addr) (stride : Nat)
    {m m₀ : Mem} {W : List Region} {r : Region} (hr : r∈W)
    (hc : ∀p:Fin 2,∀j:Fin 8,r.Contains (base+BitVec.ofNat 64 (1024*p.val+stride*j.val)) 16)
    (hf : Frame W m₀ m) : Frame W m₀ (writePair v base stride m) := by
  rw [writePair_split]
  refine writeBank_frame _ _ _ hr ?_ ?_
  · intro j
    simpa only [Fin.val_one,Nat.mul_one,BitVec.ofNat_add,BitVec.add_assoc,show (1024 : Addr)=1024#64 by rfl] using hc 1 j
  · refine writeBank_frame _ _ _ hr ?_ hf
    intro j
    simpa only [Fin.val_zero,Nat.mul_zero,Nat.zero_add] using hc 0 j

end VG.Proof.MlDsa.AArch64.Optimized.Paired

end

/-! ## From `PairedFirstMemory.lean` -/

section

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

end
