import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldPackedLayer
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedTable

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedIndex (u len g e : Nat) : Nat :=
  256/len-1-(16*u/len+4*g/len+e/len)

def packedPassValues (u : Nat) (v : Vector (BitVec 128) 8) : Vector (BitVec 128) 8 :=
  packedLayerValues 2 (packedIndex u 2) 0 4 (packedLayerValues 1 (packedIndex u 1) 0 4 v)

def packedPassOps (u : Nat) : List InverseTraversal.Op :=
  packedLayerOps u 1 (packedIndex u 1) 0 4 ++ packedLayerOps u 2 (packedIndex u 2) 0 4

theorem packedPass_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 8380417) (hf : InnerBankField u v w) :
    BankBound (packedPassValues u v) 33521668 ∧
      InnerBankField u (packedPassValues u v) (InverseTraversal.run (packedPassOps u) w) := by
  have h1 := packedLayer_full v w hu (Or.inl rfl) (packedIndex u 1) (by decide) (by decide) hv hf
  have h2 := packedLayer_full _ _ hu (Or.inr rfl) (packedIndex u 2) (by decide) (by decide) h1.1 h1.2
  simpa only [packedPassValues,packedPassOps,InverseTraversal.run_append,Int.reduceMul] using h2

theorem packedRoot_index (u g len : Nat) (hl : len=1 ∨ len=2) :
    packedRoot u g len=(fun e => (negZetaNat (packedIndex u len g e) : Int)) := by
  funext e
  have hi : (if len=1 then 255-16*u-4*g-e else 127-8*u-2*g-e/2)=packedIndex u len g e := by
    rcases hl with rfl | rfl <;> simp [packedIndex] <;> omega
  unfold packedRoot
  rw [hi]
  rfl

theorem packedPassValues_eq (u : Nat) (v : Vector (BitVec 128) 8) :
    packedRunValues v (packedRoot u) packedSteps=packedPassValues u v := by
  have h1 := fun g => packedRoot_index u g 1 (Or.inl rfl)
  have h2 := fun g => packedRoot_index u g 2 (Or.inr rfl)
  simp only [packedRunValues,packedSteps,h1,h2,packedPassValues,packedLayerValues]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
