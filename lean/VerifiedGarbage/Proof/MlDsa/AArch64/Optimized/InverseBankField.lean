import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldPackedBounds
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedTable
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldRun
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseFive

/-! ## From `InverseBankFieldPackedLayer.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedLayerValues (len : Nat) (root : Nat → Nat → Nat) (g : Nat) :
    Nat → Vector (BitVec 128) 8 → Vector (BitVec 128) 8
  | 0,v => v
  | n+1,v => packedLayerValues len root (g+1) n
      (packedValues v ⟨(2*g)%8,Nat.mod_lt _ (by decide)⟩
        ⟨(2*g+1)%8,Nat.mod_lt _ (by decide)⟩ len (fun e => (negZetaNat (root g e) : Int)))

def packedLayerOps (u len : Nat) (root : Nat → Nat → Nat) (g : Nat) : Nat → List InverseTraversal.Op
  | 0 => []
  | n+1 => InverseTraversal.packedSchedule (32*u+8*g) len (root g) ++ packedLayerOps u len root (g+1) n

theorem packedLayer_values (v : Vector (BitVec 128) 8) (w : Poly) {u len g n : Nat}
    (hu : u<8) (hl : len=1 ∨ len=2) (hgn : g+n≤4) (root : Nat → Nat → Nat)
    {b : Int} (hb : 8380417≤b) (hs : 2*b<2147483648)
    (hv : PackedProgress v g b) (hf : InnerBankField u v w) :
    PackedProgress (packedLayerValues len root g n v) (g+n) b ∧
      InnerBankField u (packedLayerValues len root g n v)
        (InverseTraversal.run (packedLayerOps u len root g n) w) := by
  induction n generalizing g v w with
  | zero => exact ⟨hv,hf⟩
  | succ n ih =>
    have hg : g<4 := by omega
    have hm0 : 2*g%8=2*g := Nat.mod_eq_of_lt (by omega)
    have hm1 : (2*g+1)%8=2*g+1 := Nat.mod_eq_of_lt (by omega)
    have hp := packedValues_progress v hg hl (fun e => (negZetaNat (root g e) : Int)) hb hs hv
    have hfield := packedValues_field v w hg hl hu (root g) hb hs
      (fun j hj => hv.pair hg hj) hf
    have hi := ih _ _ (g := g+1) (by omega) hp hfield
    simpa only [packedLayerValues,packedLayerOps,hm0,hm1,InverseTraversal.run_append,
      Nat.add_assoc,Nat.add_comm 1 n] using hi

theorem packedLayer_full (v : Vector (BitVec 128) 8) (w : Poly) {u len : Nat}
    (hu : u<8) (hl : len=1 ∨ len=2) (root : Nat → Nat → Nat)
    {b : Int} (hb : 8380417≤b) (hs : 2*b<2147483648)
    (hv : BankBound v b) (hf : InnerBankField u v w) :
    BankBound (packedLayerValues len root 0 4 v) (2*b) ∧
      InnerBankField u (packedLayerValues len root 0 4 v)
        (InverseTraversal.run (packedLayerOps u len root 0 4) w) := by
  have h := packedLayer_values v w hu hl (g := 0) (n := 4) (by decide) root hb hs
    ((packedProgress_zero v b).mpr hv) hf
  exact ⟨(packedProgress_four _ b).mp h.1,h.2⟩

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end

/-! ## From `InverseBankFieldPackedPass.lean` -/

section

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

end

/-! ## From `InverseBankField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- The physical packed groups and renamed groups visit exactly the logical
local slice, retaining each root index symbolically. -/
theorem fiveOps_eq {u : Nat} (hu : u<8) :
    packedPassOps u ++ runOps u (localIndex u) 0 7=InverseTraversal.localSlice u := by
  exact (show ∀ u : Fin 8,
    packedPassOps u.val ++ runOps u.val (localIndex u.val) 0 7=InverseTraversal.localSlice u.val
    by decide +kernel) ⟨u,hu⟩

/-- The selected five-layer machine bank has the exact inverse field result,
with every signed representative bounded by 32q. No normalization is added. -/
theorem fiveValues_field (v : Vector (BitVec 128) 8) (w : Poly) {u : Nat} (hu : u<8)
    (hv : BankBound v 8380417) (hf : InnerBankField u v w) :
    BankBound (fiveValues u v) 268173344 ∧
      InnerBankField u (fiveValues u v) (InverseTraversal.run (InverseTraversal.localSlice u) w) := by
  rw [fiveValues,packedPassValues_eq]
  have hp := packedPass_field v w hu hv hf
  have h := runValues_local _ _ hu hp.1 hp.2
  refine ⟨h.1,?_⟩
  simpa only [← InverseTraversal.run_append,fiveOps_eq hu] using h.2

end VG.Proof.MlDsa.AArch64.Optimized.Inverse

end
