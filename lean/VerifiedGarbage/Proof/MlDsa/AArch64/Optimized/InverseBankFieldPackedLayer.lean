import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseBankFieldPackedBounds
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedRun

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
