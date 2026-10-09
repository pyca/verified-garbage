import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InnerTraversal
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PackedLanes

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

def packedSchedule (start len : Nat) (root : Nat → Nat) : List Op :=
  (List.range (4/len)).flatMap fun g => (List.range len).map fun j =>
    ⟨start+2*len*g+j,len,root (len*g+j)⟩

theorem packedSchedule_get (w : Poly) {start len i : Nat} (hl : len=1 ∨ len=2)
    (hs : start+8≤256) (hi : i<8) (root : Nat → Nat) :
    (run (packedSchedule start len root) w)[start+i]! =
      let x := w[start+packedLow len i]!
      let y := zetas (root (packedLane len i))*w[start+packedLow len i+len]!
      if i%(2*len)<len then x+y else x-y := by
  have hi' : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases hl with rfl | rfl <;>
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [-getElem!_pos,packedSchedule,run,List.range_succ,Op.apply,packedLow,packedLane,Nat.add_assoc] <;>
    repeat (rw [bfly_get _ (by omega) (by unfold n; omega) _ (by unfold n; omega)]
            simp (disch := omega) [-getElem!_pos,Nat.add_assoc])

theorem packedSchedule_outside (w : Poly) {start len i : Nat} (hl : len=1 ∨ len=2)
    (hs : start+8≤256) (hi : i<256) (hout : i<start ∨ start+8≤i) (root : Nat → Nat) :
    (run (packedSchedule start len root) w)[i]! = w[i]! := by
  have h0 : i≠start := by omega
  have hn : ∀ j<8,i≠start+j := by intro j hj; omega
  rcases hl with rfl | rfl <;>
    simp [-getElem!_pos,packedSchedule,run,List.range_succ,Op.apply] <;>
    repeat (rw [bfly_get _ (by omega) (by unfold n; omega) _ (by unfold n; omega)]
            simp (disch := omega) [-getElem!_pos,Nat.add_assoc,h0,hn 1 (by decide),
              hn 2 (by decide),hn 3 (by decide),hn 4 (by decide),hn 5 (by decide),
              hn 6 (by decide),hn 7 (by decide)])

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
