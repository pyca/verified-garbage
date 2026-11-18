module

public import VerifiedGarbage.Spec.Cast5.Cbc
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# CAST5: the locality lemmas of its residue proofs

On every target: the blocks and the schedule a postcondition reads agree
between two memories that agree on the buffer they lie in
(`Proof/Cast5/X86_64/Scrub.lean`, `Proof/Cast5/RISCV64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.ScrubLocal

open VG.Proof.Aes.ScrubLocal

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

theorem blocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 8 ≤ L) :
    Spec.Cast5.blocksAt m₂ p n = Spec.Cast5.blocksAt m₁ p n := by
  simp only [Spec.Cast5.blocksAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  apply Vector.ext
  intro j hj
  simp only [Spec.Cast5.blockAt, Vector.getElem_ofFn]
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_using [this, hj])

theorem cbcBlocksAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n * 8 ≤ L) :
    Spec.Cast5.cbcBlocksAt m₂ p n = Spec.Cast5.cbcBlocksAt m₁ p n := by
  simp only [Spec.Cast5.cbcBlocksAt, blocksAt_of0 h hn]

theorem scheduleAt_of (h : ∀ a, Region.Contains ⟨p, 128⟩ a 1 → m₁ a = m₂ a) :
    Spec.Cast5.scheduleAt m₂ p = Spec.Cast5.scheduleAt m₁ p :=
  Proof.Cast5.scheduleAt_congr (agree_le h (Nat.le_refl _))

end VG.Proof.Cast5.ScrubLocal
