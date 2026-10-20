module
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameWords
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Dsa.X86.Generation.WorkspaceToFrame

/-! # Returning status and consumed bytes preserves the other search slots -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem primeReturn_ok {s : State} {frame base : Addr} {size : Nat} {words : Nat → BitVec 32}
    (F : SearchFrame s frame) (S : Scr s base size) (R : FrameWords s.mem frame words)
    (room : primeWitness + 4 ≤ size) (apart : Region.Disjoint ⟨frame, frameBytes⟩ ⟨base, size⟩) :
    WP isa (.block primeReturn) s fun t => SearchFrame t frame ∧ Scr t base size ∧
      FrameWords t.mem frame (frameUpdate (frameUpdate words 16 (s.mem.readW (off base primeUsed) 32))
        19 (s.mem.readW (off base primeStatus) 32)) ∧
      Outside frame 64 16 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold primeReturn
  refine WP.block_append (WP.mono (workspaceToFrame_ok F S R (by decide : 16 < 37)
    (by unfold primeUsed primeWitness at *; omega)) fun a ⟨Fa, Sa, Ra, ma, Oa, Ka⟩ => ?_)
  have status : a.mem.readW (off base primeStatus) 32 = s.mem.readW (off base primeStatus) 32 := by
    rw [ma]
    apply Mem.readW_writeW_sep
    · apply apart.symm.sep
      · exact Offset.contains_base _ (by unfold primeStatus primeWitness at *; omega) (by decide)
      · exact Offset.contains_base _ (by unfold frameBytes; decide) (by decide)
    · decide
  refine WP.mono (workspaceToFrame_ok Fa Sa Ra (by decide : 19 < 37)
    (by unfold primeStatus primeWitness at *; omega)) fun t ⟨Ft, St, Rt, _, Ot, Kt⟩ => ?_
  rw [status] at Rt
  exact ⟨Ft, St, Rt, (Oa.mono (by omega) (by omega)).trans (Ot.mono (by omega) (by omega)), Ka.trans Kt⟩
end VG.Proof.Dsa.X86.Generation
