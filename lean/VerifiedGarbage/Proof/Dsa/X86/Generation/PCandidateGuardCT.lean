module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Frame
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateWidth
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.PCandidateGuard
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs

/-! # The p-candidate leading-bit guard uses its public buffer pointer -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

theorem pGuardPointer_ct : RelCT isa (Two (FrameAt [5]))
    (.block (candidatePointer p ++ ([.mov .esi (.mem (frameSlot 22))] : List Instr)))
    (Two fun (P : PublicFrame) s => s.gpr .esi = P.words 5 + BitVec.ofNat 32 p) := by
  refine two_piece [.esp] (frameAt_pins _) (by taint_decide) ?_
  intro P s R
  refine WP.block_append (WP.mono (candidatePointer_ok R.1 (observedWords_rep P.base s) p)
    fun a ⟨F, W, _, _⟩ => ?_)
  refine wp_movS (F.readWord W (by decide : 22 < 37)) fun t st _ => WP.block_nil ?_
  rw [st.gpr]
  change s.mem.readW (off P.base 20) 32 + BitVec.ofNat 32 p = _
  rw [R.2 5 (by simp)]

theorem pGuardBlock_ct : RelCT isa (Two (FrameAt [5]))
    (.block (candidatePointer p ++ ([.mov .esi (.mem (frameSlot 22))] : List Instr) ++ candidateWidth)) (fun _ _ => True) := by
  refine RelCT.block_append (RelCT.seq pGuardPointer_ct ?_)
  refine two_taint [.esi] ?_ (by taint_decide)
  intro P s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.trans ht.symm
end VG.Proof.Dsa.X86.Generation
