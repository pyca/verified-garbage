module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Dsa.X86.Generation.BufferArgs
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchSlots

/-! # Select the persistent p buffer and test its leading bit -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem pCandidateGuard_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State} {value : Nat}
    (R : SearchContext P W s) (bound : value < 256 ^ P.geometry.pLen)
    (bytes : Spec.Rsa.bytesAt s.mem (off P.geometry.base p) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen value) :
    WP isa (.block (candidatePointer p ++ ([.mov .esi (.mem (frameSlot 22))] : List Instr) ++ candidateWidth)) s fun t =>
      SearchContext P (frameUpdate W 22 (P.geometry.pointer p)) t ∧
      t.cf = some (decide (value < 2 ^ (8 * P.geometry.pLen - 1))) ∧
      Frame [⟨P.geometry.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩] s.mem t.mem ∧
      Keeps [.eax, .esi] s t := by
  have pw := P.geometry.width
  have room : p + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold p usedBytes domainCheck; omega
  have start : p < usedBytes P.geometry.pLen := by omega
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (searchCandidatePointer_ok R p) fun a ⟨Ra, Oa, Ka⟩ => ?_)
  have ba : Spec.Rsa.bytesAt a.mem (off P.geometry.base p) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen value := by
    rw [drawFrame_bytes Oa (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (P.geometry.frame_part room).symm) (by omega), bytes]
  refine WP.block_append (wp_movS (Ra.arena.frame.readWord Ra.representation (by decide : 22 < 37)) fun b ab _ => WP.block_nil ?_)
  have si : b.gpr .esi = P.geometry.pointer p := by rw [ab.gpr]; rfl
  have Rb := Ra.congr ab.mem ab.keeps (by decide)
  refine WP.mono (candidateWidth_ok (by omega : 0 < P.geometry.pLen) bound (by
    rw [si, P.geometry.pointer_addr start, ab.mem]; exact ba) (by
    rw [si, P.geometry.pointer_addr start]; exact Rb.arena.read (by omega : p + 1 ≤ usedBytes P.geometry.pLen)))
    fun t ⟨cf, mem, Kt⟩ => ?_
  exact ⟨Rb.congr mem Kt (by decide), cf, by rw [mem, ab.mem]; exact Oa,
    (Ka.mono (by decide)).trans ((ab.keeps.mono (by decide)).trans (Kt.mono (by decide)))⟩
end VG.Proof.Dsa.X86.Generation
