module
public import VerifiedGarbage.Proof.Rsa.X86.CvABI
public import VerifiedGarbage.Proof.Rsa.X86.CvResult
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Rsa.X86.CvBuffers
import VerifiedGarbage.Proof.Rsa.X86.CvResources
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Words
public import Init.Prelude
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Mont.Words

/-! # CRT output writes preserve saved registers and the caller's return address -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86

theorem bodyFrame_full {g : CallGeometry} {m m' : Mem} (low : 16 ≤ g.size)
    (f : Frame (bodyWrites g) m m') : Frame g.writes m m' := by
  apply f.sub
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨g.base, g.size⟩, by simp [CallGeometry.writes], Offset.sub_base _ (by omega)⟩
  all_goals exact ⟨_, by simp [CallGeometry.writes], fun _ h => h⟩

theorem bodyFrame_saved {g : CallGeometry} {s : State} {m m' : Mem} {regs : Reg → BitVec 32}
    (h : Inputs g s) (f : Frame (bodyWrites g) m m')
    (saved : Saved m (off g.base) regs PublicFn.savedRegisters) :
    Saved m' (off g.base) regs PublicFn.savedRegisters := by
  have low : 16 ≤ g.size := by have := h.ws.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at this; omega
  have high : g.size ≤ 2 ^ 64 := by have := h.ws.workspace.nowrap; omega
  intro p hp
  have bound : p.2 + 4 ≤ 16 := by
    simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (f.readW (r := ⟨g.base, 16⟩) (Offset.contains_base _ bound (by omega)) ?_ (by decide)).trans (saved p hp)
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.base_disjoint g.base (Nat.le_refl 16) (by omega)
  · exact (h.outputScratch 0).symm.sub_left (Region.sub_prefix low)
  · exact (h.outputScratch 1).symm.sub_left (Region.sub_prefix low)
  · exact (h.outputScratch 2).symm.sub_left (Region.sub_prefix low)

theorem calculated_entry {s t : State} (a : ABI s)
    (o : Outside (caller s).base 0 (caller s).size s.mem t.mem) :
    calculated (caller s) t.mem = calculated (caller s) s.mem := by
  have same (i : Fin 4) : inputBytes (caller s) t.mem i = inputBytes (caller s) s.mem i := by
    exact scratch_bytes o (by have := (a.inputLength i).2; have := a.width.2.1; omega)
      (a.inApart _ (a.inputMember i) _ (by simp [CallGeometry.writes]))
  unfold calculated
  rw [same 0, same 1, same 2, same 3]

end VG.Proof.Rsa.X86.CrtValues
