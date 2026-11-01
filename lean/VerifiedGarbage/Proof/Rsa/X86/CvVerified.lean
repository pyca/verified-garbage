module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Rsa.X86.CvOperationTiming
import VerifiedGarbage.Proof.Rsa.X86.CvABI
import VerifiedGarbage.Proof.Rsa.X86.CvResult
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Rsa.X86.CvBuffers
import VerifiedGarbage.Proof.Rsa.X86.CvResources
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Words
import Init.Prelude
import VerifiedGarbage.Impl.Bignum.X86.PublicFn
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Rsa.X86.CvBody
import VerifiedGarbage.Proof.Rsa.X86.CvInstalled
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
/-! # Complete i686 certificate for CRT parameter calculation -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/CvReturn.lean`, which only this module imported.
section

/-! # CRT output writes preserve saved registers and the caller's return address -/

section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86

theorem bodyFrame_full {g : CallGeometry} {m m' : Mem} {b : Region} (low : 16 ≤ g.size)
    (f : Frame (bodyWrites g ++ [b]) m m') : Frame (g.writes ++ [b]) m m' := by
  apply f.sub
  intro r hr
  simp only [bodyWrites, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨g.base, g.size⟩, by simp [CallGeometry.writes], Offset.sub_base _ (by omega)⟩
  all_goals exact ⟨_, by simp [CallGeometry.writes], fun _ h => h⟩

theorem bodyFrame_saved {g : CallGeometry} {s : State} {m m' : Mem} {regs : Reg → BitVec 32}
    (h : Inputs g s) (f : Frame (bodyWrites g ++ [below (s.gpr .esp) 52]) m m')
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
  simp only [bodyWrites, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.base_disjoint g.base (Nat.le_refl 16) (by omega)
  · exact (h.outputScratch 0).symm.sub_left (Region.sub_prefix low)
  · exact (h.outputScratch 1).symm.sub_left (Region.sub_prefix low)
  · exact (h.outputScratch 2).symm.sub_left (Region.sub_prefix low)
  · exact h.room.2.2.sub_left (Region.sub_prefix low)

theorem calculated_entry {s t : State} (a : ABI s)
    (o : Outside (caller s).base 0 (caller s).size s.mem t.mem) :
    calculated (caller s) t.mem = calculated (caller s) s.mem := by
  have same (i : Fin 4) : inputBytes (caller s) t.mem i = inputBytes (caller s) s.mem i := by
    exact scratch_bytes o (by have := (a.inputLength i).2; have := a.width.2.1; omega)
      (a.inApart _ (a.inputMember i) _ (by simp [CallGeometry.writes]))
  unfold calculated
  rw [same 0, same 1, same 2, same 3]

end VG.Proof.Rsa.X86.CrtValues
end

end

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/CvCorrect.lean`, which only this module imported.
section

/-! # Functional correctness and cdecl preservation of i686 CRT parameter calculation -/

section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.CrtValuesRt (code)

theorem operation_ok [VG.Proof.Rsa.X86.BatchLaw] {s : State} (a : ABI s) :
    WP isa code s fun t => Written (caller s) s.mem t ∧ abiPreserved s t := by
  have low : 16 ≤ (caller s).size := by have := a.used; omega
  have high : (caller s).size ≤ 2 ^ 64 := by have := a.scratchBound; omega
  unfold code
  refine WP.seq (WP.mono (installed_ok a) fun u ⟨inputs, saved, k, o⟩ => ?_)
  refine WP.seq (WP.mono (body_ok inputs a.lengths_ok) fun v ⟨iv, written, frame, kv⟩ => ?_)
  have saveV := bodyFrame_saved inputs frame saved
  have espU : u.gpr .esp = s.gpr .esp := k.1 .esp (by decide)
  rw [espU] at frame
  have whole : Frame ((caller s).writes ++ [below (s.gpr .esp) 52]) s.mem v.mem := by
    have start := outside_frame o (by omega)
    simp only [off, BitVec.add_zero] at start
    exact (start.mono (by simp [CallGeometry.writes])).trans (bodyFrame_full low frame)
  have ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    refine whole.readW (Region.contains_self _ 4) (fun r hr => ?_) (by decide)
    rcases List.mem_append.mp hr with hr | hr
    · exact a.retApart r hr
    · obtain rfl := List.mem_singleton.mp hr
      exact a.retAbove
  refine WP.mono (entryRestore_ok iv.ws.workspace low saveV) fun t restored => ?_
  refine ⟨?_, publicRestored_abi restored ((kv.1 _ (by decide)).trans (k.1 _ (by decide))) ret⟩
  unfold Written at written ⊢
  rw [calculated_entry a o] at written
  rw [restored.mem, restored.other .eax (by decide)]
  exact written

theorem correct [VG.Proof.Rsa.X86.BatchLaw] (s : State) (h : (Spec.Rsa.crtValuesContract abi 52).pre s) :
    ∃ trace t, Exec isa code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.crtValuesContract abi 52).post s t := by
  have a := abi_of h
  obtain ⟨trace, t, run, written, preserved⟩ := operation_ok a
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  unfold Written outputBuffers calculated inputBytes CallGeometry.buffer caller at written
  change Spec.Rsa.writtenAll t.mem
    [(VG.Proof.Dsa.X86.argumentPointer s 0, (arg s 1).toNat),
      (VG.Proof.Dsa.X86.argumentPointer s 2, (arg s 3).toNat),
      (VG.Proof.Dsa.X86.argumentPointer s 4, (arg s 5).toNat)] (t.gpr .eax) _ at written
  rw [a.dpLen, a.dqLen, a.qiLen] at written
  exact written

end VG.Proof.Rsa.X86.CrtValues
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86
open VG.Impl.Rsa.X86.CrtValuesRt (code)

/-- Disjoint 512-bit buffers with the contract's full scratch allowance. -/
def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 32
    else if a = 0x2000d then 32
    else if a = 0x20010 then 32
    else if a = 0x20015 then 48
    else if a = 0x20018 then 32
    else if a = 0x2001d then 64
    else if a = 0x20020 then 64
    else if a = 0x20025 then 80
    else if a = 0x20028 then 32
    else if a = 0x2002d then 96
    else if a = 0x20030 then 32
    else if a = 0x20035 then 112
    else if a = 0x20038 then 64
    else if a = 0x2003e then 1
    else if a = 0x20040 then 32
    else if a = 0x20041 then 4 else 0
  rd := [⟨0x4000, 64⟩, ⟨0x5000, 32⟩, ⟨0x6000, 32⟩, ⟨0x7000, 64⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x10000, 8448⟩, ⟨0x20004, 64⟩]

theorem satisfiable : ∃ s, (Spec.Rsa.crtValuesContract abi 52).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 32 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 32 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 32 := by decide
  have a6 : arg satState 6 = 16384 := by decide
  have a7 : arg satState 7 = 64 := by decide
  have a8 : arg satState 8 = 20480 := by decide
  have a9 : arg satState 9 = 32 := by decide
  have a10 : arg satState 10 = 24576 := by decide
  have a11 : arg satState 11 = 32 := by decide
  have a12 : arg satState 12 = 28672 := by decide
  have a13 : arg satState 13 = 64 := by decide
  have a14 : arg satState 14 = 65536 := by decide
  have a15 : arg satState 15 = 1056 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, e, esp, satState, Spec.Rsa.lenValid, Spec.Rsa.scratchWords] using satState

theorem verified [VG.Proof.Rsa.X86.BatchLaw] : Verified target code (Spec.Rsa.crtValuesContract abi 52) :=
  ⟨correct, constantTime, satisfiable⟩

end VG.Proof.Rsa.X86.CrtValues
