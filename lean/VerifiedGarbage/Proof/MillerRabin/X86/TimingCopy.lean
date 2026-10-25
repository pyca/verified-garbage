module

import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
public import VerifiedGarbage.Proof.MillerRabin.X86.CopyLoop
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Array copies visit the same native-word addresses for every candidate -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

def copyRegisters : List Reg := [.esi, .ebx, .ebp, .edi]

theorem copyLoop_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint copyRegisters))
    (.loop (.block copyBody) .ne) (VG.X86.Taint.Agree (roundTaint copyRegisters)) :=
  checkedProgramChange (τ' := roundTaint copyRegisters true)
    (hint := VG.Taint.hintOf taint (roundTaint copyRegisters) (.loop (.block copyBody) .ne)) (by kernel_rfl) (by kernel_rfl)

theorem copy_trace {g : Geometry} (v : g.Valid) (dst src : Nat) (di : dst < 28) (si : src < 28) :
    RelCT isa (Pair g [.edi]) (copy dst src) (VG.X86.Taint.Agree (roundTaint copyRegisters)) := by
  unfold copy
  rw [List.append_assoc]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp dst (by decide) di [.edi] (by decide))
    (RelCT.block_append (RelCT.seq
      (pointer_pair_relCT v .ebx src (by decide) si [.ebp, .edi] (by decide))
      (words_pair_relCT v [.ebx, .ebp, .edi] (by decide)))))) ?_
  exact copyLoop_raw.mono (P' := Pair g copyRegisters) (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem copy_relCT {g : Geometry} (v : g.Valid) (dst src : Nat) (di : dst < 28) (si : src < 28) :
    RelCT isa (Pair g [.edi]) (copy dst src) (Pair g [.edi]) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := copy_trace v dst src di si _ _ _ _ _ _ H E G
  obtain ⟨_, _, _, Cu⟩ := wp_result (copy_ok v H.1 dst src di si) E
  obtain ⟨_, _, _, Cz⟩ := wp_result (copy_ok v H.2.1 dst src di si) G
  refine ⟨trace, Cu, Cz, round_add_regs (round_forget A) ?_⟩
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact round_regs A (by decide : .edi ∈ copyRegisters)

end VG.Proof.MillerRabin.X86
