module

import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase

/-! # The secret exponent marker is read at its fixed public-width address -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem markerPointer_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi]) (.block markerPointer) (VG.X86.Taint.Agree (roundTaint [.edi, .ebp])) := by
  unfold markerPointer
  rw [List.append_assoc]
  refine RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp aExponent (by decide) (by decide) [.edi] (by decide))
    (RelCT.block_append (RelCT.seq (words_pair_relCT v [.ebp, .edi] (by decide)) ?_)))
  exact (checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi, .ebp, .esi, .eax] true) rfl rfl).mono
    (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem markerCalc_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi, .ebp]))
    (.block markerCalc) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi, .ebp]) rfl rfl

theorem lastSquares_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi]) (.block lastSquares) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold lastSquares
  rw [List.append_assoc]
  exact RelCT.block_append (RelCT.seq (markerPointer_trace v)
    (RelCT.block_append (RelCT.seq markerCalc_trace (checkedBlockInvariant rfl rfl))))

theorem initWindows_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block initWindows) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant (τ' := roundTaint [.edi, .eax]) rfl rfl

end VG.Proof.MillerRabin.X86
