module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
public import VerifiedGarbage.Proof.MillerRabin.X86.SelectLoop
import VerifiedGarbage.Proof.MillerRabin.X86.Select
import VerifiedGarbage.Proof.MillerRabin.X86.TimingReadonly
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers

/-! # Masked selection reads every word at the same public addresses -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem loadMask_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g copyRegisters) (.block [.mov .ecx (.mem (slot sEq1))]) (Pair g copyRegisters) := by
  refine readonly_relCT (checkedBlockInvariant rfl rfl) ?_
  intro s C
  exact wp_movS (readSrc_ptr C.ws C.base (d := sEq1) (by have := v.headerFit; unfold sEq1; omega))
    fun t T _ => WP.block_nil ⟨T.mem, T.keeps.mono (by decide)⟩

theorem selectLoop_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint copyRegisters))
    (.loop (.block selectBody) .ne) (VG.X86.Taint.Agree (roundTaint copyRegisters)) :=
  checkedProgramChange (τ' := roundTaint copyRegisters true)
    (hint := VG.Taint.hintOf taint (roundTaint copyRegisters) (.loop (.block selectBody) .ne)) rfl rfl

theorem selectEntry_trace {g : Geometry} (v : g.Valid) (j : Nat) (digit : j < 16) :
    RelCT isa (Pair g [.edi]) (selectEntry j) (VG.X86.Taint.Agree (roundTaint copyRegisters)) := by
  unfold selectEntry
  simp only [List.append_assoc]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp (aTable + j) (by decide) (by unfold aTable; omega) [.edi] (by decide))
    (RelCT.block_append (RelCT.seq
      (pointer_pair_relCT v .ebx aX (by decide) (by decide) [.ebp, .edi] (by decide))
      (RelCT.block_append (RelCT.seq
        (words_pair_relCT v [.ebx, .ebp, .edi] (by decide)) (loadMask_relCT v))))))) ?_
  exact selectLoop_raw.mono (P' := Pair g copyRegisters) (fun _ _ H => H.2.2) (fun _ _ H => H)

def masked (g : Geometry) (s : State) : Prop :=
  ∃ bit : Bool, s.mem.readW (off g.W sEq1) 32 = if bit then BitVec.allOnes 32 else 0#32

theorem selectEntry_relCT {g : Geometry} (v : g.Valid) (j : Nat) (digit : j < 16) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧ masked g s ∧ masked g t)
      (selectEntry j) (Pair g [.edi]) := by
  intro s t tr ur u z ⟨H, ⟨bs, Ms⟩, ⟨bt, Mt⟩⟩ E G
  obtain ⟨trace, A⟩ := selectEntry_trace v j digit _ _ _ _ _ _ H E G
  obtain ⟨_, _, _, Cu⟩ := wp_result (selectEntry_ok v H.1 j digit bs Ms) E
  obtain ⟨_, _, _, Cz⟩ := wp_result (selectEntry_ok v H.2.1 j digit bt Mt) G
  refine ⟨trace, Cu, Cz, round_add_regs (round_forget A) ?_⟩
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  exact round_regs A (by decide : .edi ∈ copyRegisters)

end VG.Proof.MillerRabin.X86
