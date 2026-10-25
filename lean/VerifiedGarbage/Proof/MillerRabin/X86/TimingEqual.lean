module

import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
public import VerifiedGarbage.Proof.MillerRabin.X86.EqualLoop
import VerifiedGarbage.Proof.MillerRabin.X86.Equal
import VerifiedGarbage.Proof.MillerRabin.X86.Data
import VerifiedGarbage.Proof.MillerRabin.X86.TimingReadonly
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Full-width equality scans use public addresses and counters -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

def equalRegisters : List Reg := [.esi, .ecx, .ebp, .edi]

theorem equalZero_relCT {g : Geometry} :
    RelCT isa (Pair g equalRegisters) (.block [.mov .ebx (.imm 0)]) (Pair g equalRegisters) := by
  refine readonly_relCT (checkedProgramChange (hint := .block [])
    (τ' := roundTaint (.ebx :: equalRegisters)) (by kernel_rfl) (by kernel_rfl)) ?_
  intro s _
  exact wp_movS rfl fun t T _ => WP.block_nil ⟨T.mem, T.keeps.mono (by decide)⟩

theorem equalLoop_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint equalRegisters))
    (.loop (.block equalBody) .ne) (VG.X86.Taint.Agree (roundTaint equalRegisters)) :=
  checkedProgramChange (τ' := roundTaint equalRegisters true)
    (hint := VG.Taint.hintOf taint (roundTaint equalRegisters) (.loop (.block equalBody) .ne)) (by kernel_rfl) (by kernel_rfl)

theorem equalFinish_raw (result : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
      (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1), .alu .adc .eax (.imm 0), .store (slot result) .eax])
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block [.mov .eax (.imm 0), .alu .sub .ebx (.imm 1),
    .alu .adc .eax (.imm 0), .store (slot 0) .eax]) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem equal_trace {g : Geometry} (v : g.Valid) (result a b : Nat) (ai : a < 28) (bi : b < 28) :
    RelCT isa (Pair g [.edi]) (equal result a b) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold equal
  simp only [List.append_assoc]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp a (by decide) ai [.edi] (by decide))
    (RelCT.block_append (RelCT.seq
      (pointer_pair_relCT v .ecx b (by decide) bi [.ebp, .edi] (by decide))
      (RelCT.block_append (RelCT.seq
        (words_pair_relCT v [.ecx, .ebp, .edi] (by decide)) equalZero_relCT)))))) ?_
  refine RelCT.seq (equalLoop_raw.mono (P' := Pair g equalRegisters) (fun _ _ H => H.2.2) (fun _ _ H => H)) ?_
  exact (equalFinish_raw result).mono (fun _ _ H => round_add_regs (round_forget H) fun r mem =>
    round_regs H (by obtain rfl := List.mem_singleton.mp mem; decide)) (fun _ _ H => H)

theorem equal_relCT {g : Geometry} (v : g.Valid) (result a b : Nat)
    (scratch : scratchWord result) (ai : a < 28) (bi : b < 28) :
    RelCT isa (Pair g [.edi]) (equal result a b) (Pair g [.edi]) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := equal_trace v result a b ai bi _ _ _ _ _ _ H E G
  have fit : result + 4 ≤ g.L := Nat.le_trans (scratch_fit scratch) v.headerFit
  obtain ⟨_, Ou, Ku⟩ := wp_result (equal_ok v H.1 result a b fit ai bi) E
  obtain ⟨_, Oz, Kz⟩ := wp_result (equal_ok v H.2.1 result a b fit ai bi) G
  exact ⟨trace, H.1.keepScalar Ku (by decide) Ou scratch, H.2.1.keepScalar Kz (by decide) Oz scratch, A⟩

end VG.Proof.MillerRabin.X86
