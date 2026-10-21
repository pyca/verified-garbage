module

import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
public import VerifiedGarbage.Proof.MillerRabin.X86.WordPointer
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase

/-! # Exponent loads use the public word counter, even for a secret exponent -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem wordPointer_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi]) (.block wordPointer) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold wordPointer
  refine RelCT.block_append (RelCT.seq
    (pointer_pair_relCT v .ebp aExponent (by decide) (by decide) [.edi] (by decide)) ?_)
  exact (checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi]) rfl rfl).mono
    (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem wordPointer_relCT {g : Geometry} (v : g.Valid) (q : Nat) (positive : 0 < q) (bound : q ≤ g.words) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧
      s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q ∧
      t.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q)
      (.block wordPointer) (VG.X86.Taint.Agree (roundTaint [.edi, .ebp])) := by
  intro s t tr ur u z ⟨H, S, T⟩ E G
  obtain ⟨trace, A⟩ := wordPointer_trace v _ _ _ _ _ _ H E G
  obtain ⟨Pu, _, _⟩ := wp_result (wordPointer_ok v H.1 q positive bound S) E
  obtain ⟨Pz, _, _⟩ := wp_result (wordPointer_ok v H.2.1 q positive bound T) G
  refine ⟨trace, round_add_regs (round_forget A) ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact round_regs A (by decide)
  · exact ptr_agree Pu Pz

theorem loadWord_trace {g : Geometry} (v : g.Valid) (q : Nat) (positive : 0 < q) (bound : q ≤ g.words) :
    RelCT isa (fun s t => Pair g [.edi] s t ∧
      s.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q ∧
      t.mem.readW (off g.W sWords) 32 = BitVec.ofNat 32 q)
      (.block loadWord) (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  change RelCT isa _ (.block (wordPointer ++ [.mov .eax (.mem (at_ .ebp 0)), .store (slot sValue) .eax,
    .mov .eax (.imm 8), .store (slot sWindows) .eax])) _
  exact RelCT.block_append (RelCT.seq (wordPointer_relCT v q positive bound)
    (checkedProgramChange (hint := .block []) (τ' := roundTaint [.edi, .ebp, .eax]) rfl rfl))

end VG.Proof.MillerRabin.X86
