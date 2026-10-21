module

import VerifiedGarbage.Proof.Mont.X86.Compact.TimingValue
import VerifiedGarbage.Proof.Mont.X86.Compact.SubAll
import VerifiedGarbage.Proof.Mont.X86.Compact.TimingKernels
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingLift

/-! # Direct subtraction leaks neither the Montgomery product nor its borrow -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86

def BorrowPair (g : Geometry) (s t : State) : Prop :=
  WindowPair g (g.S + Compact.accOff + 8 * g.N) s t ∧
    (∃ c, s.gpr .ecx = cmask c) ∧ (∃ c, t.gpr .ecx = cmask c)

theorem zeroBorrow_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.edi, .ebx, .esi, .ebp]) (.block [.mov .ecx (.imm 0)]) (Pair g [.edi, .ebx, .esi, .ebp]) := by
  refine lift_readonly v (checkedProgramChange (hint := .block [])
    (τ' := timingTaint [.edi, .ebx, .esi, .ebp, .ecx]) rfl rfl) ?_
  intro s
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨T.mem, T.keeps.mono (by decide)⟩

theorem subM_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (Pair g [.ebp, .edi]) Compact.subM (VG.X86.Taint.Agree (timingTaint [])) := by
  have header : 128 ≤ g.L := by have := v.lay.header; have := v.lay.scr; omega
  have first : RelCT isa (Pair g [.ebp, .edi]) (.block (Compact.arrayPtr .esi 0)) (Pair g [.esi, .ebp]) :=
    (arrayPointer_relCT v .esi 0 ((g.W.toNat + g.mo) % 2 ^ 32) modulusSubPtr_relCT
      (by omega) (fun _ C => C.metadata.modulus) (by decide) (by decide)).mono
      (fun _ _ H => pair_regs H (by decide)) (fun _ _ H => H)
  have output : RelCT isa (Pair g [.esi, .ebp]) (.block (Compact.operandPtr .ebx 2 .edx)) (Pair g [.ebx, .esi, .ebp]) :=
    operandPointer_relCT v .ebx .edx 2 ((g.W.toNat + g.o) % 2 ^ 32) outPtr_relCT
      (by decide) (by decide) (by decide) (by intro _ _; have := v.outIndex; omega)
      (fun _ C => C.outPtr) (by decide) (by decide)
  unfold Compact.subM
  simp only [List.append_assoc]
  refine RelCT.seq (RelCT.block_append (RelCT.seq first (RelCT.block_append (RelCT.seq output
    (RelCT.block_append (RelCT.seq
      (length_relCT v .edi .eax 0 outputLength_relCT (by decide) (by decide)) (zeroBorrow_relCT v))))))) ?_
  refine RelCT.seq (subLoop_relCT.mono (fun _ _ H => H.2.2) (fun _ _ H => H)) ?_
  exact scratchPtr_relCT.mono (fun _ _ H => timing_forget H) (fun _ _ H => H)

theorem subM_relCT {g : Geometry} (v : g.Valid) :
    RelCT isa (WindowPair g (g.S + Compact.accOff + 4 * g.N)) Compact.subM (BorrowPair g) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := subM_trace v _ _ _ _ _ _ H.1 E G
  have fit := v.lay.scr
  have header := v.lay.header
  have acc : Compact.accOff = 24 := rfl
  obtain ⟨Ou, ⟨cu, Cu, _⟩, Bu, Du, Ku⟩ := wp_result (subAll_ok H.1.1.ws H.1.1.args v.base H.1.1.metadata
    (by omega) v.outIndex H.1.1.outPtr v.positive v.n32 (by omega) v.lay.mo_le v.outFit
    v.outHeader (by have := v.outScratch; omega) v.outMod H.2.2.2.1) E
  obtain ⟨Oz, ⟨cz, Cz, _⟩, Bz, Dz, Kz⟩ := wp_result (subAll_ok H.1.2.1.ws H.1.2.1.args v.base H.1.2.1.metadata
    (by omega) v.outIndex H.1.2.1.outPtr v.positive v.n32 (by omega) v.lay.mo_le v.outFit
    v.outHeader (by have := v.outScratch; omega) v.outMod H.2.2.2.2) G
  have writes {m m' : Mem} (O : Outside g.W g.o (4 * g.N) m m') : Outs g.W g.writes m m' :=
    Outs.of_outside O (by change (g.o, 4 * g.N) ∈ [(g.S, 8 * g.N + 28), (g.o, 4 * g.N)]; simp)
  have P : Pair g [.ebp, .edi] u z := by
    refine ⟨H.1.1.keep v Ku (by decide) (writes Ou) A.wf₁,
      H.1.2.1.keep v Kz (by decide) (writes Oz) A.wf₂, ?_⟩
    apply timing_add_regs A
    intro r member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (Bu.trans Bz.symm)
    · exact BitVec.eq_of_toNat_eq (Du.trans Dz.symm)
  exact ⟨trace, ⟨P, Du, Dz, Bu, Bz⟩, ⟨cu, Cu⟩, ⟨cz, Cz⟩⟩

end VG.Proof.Mont.X86.Compact
