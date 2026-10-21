module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.FrameOutside
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment

/-! # The candidate body draws exactly its first entropy block -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def candidateValue (E : Environment) (entropy : List Byte) : Nat :=
  Spec.RsaKeyGen.candidate (8 * E.length) (Spec.Rsa.os2ip (entropy.take E.length))

structure Drawn (E : Environment) (eBytes pBytes entropy : List Byte) (s : State) : Prop where
  input : Input E eBytes pBytes entropy s
  candidate : val32 s.mem E.base (slot E.width 0) (2 * E.width) = candidateValue E entropy
  used : w32 s.mem E.base 152 = E.length
  zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0

theorem load_ok {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (I : Input E eBytes pBytes entropy s)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0)
    (enough : E.length ≤ E.randLength) :
    WP isa (VG.Impl.RsaKeyGen.X86.CandidateLoad.code E.width) s fun t =>
      Drawn E eBytes pBytes entropy t ∧ WorkFrame E s.mem t.mem ∧ Keeps [.eax, .ebx, .esi, .ecx] s t := by
  have width := v.width_bounds.1
  have space : 256 ≤ E.size := v.geometry.headerFit
  have outFit := v.slotFit (j := 0) (by decide)
  have length := v.length_eq
  have read : InRegions (s.rd ++ s.wr) (E.rand.setWidth 64) (8 * E.width) := by
    obtain ⟨r, mem, contains⟩ := I.memory.randRead
    refine ⟨r, mem, ?_⟩
    change (E.rand.setWidth 64 - r.base).toNat + 8 * E.width ≤ r.len
    change (E.rand.setWidth 64 - r.base).toNat + E.randLength ≤ r.len at contains
    omega
  have separate : (⟨E.rand.setWidth 64, 8 * E.width⟩ : Region).Disjoint E.workspaceRegion :=
    (v.readWorkspace (r := E.randRegion) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).sub_left
      (Region.sub_prefix (by omega))
  have firstBytes : Spec.Rsa.bytesAt s.mem (E.rand.setWidth 64) E.length = entropy.take E.length := by
    have first := VG.Proof.RsaKeyGen.seg_bytesAt s.mem (E.rand.setWidth 64) (a := 0) (n := E.length) (k := E.randLength) (by omega)
    rw [I.memory.entropy] at first
    simpa only [VG.Proof.RsaKeyGen.seg, List.drop_zero, show BitVec.ofNat 64 0 = 0#64 from rfl,
      BitVec.add_zero] using first.symm
  refine WP.mono_syms (CandidateLoad.code_ok I.scratch (by omega) (by omega) outFit
    (by have := v.randFit; omega) I.rand_eq read separate) fun t ⟨value, count, F, K⟩ syms => ?_
  have O : Outs E.base [(slot E.width 0, 8 * E.width), (152, 8)] s.mem t.mem :=
    VG.Proof.RsaKeyGen.frame_outs F (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> change _ ≤ 2 ^ 64 <;> have := I.scratch.nowrap <;> omega)
  have W : WorkspaceFrame E.geometry [(slot E.width 0, 8 * E.width), (152, 8)] s.mem t.mem :=
    WorkspaceFrame.of_outs I.scratch.nowrap O
  have frame : WorkFrame E s.mem t.mem := F.sub (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact ⟨E.workspaceRegion, List.mem_cons_self, Offset.sub_base E.base outFit⟩
    · exact ⟨E.workspaceRegion, List.mem_cons_self, Offset.sub_base E.base (by change 152 + 8 ≤ E.size; omega)⟩)
  have J := I.keepWorkspace v K (by decide) (by decide) frame W (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact Nat.le_trans (by decide) (E.slotHeader 0)
    · decide) (by rw [syms])
  refine ⟨⟨J, ?_, ?_, (frame.output v).trans zeros⟩, frame, K⟩
  · rw [show 64 * E.width = 8 * E.length by omega, length, firstBytes] at value
    exact value
  · rw [length] at count
    exact count_low v count

end VG.Proof.RsaKeyGen.X86.Candidate
