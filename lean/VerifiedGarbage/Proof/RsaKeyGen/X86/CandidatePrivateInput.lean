module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext

/-! # The single private call frame establishes every prepared-loop input -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem private_input {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (D : Drawn E eBytes pBytes entropy s)
    (minusOne : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1)
    (S : Scr t E.base E.size) (C : Caller E.geometry E.capacity (E.p - 28#32) t)
    (F : Frame [below E.p 28] s.mem t.mem) (K : Keeps [.edx] (allocFrame 28 s) t) :
    CandidatePrepare.Input (E.parameters entropy) t := by
  have workspaceFar : E.workspaceRegion.Disjoint (below E.p 28) :=
    (v.stackFar E.workspaceRegion (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right
      (below_sub (by decide) v.low)
  have randFar : E.randRegion.Disjoint (below E.p 28) :=
    (v.stackFar E.randRegion (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right
      (below_sub (by decide) v.low)
  have W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame F D.input.scratch.nowrap
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  have top : 2 ^ (64 * E.width - 1) ≤ candidateValue E entropy := by
    have lower := (candidate_shape v entropy).2.1
    have width := v.width_bounds.1
    have eqPower : 2 ^ (64 * E.width - 1) = 2 ^ (64 * E.width - 2) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    rw [eqPower]
    omega
  refine ⟨⟨S, C, ?_, ?_, candidate_odd v entropy, by change 1 < candidateValue E entropy; have := candidate_large v entropy; omega, top⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have value := W.val32 (v.geometry.arrayFit (j := 0) (by decide)) (by intro r mem; cases mem)
    rw [← Prepared.slot_eq] at value
    exact value.trans D.candidate
  · have value := W.val32 (v.geometry.arrayFit (j := 5) (by decide)) (by intro r mem; cases mem)
    rw [← Prepared.slot_eq] at value
    exact value.trans minusOne
  · rw [K.2.1, K.2.2]
    obtain ⟨r, mem, contains⟩ := D.input.memory.randRead
    refine ⟨r, ?_, contains⟩
    change r ∈ s.rd ++ (⟨(s.gpr .esp - 28#32).setWidth 64, 28⟩ :: s.wr)
    exact (List.mem_append.mp mem).elim (List.mem_append_left _) (fun known => List.mem_append_right _ (List.mem_cons_of_mem _ known))
  · change Spec.Rsa.bytesAt t.mem (E.rand.setWidth 64) E.randLength = entropy
    rw [VG.Proof.RsaKeyGen.frame_bytesAt F
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact randFar) (by have := v.randLengthFit; omega)]
    exact D.input.memory.entropy
  · exact (W.read32 (d := 28) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 28 + 4 ≤ E.size; omega)
      (by intro r mem; cases mem)).trans D.input.rand_eq
  · have word := W.read32 (d := 32) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 32 + 4 ≤ E.size; omega)
      (by intro r mem; cases mem)
    exact (congrArg BitVec.toNat word).trans (D.input.randLength_eq v)
  · have word := W.read32 (d := 152) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 152 + 4 ≤ E.size; omega)
      (by intro r mem; cases mem)
    change (t.mem.readW (off E.base 152) 32).toNat = 8 * E.width
    rw [v.length_eq]
    exact (congrArg BitVec.toNat word).trans D.used

end VG.Proof.RsaKeyGen.X86.Candidate
