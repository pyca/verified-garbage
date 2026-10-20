module
public import VerifiedGarbage.Proof.Rsa.X86.CvABI
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Rsa.X86.CvBuffers
import VerifiedGarbage.Proof.Rsa.X86.CvEntry
import VerifiedGarbage.Proof.Rsa.X86.CvResources

/-! # Install CRT caller resources while saving the callee-saved registers -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.CrtValues

theorem installed_ok {s : State} (a : ABI s) :
    WP isa (.block entry) s fun t => Inputs (caller s) t ∧
      Spill.Saved t.mem (off (caller s).base) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside (caller s).base 0 (caller s).size s.mem t.mem := by
  refine WP.mono (entry_ok (base := (caller s).base) (ptr := arg s 14) (a.stackArgument (by decide : 14 < 16)).readSrc
    rfl a.scratchBound (by have := a.used; omega) (by rw [a.wr]; simp) a.stack)
    fun t ⟨sc, saved, k, o⟩ => ?_
  refine ⟨?_, saved, k, o⟩
  have w := a.width
  refine ⟨⟨sc, a.space, by omega, by omega⟩, w.1, w.2.1, ?_, ?_,
    (fun i => (a.inputLength i).1), (fun i => (a.inputLength i).2), a.inputFit, ?_, ?_,
    (fun i => (a.outputLength i).1), (fun i => (a.outputLength i).2), a.outputFit, ?_, ?_, a.outputSeparate⟩
  · intro i hi
    exact (CallArgument.mk (a.stackArgument hi) rfl).keep k (by decide) o
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, k.1 .esp (by decide)]]
    exact a.stackApart hi hr
  · intro i
    rw [k.2.1, k.2.2]
    exact ⟨_, List.mem_append_left _ (a.inputMember i), Region.contains_self _ _⟩
  · exact fun i r hr => a.inApart _ (a.inputMember i) r hr
  · intro i
    rw [k.2.2, a.wr]
    refine ⟨_, ?_, Region.contains_self _ _⟩
    exact List.mem_append_left [⟨(caller s).base, (caller s).size⟩, ⟨argAddr s 0, 64⟩]
      (ABI.outputMember (s := s) i)
  · exact fun i => a.outScratch _ (ABI.outputMember i)

end VG.Proof.Rsa.X86.CrtValues
