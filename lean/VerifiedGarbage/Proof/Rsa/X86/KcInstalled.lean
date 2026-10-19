module

public import VerifiedGarbage.Proof.Rsa.X86.KcBuffers
public import VerifiedGarbage.Proof.Rsa.X86.KcEntry

/-! # Install key-check call resources after saving the caller's registers -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.KeyCheck

theorem installed_ok {full : Bool} {s : State} (a : ABI full s) :
    WP isa (.block (entry full)) s fun t => Inputs (caller full s) t ∧
      Spill.Saved t.mem (off (caller full s).base) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside (caller full s).base 0 (caller full s).size s.mem t.mem := by
  refine WP.mono (entry_ok full (base := (caller full s).base) (ptr := arg s (scratchArg full))
    (a.stackArgument (by omega : scratchArg full < scratchArg full + 2)).readSrc
    rfl a.scratchBound (by have := a.used; omega) (by rw [a.wr]; simp) a.stack)
    fun t ⟨sc, saved, k, o⟩ => ?_
  refine ⟨?_, saved, k, o⟩
  have w := a.width
  refine ⟨⟨sc, a.space, by omega, by omega⟩, w.1, w.2.1, ?_, ?_,
    (fun i hi => (a.inputLength hi).1), (fun i hi => (a.inputLength hi).2),
    (fun i hi => a.inputFit hi), ?_, ?_⟩
  · intro i hi
    exact (CallArgument.mk (a.stackArgument hi) rfl).keep k (by decide) o
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, k.1 .esp (by decide)]]
    exact a.stackApart hi hr
  · intro i hi
    rw [k.2.1, k.2.2]
    exact ⟨_, List.mem_append_left _ (a.inputMember hi), Region.contains_self _ _⟩
  · intro i hi r hr
    simp only [CallGeometry.writes, List.mem_singleton] at hr
    subst r
    exact a.inApart _ (a.inputMember hi)
end VG.Proof.Rsa.X86.KeyCheck
