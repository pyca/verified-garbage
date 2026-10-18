module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeResources
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeEntry

/-! # Install the precomputation workspace from the shared contract -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem PrecomputeABI.outputBytes {s : State} (A : PrecomputeABI s) :
    (arg s 1).toNat * 8 = 16 * Spec.Rsa.modulusWords (arg s 3).toNat := by
  rw [A.preLength, Spec.Rsa.precomputedWords]
  omega

theorem precomputeInstalled_ok {s : State} (A : PrecomputeABI s) :
    WP isa (.block PrecomputeFn.entry) s fun t =>
      PrecomputeInputs (argumentPointer s 4) ((arg s 5).toNat * 8) (arg s 3).toNat (arg s) t ∧
      Spill.Saved t.mem (off (argumentPointer s 4)) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧
      Outside (argumentPointer s 4) 0 ((arg s 5).toNat * 8) s.mem t.mem := by
  refine WP.mono (precomputeEntry_ok (ptr := arg s 4)
    (A.stackArgument (by decide : 4 < 6)).readSrc rfl A.scratchBound
    (by have := A.used; omega) (by rw [A.wr]; simp) A.stack) ?_
  intro t ⟨Sc, Saved, K, O⟩
  refine ⟨?_, Saved, K, O⟩
  refine ⟨Sc, A.lengths.1, A.lengths.2, A.space, ?_, ?_, ?_, ?_, A.nBound, ?_, ?_, ?_, A.nScratch⟩
  · intro i hi
    exact (CallArgument.mk (A.stackArgument hi) rfl).keep K (by decide) O
  · change arg s 1 = BitVec.ofNat 32 (Spec.Rsa.precomputedWords (arg s 3).toNat)
    rw [← A.preLength]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← A.outputBytes]; exact A.outBound
  · rw [K.2.2, A.wr, ← A.outputBytes]
    exact ⟨⟨argumentPointer s 0, (arg s 1).toNat * 8⟩, List.mem_cons_self, Region.contains_self _ _⟩
  · rw [K.2.1, K.2.2, A.rd, A.wr]
    exact ⟨⟨argumentPointer s 2, (arg s 3).toNat⟩, by simp, Region.contains_self _ _⟩
  · rw [← A.outputBytes]; exact A.outScratch.symm

end VG.Proof.Bignum.X86
