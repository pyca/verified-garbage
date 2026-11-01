module
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedABI
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Bignum.X86.PrecomputedResources
import VerifiedGarbage.Proof.Bignum.X86.PublicEntry

/-! # Install caller resources for checked public RSA with a packed key -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem PrecomputedABI.preBytes {s : State} (A : PrecomputedABI s) :
    (arg s 3).toNat * 8 = 16 * Spec.Rsa.modulusWords (arg s 1).toNat := by
  rw [A.preLength, Spec.Rsa.precomputedWords]
  omega

theorem precomputedInstalled_ok {s : State} (A : PrecomputedABI s) :
    WP isa (.block PublicFn.entry) s fun t =>
      PrecomputedInputs (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 1).toNat (arg s) t ∧
      Spill.Saved t.mem (off (argumentPointer s 8)) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧
      Outside (argumentPointer s 8) 0 ((arg s 9).toNat * 8) s.mem t.mem := by
  refine WP.mono (publicEntry_ok (ptr := arg s 8)
    (A.stackArgument (by decide : 8 < 10)).readSrc rfl A.scratchBound
    (by have := A.used; omega) (by rw [A.wr]; simp) A.stack) ?_
  intro t ⟨Sc, Saved, K, O⟩
  refine ⟨?_, Saved, K, O⟩
  refine ⟨Sc, A.lengths.1, A.lengths.2, A.space, ?_, ?_, ?_, ?_, A.ePositive,
    A.eLength, A.outBound, ?_, A.eBound, ?_, ?_, ?_, ?_, ?_, A.outScratch.symm, ?_, A.eScratch, ?_⟩
  · intro i hi
    exact (CallArgument.mk (A.stackArgument hi) rfl).keep K (by decide) O
  · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change arg s 3 = BitVec.ofNat 32 (Spec.Rsa.precomputedWords (arg s 1).toNat)
    rw [← A.preLength]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [← A.inLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← A.preBytes]; exact A.preBound
  · rw [← A.inLength]; exact A.inBound
  · rw [K.2.2, A.wr]
    exact ⟨⟨argumentPointer s 0, (arg s 1).toNat⟩, List.mem_cons_self, Region.contains_self _ _⟩
  · rw [K.2.1, K.2.2, A.rd, A.wr, ← A.preBytes]
    exact ⟨⟨argumentPointer s 2, (arg s 3).toNat * 8⟩, by simp, Region.contains_self _ _⟩
  · rw [K.2.1, K.2.2, A.rd, A.wr]
    exact ⟨⟨argumentPointer s 4, (arg s 5).toNat⟩, by simp, Region.contains_self _ _⟩
  · rw [K.2.1, K.2.2, A.rd, A.wr, ← A.inLength]
    exact ⟨⟨argumentPointer s 6, (arg s 7).toNat⟩, by simp, Region.contains_self _ _⟩
  · rw [← A.preBytes]; exact A.preScratch
  · rw [← A.inLength]; exact A.inScratch

end VG.Proof.Bignum.X86
