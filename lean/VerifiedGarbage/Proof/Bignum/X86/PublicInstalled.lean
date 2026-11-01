module
public import VerifiedGarbage.Proof.Bignum.X86.PublicABI
public import VerifiedGarbage.Proof.Bignum.X86.PublicInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Bignum.X86.PublicResources
import VerifiedGarbage.Proof.Bignum.X86.PublicEntry

/-! # Installing the checked public operation's caller resources -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem publicInstalled_ok {s : State} (A : PublicABI s) :
    WP isa (.block PublicFn.entry) s fun t =>
      PublicInputs (argumentPointer s 8) ((arg s 9).toNat * 8) (arg s 3).toNat (arg s) t ∧
      Spill.Saved t.mem (off (argumentPointer s 8)) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧
      Outside (argumentPointer s 8) 0 ((arg s 9).toNat * 8) s.mem t.mem := by
  refine WP.mono (publicEntry_ok (ptr := arg s 8)
    (A.stackArgument (by decide : 8 < 10)).readSrc rfl A.scratchBound
    (by have := A.used; omega) (by rw [A.wr]; simp) A.stack) ?_
  intro t ⟨Sc, Saved, K, O⟩
  refine ⟨?_, Saved, K, O⟩
  refine ⟨Sc, A.lengths.1, A.lengths.2, A.space, ?_, ?_, ?_, ?_, A.ePositive,
    A.eLength, ?_, A.nBound, A.eBound, ?_, ?_, ?_, ?_, ?_, ?_, A.nScratch,
    A.eScratch, ?_⟩
  · intro i hi
    exact (CallArgument.mk (A.stackArgument hi) rfl).keep K (by decide) O
  · simp only [← A.outLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [← A.inLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← A.outLength]; exact A.outBound
  · rw [← A.inLength]; exact A.inBound
  · rw [K.2.2, A.wr, ← A.outLength]
    exact ⟨⟨argumentPointer s 0, (arg s 1).toNat⟩, List.mem_cons_self, Region.contains_self _ _⟩
  · rw [K.2.1, K.2.2, A.rd, A.wr]
    exact ⟨⟨argumentPointer s 2, (arg s 3).toNat⟩, by simp, Region.contains_self _ _⟩
  · rw [K.2.1, K.2.2, A.rd, A.wr]
    exact ⟨⟨argumentPointer s 4, (arg s 5).toNat⟩, by simp, Region.contains_self _ _⟩
  · rw [K.2.1, K.2.2, A.rd, A.wr, ← A.inLength]
    exact ⟨⟨argumentPointer s 6, (arg s 7).toNat⟩, by simp, Region.contains_self _ _⟩
  · rw [← A.outLength]; exact A.outScratch.symm
  · rw [← A.inLength]; exact A.inScratch

end VG.Proof.Bignum.X86
