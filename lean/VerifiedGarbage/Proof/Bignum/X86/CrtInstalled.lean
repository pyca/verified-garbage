module
public import VerifiedGarbage.Proof.Bignum.X86.CrtABI
public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Bignum.X86.CrtResources
import VerifiedGarbage.Proof.Bignum.X86.CrtEntry

/-! # Install all caller resources for the private CRT operation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Impl.Bignum.X86

theorem installed_ok {s : State} (A : CrtABI s) :
    WP isa (.block Crt.entry) s fun t =>
      Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) t ∧
      Spill.Saved t.mem (off (argumentPointer s 16)) s.gpr Crt.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧
      Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) s.mem t.mem := by
  refine WP.mono (entry_ok (ptr := arg s 16)
    (A.stackArgument (by decide : 16 < 18)).readSrc rfl A.scratchBound
    (by have := A.used; omega) (by rw [A.wr]; simp) A.stack) ?_
  intro t ⟨Sc, Saved, K, O⟩
  refine ⟨?_, Saved, K, O⟩
  refine ⟨Sc, A.lengths.1, A.lengths.2, A.space, ?_, ?_, ?_, ?_, A.pLength, A.qLength,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [K.1 _ (by decide)]; exact A.room, by rw [K.1 _ (by decide)]; exact A.stackBound⟩
  · intro i hi
    exact (CallArgument.mk (A.stackArgument hi) rfl).keep K (by decide) O
  · simp only [← A.outLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [← A.inLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact BitVec.eq_of_toNat_eq A.dpLength
  · exact BitVec.eq_of_toNat_eq A.dqLength
  · exact BitVec.eq_of_toNat_eq A.qiLength
  · rw [← A.outLength]; exact A.outBound
  · rw [K.2.2, A.wr, ← A.outLength]
    exact ⟨⟨argumentPointer s 0, (arg s 1).toNat⟩, List.mem_cons_self, Region.contains_self _ _⟩
  · rw [← A.outLength]; exact A.outScratch.symm
  · intro i hi
    have := A.lengths.1
    have := A.inLength
    have := A.pPositive
    have := A.qPositive
    have := A.dpLength
    have := A.dqLength
    have := A.qiLength
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceAdd] <;> omega
  · intro i hi
    have := A.inLength
    have := A.pLength
    have := A.qLength
    have := A.dpLength
    have := A.dqLength
    have := A.qiLength
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reduceAdd] <;> omega
  · intro i hi
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nBound
    · exact A.inBound
    · exact A.pBound
    · exact A.qBound
    · exact A.dpBound
    · exact A.dqBound
    · exact A.qiBound
  · intro i hi
    rw [K.2.1, K.2.2, A.rd, A.wr]
    refine ⟨⟨argumentPointer s i, (arg s (i + 1)).toNat⟩, ?_, Region.contains_self _ _⟩
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro i hi
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nScratch
    · exact A.inScratch
    · exact A.pScratch
    · exact A.qScratch
    · exact A.dpScratch
    · exact A.dqScratch
    · exact A.qiScratch

end VG.Proof.Bignum.X86.Crt
