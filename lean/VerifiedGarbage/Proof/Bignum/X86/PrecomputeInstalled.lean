module
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeABI
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Bignum.X86.PrecomputeResources
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeEntry
import VerifiedGarbage.Proof.Framework.Offset

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
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have sa : VG.Proof.Dsa.X86.stackAddress t 1 = VG.Proof.Dsa.X86.stackAddress s 1 := by
    simp only [VG.Proof.Dsa.X86.stackAddress, esp]
  have bound := A.stackBound
  have P : VG.Proof.Dsa.X86.stackAddress s 1 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 8 :=
    addr_eq (by omega)
  have Z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  have sub : Region.Sub ⟨VG.Proof.Dsa.X86.stackAddress s 1, 4⟩ ⟨argAddr s 0, 24⟩ := by
    rw [P, Z]; exact Offset.sub _ (by omega) (by omega)
  refine ⟨Sc, A.lengths.1, A.lengths.2, A.space, ?_, ?_, ?_, ?_, A.nBound, ?_, ?_, ?_, A.nScratch,
    ⟨by rw [esp]; exact A.stackLow, by
      rw [esp]; simp only [below]; rw [VG.X86.Taint.sub_setWidth A.stackLow]; exact A.belowScratch⟩,
    by rw [esp]; omega,
    by simp only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 4).isLt (by decide : 2 ^ 32 < 2 ^ 64))], rfl,
    by rw [sa, K.2.2, A.wr]; exact ⟨⟨argAddr s 0, 24⟩, by simp, by rw [P, Z]; exact Offset.contains _ (by omega) (by omega) (by omega)⟩,
    by rw [sa]; exact A.nArgs.sub_right sub,
    by simp only [argAddr, esp]; rw [← A.outputBytes]; exact A.outArgs,
    by rw [esp]; exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) A.retScratch A.scratchArgs.symm,
    by rw [esp, ← A.outputBytes]; exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) A.retOut A.outArgs.symm⟩
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
