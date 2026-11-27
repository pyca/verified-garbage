module

public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext
public import VerifiedGarbage.Proof.Dsa.X86.StackArgument
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! ### `Bignum.X86.PrecomputeEntry`, which this module and modules that import it used -/

section

/-! # Establishing the arithmetic workspace while preserving the caller ABI -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86

theorem precomputeEntry_ok {s : State} {base : Addr} {size : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (PublicFn.argument 4)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 16 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size) :
    WP isa (.block PrecomputeFn.entry) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 size s.mem t.mem := by
  unfold PrecomputeFn.entry
  simp only [List.singleton_append]
  refine wp_movS read fun u U _ => ?_
  refine WP.block_append (WP.mono (entrySave_ok (base := base) (size := size) (by rw [U.gpr]; exact hb)
    (by rw [U.gpr]; exact hf) hz (by rw [U.wr]; exact hw)) fun v ⟨G, Rd, Wr, S, F⟩ => ?_)
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [T.gpr, G, U.gpr]; exact hb
    · rw [T.wr, Wr, U.wr]; exact hw
    · rw [← hb, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ptr.isLt (by decide))]
      exact hf
    · rw [T.other _ (by decide), G, U.other _ (by decide)]
      exact stk
  · intro p hp
    rw [T.mem, S p hp]
    have H : p.1 ≠ .eax := by
      simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    exact U.other _ H
  · refine ⟨?_, ?_, ?_⟩
    · intro reg hr
      rw [T.other reg (by intro H; subst reg; exact hr (by simp)), G]
      exact U.other reg (by intro H; subst reg; exact hr (by simp))
    · rw [T.rd, Rd, U.rd]
    · rw [T.wr, Wr, U.wr]
  · intro a ha
    rw [T.mem]
    have H : ¬ InRegions [⟨base, size⟩] a 1 := by
      simp only [InRegions, List.mem_singleton, exists_eq_left, Region.Contains]
      change ¬ (ofs base a + 1 ≤ size)
      omega_using [ha]
    exact (F a (by intro reg hreg hcontains; exact H ⟨reg, hreg, hcontains⟩)).trans (congrFun U.mem a)

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.PrecomputeResources`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.PrecomputeABI`, which this module and modules that import it used -/

section

/-! # Caller resources for public RSA precomputation -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure PrecomputeABI (s : State) : Prop where
  stackLow : 96 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat * 8⟩,
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩, ⟨argAddr s 0, 24⟩]
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  retOut : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩
  outBound : (arg s 0).toNat + (arg s 1).toNat * 8 ≤ 2 ^ 32
  nScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  scratchArgs : (⟨argumentPointer s 4, (arg s 5).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩ : Region).Disjoint
    ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩
  nArgs : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩
  outArgs : (⟨argumentPointer s 0, (arg s 1).toNat * 8⟩ : Region).Disjoint ⟨argAddr s 0, 24⟩
  nBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  scratchBound : (arg s 4).toNat + (arg s 5).toNat * 8 ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 3).toNat
  preLength : (arg s 1).toNat = Spec.Rsa.precomputedWords (arg s 3).toNat
  scratchLength : Spec.Rsa.publicScratchWords (arg s 3).toNat ≤ (arg s 5).toNat

theorem precomputeABI_of {s : State} (h : (Spec.Rsa.publicPrecomputeContract abi 96).pre s) : PrecomputeABI s := by
  sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> with_reducible assumption

end VG.Proof.Bignum.X86

end

end

/-! # Caller resources for the public RSA workspace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem PrecomputeABI.space {s : State} (A : PrecomputeABI s) :
    VG.Impl.Bignum.X86.PublicContext.size (Spec.Rsa.modulusWords (arg s 3).toNat) ≤
      (arg s 5).toNat * 8 := by
  rw [PublicContext.size_contract]
  have := A.scratchLength
  omega_using [this]

theorem PrecomputeABI.used {s : State} (A : PrecomputeABI s) : 384 ≤ (arg s 5).toNat * 8 := by
  have H := A.space
  rw [PublicContext.size_eq] at H
  omega_using [H]

theorem PrecomputeABI.stackArgument {s : State} (A : PrecomputeABI s) {i : Nat} (hi : i < 6) :
    StackArgument s (argumentPointer s 4) ((arg s 5).toNat * 8) i := by
  apply stackArgument_of (count := 6) (by have := A.stackBound; omega_using [this]) hi
  · rw [A.rd, A.wr]; simp
  · exact A.scratchArgs.symm

theorem PrecomputeABI.stack {s : State} (A : PrecomputeABI s) :
    StkOk (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 96) A.stackLow
  · have H := A.scratchBound
    simpa only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 4).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
  · have H : 384 ≤ (arg s 5).toNat * 8 := A.used; omega_using [H]
  · exact A.belowScratch


end VG.Proof.Bignum.X86

end

end

/-! # Install the precomputation workspace from the shared contract -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86

theorem PrecomputeABI.outputBytes {s : State} (A : PrecomputeABI s) :
    (arg s 1).toNat * 8 = 16 * Spec.Rsa.modulusWords (arg s 3).toNat := by
  rw [A.preLength, Spec.Rsa.precomputedWords]
  omega_using []

theorem precomputeInstalled_ok {s : State} (A : PrecomputeABI s) :
    WP isa (.block PrecomputeFn.entry) s fun t =>
      PrecomputeInputs (argumentPointer s 4) ((arg s 5).toNat * 8) (arg s 3).toNat (arg s) t ∧
      Spill.Saved t.mem (off (argumentPointer s 4)) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧
      Outside (argumentPointer s 4) 0 ((arg s 5).toNat * 8) s.mem t.mem := by
  refine WP.mono (precomputeEntry_ok (ptr := arg s 4)
    (A.stackArgument (by decide : 4 < 6)).readSrc rfl A.scratchBound
    (by have := A.used; omega_using [this]) (by rw [A.wr]; simp) A.stack) ?_
  intro t ⟨Sc, Saved, K, O⟩
  refine ⟨?_, Saved, K, O⟩
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have sa : VG.Proof.Dsa.X86.stackAddress t 1 = VG.Proof.Dsa.X86.stackAddress s 1 := by
    simp only [VG.Proof.Dsa.X86.stackAddress, esp]
  have bound := A.stackBound
  have P : VG.Proof.Dsa.X86.stackAddress s 1 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 8 :=
    addr_eq (by omega_using [bound])
  have Z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_using [bound])
  have sub : Region.Sub ⟨VG.Proof.Dsa.X86.stackAddress s 1, 4⟩ ⟨argAddr s 0, 24⟩ := by
    rw [P, Z]; exact Offset.sub _ (by omega_using []) (by omega_using [])
  refine ⟨Sc, A.lengths.1, A.lengths.2, A.space, ?_, ?_, ?_, ?_, A.nBound, ?_, ?_, ?_, A.nScratch,
    ⟨by rw [esp]; exact A.stackLow, by
      rw [esp]; simp only [below]; rw [VG.X86.Taint.sub_setWidth A.stackLow]; exact A.belowScratch⟩,
    by rw [esp]; omega_using [bound],
    by simp only [argumentPointer, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 4).isLt (by decide : 2 ^ 32 < 2 ^ 64))], rfl,
    by rw [sa, K.2.2, A.wr]; exact ⟨⟨argAddr s 0, 24⟩, by simp, by rw [P, Z]; exact Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [])⟩,
    by rw [sa]; exact A.nArgs.sub_right sub,
    by simp only [argAddr, esp]; rw [← A.outputBytes]; exact A.outArgs,
    by rw [esp]; exact VG.X86.Taint.frame_disjoint (n := 24) (by omega_using [bound]) A.retScratch A.scratchArgs.symm,
    by rw [esp, ← A.outputBytes]; exact VG.X86.Taint.frame_disjoint (n := 24) (by omega_using [bound]) A.retOut A.outArgs.symm⟩
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
