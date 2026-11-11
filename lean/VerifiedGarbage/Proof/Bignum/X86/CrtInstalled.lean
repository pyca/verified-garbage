module
public import VerifiedGarbage.Proof.Bignum.X86.CrtABI
public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Impl.Bignum.X86.CrtFn
public import VerifiedGarbage.Proof.Framework.X86.Spill

import VerifiedGarbage.Proof.Bignum.X86.CrtResources
import VerifiedGarbage.Proof.Bignum.X86.CrtEntry
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps

/-! # Install all caller resources for the private CRT operation -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Impl.Bignum.X86

/-- What installing the working space needs of the caller's resources: `CrtABI`'s, or those
of a contract with more arguments. -/
structure CrtRes (s : State) : Prop where
  args : ∀ i, i < 18 → StackArgument s (argumentPointer s 16) ((arg s 17).toNat * 8) i
  scratchBound : (arg s 16).toNat + (arg s 17).toNat * 8 ≤ 2 ^ 32
  used : 224 ≤ (arg s 17).toNat * 8
  scratchW : (⟨argumentPointer s 16, (arg s 17).toNat * 8⟩ : Region) ∈ s.wr
  stack : StkOk (s.gpr .esp) (argumentPointer s 16) ((arg s 17).toNat * 8)
  lengths : Spec.Rsa.lenValid (arg s 3).toNat
  space : VG.Impl.Bignum.X86.Crt.size (Spec.Rsa.modulusWords (arg s 3).toNat) ≤ (arg s 17).toNat * 8
  pLength : (arg s 7).toNat < (arg s 3).toNat
  qLength : (arg s 9).toNat < (arg s 3).toNat
  room : CallRoom (s.gpr .esp) (argumentPointer s 16) ((arg s 17).toNat * 8)
  stackBound : (s.gpr .esp).toNat + 76 ≤ 2 ^ 32
  outLength : (arg s 1).toNat = (arg s 3).toNat
  inLength : (arg s 5).toNat = (arg s 3).toNat
  pPositive : 1 ≤ (arg s 7).toNat
  qPositive : 1 ≤ (arg s 9).toNat
  dpLength : (arg s 11).toNat = (arg s 7).toNat
  qiLength : (arg s 15).toNat = (arg s 7).toNat
  dqLength : (arg s 13).toNat = (arg s 9).toNat
  outBound : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  outW : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region) ∈ s.wr
  outScratch : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  compR : ∀ i ∈ componentArguments, (⟨argumentPointer s i, (arg s (i + 1)).toNat⟩ : Region) ∈ s.rd ++ s.wr
  nBound : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  inBound : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  pBound : (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32
  qBound : (arg s 8).toNat + (arg s 9).toNat ≤ 2 ^ 32
  dpBound : (arg s 10).toNat + (arg s 11).toNat ≤ 2 ^ 32
  dqBound : (arg s 12).toNat + (arg s 13).toNat ≤ 2 ^ 32
  qiBound : (arg s 14).toNat + (arg s 15).toNat ≤ 2 ^ 32
  nScratch : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  inScratch : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  pScratch : (⟨argumentPointer s 6, (arg s 7).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qScratch : (⟨argumentPointer s 8, (arg s 9).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dpScratch : (⟨argumentPointer s 10, (arg s 11).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  dqScratch : (⟨argumentPointer s 12, (arg s 13).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩
  qiScratch : (⟨argumentPointer s 14, (arg s 15).toNat⟩ : Region).Disjoint ⟨argumentPointer s 16, (arg s 17).toNat * 8⟩

theorem _root_.VG.Proof.Bignum.X86.CrtABI.res {s : State} (A : CrtABI s) : CrtRes s where
  args _ hi := A.stackArgument hi
  scratchBound := A.scratchBound
  used := A.used
  scratchW := by rw [A.wr]; simp
  stack := A.stack
  lengths := A.lengths
  space := A.space
  pLength := A.pLength
  qLength := A.qLength
  room := A.room
  stackBound := A.stackBound
  outLength := A.outLength
  inLength := A.inLength
  pPositive := A.pPositive
  qPositive := A.qPositive
  dpLength := A.dpLength
  qiLength := A.qiLength
  dqLength := A.dqLength
  outBound := A.outBound
  outW := by rw [A.wr]; simp
  outScratch := A.outScratch
  compR i hi := by
    rw [A.rd, A.wr]
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  nBound := A.nBound
  inBound := A.inBound
  pBound := A.pBound
  qBound := A.qBound
  dpBound := A.dpBound
  dqBound := A.dqBound
  qiBound := A.qiBound
  nScratch := A.nScratch
  inScratch := A.inScratch
  pScratch := A.pScratch
  qScratch := A.qScratch
  dpScratch := A.dpScratch
  dqScratch := A.dqScratch
  qiScratch := A.qiScratch

theorem installedG_ok {s : State} (A : CrtRes s) :
    WP isa (.block Crt.entry) s fun t =>
      Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) t ∧
      Spill.Saved t.mem (off (argumentPointer s 16)) s.gpr Crt.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧
      Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) s.mem t.mem := by
  refine WP.mono (entry_ok (ptr := arg s 16)
    (A.args 16 (by decide)).readSrc rfl A.scratchBound
    (by have := A.used; omega) A.scratchW A.stack) ?_
  intro t ⟨Sc, Saved, K, O⟩
  refine ⟨?_, Saved, K, O⟩
  refine ⟨Sc, A.lengths.1, A.lengths.2, A.space, ?_, ?_, ?_, ?_, A.pLength, A.qLength,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [K.1 _ (by decide)]; exact A.room, by rw [K.1 _ (by decide)]; exact A.stackBound⟩
  · intro i hi
    exact (CallArgument.mk (A.args i hi) rfl).keep K (by decide) O
  · simp only [← A.outLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [← A.inLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact BitVec.eq_of_toNat_eq A.dpLength
  · exact BitVec.eq_of_toNat_eq A.dqLength
  · exact BitVec.eq_of_toNat_eq A.qiLength
  · rw [← A.outLength]; exact A.outBound
  · rw [K.2.2]
    exact ⟨_, A.outW, by rw [← A.outLength]; exact Region.contains_self _ _⟩
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
    rw [K.2.1, K.2.2]
    exact ⟨_, A.compR i hi, Region.contains_self _ _⟩
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


theorem installed_ok {s : State} (A : CrtABI s) :
    WP isa (.block Crt.entry) s fun t =>
      Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) t ∧
      Spill.Saved t.mem (off (argumentPointer s 16)) s.gpr Crt.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧
      Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) s.mem t.mem :=
  installedG_ok A.res

theorem _root_.VG.Proof.Bignum.X86.CrtABIP.res {s : State} (A : CrtABIP s) : CrtRes s := by
  have space : VG.Impl.Bignum.X86.Crt.size (Spec.Rsa.modulusWords (arg s 3).toNat) ≤ (arg s 17).toNat * 8 := by
    have H := Crt.shared_scratch A.lengths.1
    have := A.scratchLength
    omega
  have used : 224 ≤ (arg s 17).toNat * 8 := by
    have H := space
    rw [Crt.size_eq] at H
    omega
  exact {
  args := fun i hi => stackArgument_of (count := 20) (by have := A.stackBound; omega) (by omega)
    (by rw [A.rd, A.wr]; simp) A.scratchArgs.symm
  scratchBound := A.scratchBound
  used := used
  scratchW := by rw [A.wr]; simp
  stack := by
    apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 96) A.stackLow
    · have H := A.scratchBound
      simpa only [argumentPointer, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (Nat.lt_trans (arg s 16).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using H
    · omega
    · exact A.belowScratch
  lengths := A.lengths
  space := space
  pLength := A.pLength
  qLength := A.qLength
  room := by
    refine ⟨A.stackLow, ?_⟩
    simp only [below]
    rw [VG.X86.Taint.sub_setWidth A.stackLow]
    exact A.belowScratch
  stackBound := by have := A.stackBound; omega
  outLength := A.outLength
  inLength := A.inLength
  pPositive := A.pPositive
  qPositive := A.qPositive
  dpLength := A.dpLength
  qiLength := A.qiLength
  dqLength := A.dqLength
  outBound := A.outBound
  outW := by rw [A.wr]; simp
  outScratch := A.outScratch
  compR := fun i hi => by
    rw [A.rd, A.wr]
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  nBound := A.nBound
  inBound := A.inBound
  pBound := A.pBound
  qBound := A.qBound
  dpBound := A.dpBound
  dqBound := A.dqBound
  qiBound := A.qiBound
  nScratch := A.nScratch
  inScratch := A.inScratch
  pScratch := A.pScratch
  qScratch := A.qScratch
  dpScratch := A.dpScratch
  dqScratch := A.dqScratch
  qiScratch := A.qiScratch }

end VG.Proof.Bignum.X86.Crt
