module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIValid
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEntry
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABI
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIRegions

/-! # The outer register push preserves all eleven cdecl arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem call_argument (s : State) (i : Nat) (index : i < 11) : (callEnvironment s).argument i = arg s i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Environment.argument, callEnvironment, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem CallLayout.argumentOffset {s : State} (A : CallLayout s) {i : Nat} (index : i < 11) :
    argAddr s i = off (argAddr s 0) (4 * i) := by
  have fit := A.argsFit
  change addr (s.gpr .esp) (4 + 4 * i) = off (addr (s.gpr .esp) 4) (4 * i)
  rw [addr_eq (by omega), addr_eq (by omega)]
  exact (Offset.add_add _ _ _).symm

theorem CallLayout.pushedArgument {s : State} (A : CallLayout s) {i : Nat} (index : i < 11) :
    readSrc (Compact.entered s) (.mem (VG.Impl.RsaKeyGen.X86.CandidateArgs.arg i)) = some (arg s i) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  have separate : (⟨argAddr s 0, 44⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    change (⟨addr (s.gpr .esp) 4, 44⟩ : Region).Disjoint (below (s.gpr .esp) 16)
    rw [addr_eq (by have := A.argsFit; omega)]
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.disjoint_below _ (by decide)
  have contains : (⟨argAddr s 0, 44⟩ : Region).Contains (argAddr s i) 4 := by
    rw [A.argumentOffset index]
    exact Offset.contains_base _ (by omega) (by omega)
  have word := F.readW (w := 32) contains (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact separate) (by decide)
  change (Compact.entered s).load32 ((Compact.entered s).ea (VG.Impl.Mont.X86.Compact.arg i)) = _
  rw [Compact.argument_address]
  have access : InRegions ((Compact.entered s).rd ++ (Compact.entered s).wr) (argAddr s i) 4 := by
    change InRegions (s.rd ++ (below (s.gpr .esp) 16 :: s.wr)) (argAddr s i) 4
    refine ⟨⟨argAddr s 0, 44⟩, List.mem_append_right _ (List.mem_cons_of_mem _ ?_), contains⟩
    rw [A.wr]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [State.load32, ite_eq_left access]
  exact congrArg some word

theorem entry_arguments {s : State} (h : contract.pre s) :
    CandidateArgs.Entry (callEnvironment s).base (callEnvironment s).size (callEnvironment s).p
      (callEnvironment s).argument (Compact.entered s) := by
  have A := call_layout h
  have v := call_valid h
  have space : 256 ≤ (callEnvironment s).size := v.geometry.headerFit
  refine ⟨⟨?_, ?_⟩, by omega, rfl, ?_, ?_, v.argsFit, v.argsFar, ?_⟩
  · change (callEnvironment s).workspaceRegion ∈ below (s.gpr .esp) 16 :: s.wr
    exact List.mem_cons_of_mem _ (A.writeMember (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · change ((arg s 9).setWidth 64).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (arg s 9).isLt (by decide))]
    exact A.workspaceFit
  · refine ⟨by have := v.low; omega, ?_⟩
    rcases v.workspaceStack with left | right
    · exact Or.inl left
    · exact Or.inr (by omega)
  · rw [Compact.entered, pushed_esp]
    rfl
  · intro i index
    rw [call_argument s i index]
    exact A.pushedArgument index

end VG.Proof.RsaKeyGen.X86.Candidate
