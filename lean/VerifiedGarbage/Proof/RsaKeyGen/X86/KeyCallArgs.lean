module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBody
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallGeometry
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCallValid
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
import VerifiedGarbage.Proof.Framework.Offset

/-! # The native register push retains all eighteen cdecl key arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem CallLayout.workspaceMember {s : State} (A : CallLayout s) : callWorkspace s ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_right _ List.mem_cons_self

theorem CallLayout.argumentMember {s : State} (A : CallLayout s) : callArguments s ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem CallLayout.outputMember {s : State} (A : CallLayout s) {i : Nat} (hi : i < 7) : callOutput s i ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem CallLayout.argumentOffset {s : State} (A : CallLayout s) {i : Nat} (hi : i < 18) :
    argAddr s i = off (argAddr s 0) (4 * i) := by
  have fit := A.argsFit
  change addr (s.gpr .esp) (4 + 4 * i) = off (addr (s.gpr .esp) 4) (4 * i)
  rw [addr_eq (by omega), addr_eq (by omega)]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]

theorem CallLayout.pushedArgument {s : State} (A : CallLayout s) {i : Nat} (hi : i < 18) :
    readSrc (Compact.entered s) (.mem (VG.Impl.RsaKeyGen.X86.CandidateArgs.arg i)) = some (arg s i) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  have separate : (callArguments s).Disjoint (below (s.gpr .esp) 16) := by
    change (⟨addr (s.gpr .esp) 4, 72⟩ : Region).Disjoint (below (s.gpr .esp) 16)
    rw [addr_eq (by have := A.argsFit; omega)]
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.disjoint_below _ (by decide)
  have contains : (callArguments s).Contains (argAddr s i) 4 := by
    rw [A.argumentOffset hi]
    exact Offset.contains_base _ (by omega) (by omega)
  have word := F.readW contains (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide : 32 / 8 < 2 ^ 64)
  change (Compact.entered s).load32 ((Compact.entered s).ea (VG.Impl.Mont.X86.Compact.arg i)) = _
  rw [Compact.argument_address]
  have access : InRegions ((Compact.entered s).rd ++ (Compact.entered s).wr) (argAddr s i) 4 := by
    refine ⟨callArguments s, List.mem_append_right _ (List.mem_cons_of_mem _ A.argumentMember), contains⟩
  rw [State.load32, ite_eq_left access]
  exact congrArg some word

theorem call_args_region (s : State) : KeyArgs.argsRegion (callSp s) = callArguments s := by
  unfold KeyArgs.argsRegion callArguments
  congr 1
  change ((s.gpr .esp - 16#32 + 20#32).setWidth 64) = ((s.gpr .esp + 4#32).setWidth 64)
  congr 1
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem entry_arguments {s : State} (h : contract.pre s) :
    KeyArgs.Entry (callEnvironment s).base (callEnvironment s).size (callSp s)
      (callEnvironment s).argument (Compact.entered s) := by
  have A := call_layout h
  have D := call_separation h
  have Z := call_sizes h
  have v := call_valid h
  have bank := v.bankFit
  have head : 72 ≤ (callEnvironment s).size := by
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Impl.Rsa.X86.Keys.hdr at bank
    omega
  refine ⟨⟨?_, ?_⟩, head, rfl, workspace_stack h, ?_, ?_, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ A.workspaceMember
  · change ((arg s 16).setWidth 64).toNat + 8 * (arg s 17).toNat ≤ 2 ^ 32
    rw [VG.BitVec.toNat_setWidth_32_64]
    exact A.workspaceFit
  · rw [Compact.entered, pushed_esp]
    rfl
  · rw [A.privateNat]
    have := A.low
    have := A.argsFit
    omega
  · rw [call_args_region]
    exact D.argsWorkspace
  · intro i hi
    rw [Z.argument hi]
    exact A.pushedArgument hi

theorem entry_input {s : State} (h : contract.pre s) :
    EntryInput (callEnvironment s) (callSp s) (Compact.entered s) := by
  have A := call_layout h
  have Z := call_sizes h
  refine ⟨entry_arguments h, ?_, ?_, ?_⟩
  · intro i hi
    rw [Z.outputRegion hi]
    exact ⟨callOutput s i, List.mem_cons_of_mem _ (A.outputMember hi), Region.contains_self _ _⟩
  · refine ⟨callExponent s, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    change callExponent s ∈ s.rd
    rw [A.rd]
    exact List.mem_singleton_self _
  · intro i hi
    rw [call_args_region, Z.outputRegion hi]
    exact (call_separation h).argsOutput i hi

end VG.Proof.RsaKeyGen.X86.Key
