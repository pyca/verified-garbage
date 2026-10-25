module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEntry
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Argument entry leaks only the public cdecl arguments and workspace address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateArgs

def EntryPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Entry base size p inputs s ∧ Entry base size p inputs t

theorem pointer_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (S : Entry base size p inputs s) :
    WP isa (.block [.mov .edi (.mem (arg 9))]) s fun t => t.gpr .edi = inputs 9 ∧ Keeps [.edi] s t := by
  refine wp_movS (S.read 9 (by decide)) fun t T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem pointer_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) (.block [.mov .edi (.mem (arg 9))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (arg 9))])
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  have A : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.sp.trans T.sp.symm)
  obtain ⟨ptrU, Ku⟩ := wp_result (pointer_ok S) E
  obtain ⟨ptrZ, Kz⟩ := wp_result (pointer_ok T) G
  refine ⟨(raw _ _ _ _ _ _ A E G).1, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · rw [Ku.1 .esp (by decide), Kz.1 .esp (by decide)]; exact S.sp.trans T.sp.symm
  · exact ptrU.trans ptrZ.symm

def InitializedPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Context base size p inputs s ∧ Context base size p inputs t ∧
    (∀ i < 11, s.mem.readW (off base (4 * i)) 32 = inputs i ∧ t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
    s.mem.readW (off base 44) 32 = inputs 2 ∧ t.mem.readW (off base 44) 32 = inputs 2

theorem enter_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) enter (InitializedPair base size p inputs) := by
  have copied : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) code (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ H => H)
      (hc := VG.Taint.hintOf taint (τr [.esp, .edi]) code)
    kernel_rfl
  have raw : RelCT isa (EntryPair base size p inputs) enter (fun _ _ => True) := RelCT.seq pointer_trace copied
  intro s t tr ur u z ⟨S, T⟩ E G
  obtain ⟨Cu, valuesU, usedU, _, _⟩ := wp_result (enter_ok S) E
  obtain ⟨Cz, valuesZ, usedZ, _, _⟩ := wp_result (enter_ok T) G
  exact ⟨(raw _ _ _ _ _ _ ⟨S, T⟩ E G).1, Cu, Cz, fun i index => ⟨valuesU i index, valuesZ i index⟩, usedU, usedZ⟩

end VG.Proof.RsaKeyGen.X86.CandidateArgs
