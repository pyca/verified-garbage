module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialContext
public import VerifiedGarbage.Spec.Dsa

/-! # The outer loop's checked prefix and terminal status -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.RsaKeyGen

def trialValue (s : State) (input : BitVec 32) (len : Nat) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (input.setWidth 64) len)

def trialStatus (entries value : Nat) : BitVec 32 :=
  if (List.range entries).any (fun i => value % tabEntry i == 0) then 0 else 1

theorem trialStatus_fail {entries value i : Nat} (hi : i < entries) (hz : value % tabEntry i = 0) :
    trialStatus entries value = 0 := by
  have yes : (List.range entries).any (fun i => value % tabEntry i == 0) = true :=
    List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, by rw [hz]; rfl⟩
  simp only [trialStatus, yes, ite_true]

theorem trialStatus_pass {entries value : Nat} (hn : ∀ i < entries, value % tabEntry i ≠ 0) :
    trialStatus entries value = 1 := by
  have no : (List.range entries).any (fun i => value % tabEntry i == 0) = false := by
    apply List.any_eq_false.mpr
    intro i hi
    simpa only [beq_iff_eq] using hn i (List.mem_range.mp hi)
  simp only [trialStatus, no, Bool.false_eq_true, ite_false]

structure TrialLoopInv (s : State) (base : Addr) (input table : BitVec 32) (len i : Nat) (t : State) : Prop where
  context : TrialContext s base t
  source : trialSlot t.mem base 0 = input
  table : trialSlot t.mem base 4 = table
  index : trialSlot t.mem base 8 = BitVec.ofNat 32 i
  status : trialSlot t.mem base 12 = 1
  clear : ∀ j < i, trialValue s input len % tabEntry j ≠ 0

def TrialDone (s : State) (base : Addr) (input : BitVec 32) (len entries : Nat) (t : State) : Prop :=
  TrialContext s base t ∧ trialSlot t.mem base 12 = trialStatus entries (trialValue s input len)
end VG.Proof.Dsa.X86.Generation
