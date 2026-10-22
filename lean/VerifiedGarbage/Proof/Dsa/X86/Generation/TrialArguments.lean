module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.TrialFilter
public import VerifiedGarbage.Proof.MillerRabin.X86.ArgumentState
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Reuse the existing argument-frame invariant for the four public trial parameters. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.MillerRabin.X86 VG.Proof.Mont.X86

def trialArgument (edi : BitVec 32) (n : Nat) : Nat → BitVec 32
  | 0 => edi + BitVec.ofNat 32 (VG.Impl.Mont.X86.Dynamic.slot n 0)
  | 1 => edi + BitVec.ofNat 32 (VG.Impl.Mont.X86.Dynamic.slot n 0 + 8 * n)
  | 2 => edi + BitVec.ofNat 32 trialTableOffset
  | _ => BitVec.ofNat 32 (trialWordCount n)

theorem trial_pointer_argument {f s : State} {values : Nat → BitVec 32} {index offset : Nat}
    (H : ArgumentState f values index s) (bound : index < 9)
    (fit : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32) (frame : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr)
    (value : values index = f.gpr .edi + BitVec.ofNat 32 offset) :
    WP isa (.block (trialArgPointer offset index)) s (ArgumentState f values (index + 1)) := by
  unfold trialArgPointer
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  have Hb := (H.of_keeps (A.keeps.mono (by decide)) A.mem).of_keeps (B.keeps.mono (by decide)) B.mem
  refine Hb.store bound fit frame (by rw [B.gpr, A.gpr, H.keeps.1 .edi (by decide), value])
    fun _ next => WP.block_nil next

theorem trial_arguments {f : State} {n : Nat}
    (fit : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32) (frame : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (trialArguments n)) f (ArgumentState f (trialArgument (f.gpr .edi) n) 4) := by
  unfold trialArguments
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (trial_pointer_argument (ArgumentState.initial f (trialArgument (f.gpr .edi) n)) (by decide)
    fit frame (offset := VG.Impl.Mont.X86.Dynamic.slot n 0) rfl) fun a A => ?_)
  refine WP.block_append (WP.mono (trial_pointer_argument A (by decide) fit frame
    (offset := VG.Impl.Mont.X86.Dynamic.slot n 0 + 8 * n) rfl) fun b B => ?_)
  refine WP.block_append (WP.mono (trial_pointer_argument B (by decide) fit frame
    (offset := trialTableOffset) rfl) fun c C => ?_)
  refine wp_movS rfl fun d D _ => ?_
  have Hd := C.of_keeps (D.keeps.mono (by decide)) D.mem
  exact Hd.store (by decide) fit frame D.gpr fun _ next => WP.block_nil next

end VG.Proof.Dsa.X86.Generation
