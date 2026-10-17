module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchContract
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
import VerifiedGarbage.Proof.Framework.Omega

/-! # A private outgoing-argument frame for the native candidate operation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum

def outgoingSP (s : State) : Addr := s.gpr .rsp - 32

def referenceValues (s : State) : List (Nat × BitVec 64) :=
  [(1, stackArg s 0), (2, stackArg s 1), (3, stackArg s 2)]

def candidateReference (s : State) : State :=
  { s with
    gpr := fun r => if r = .rsp then outgoingSP s else s.gpr r
    mem := writeController s.mem (outgoingSP s) (referenceValues s)
    rd := [inputRand s, ⟨outgoingSP s + 8, 24⟩]
    wr := inputBuffers s }

theorem reference_rsp (s : State) : (candidateReference s).gpr .rsp = outgoingSP s := rfl

theorem reference_reg (s : State) (r : Reg) (h : r ≠ .rsp) :
    (candidateReference s).gpr r = s.gpr r := ite_eq_right h

theorem reference_arg (s : State) (j : Nat) (hj : j < 3) :
    stackArg (candidateReference s) j = stackArg s j := by
  change word (writeController s.mem (outgoingSP s) (referenceValues s)) (outgoingSP s) (8 * (j + 1)) = _
  have hv : ∀ e ∈ referenceValues s, e.1 < 16 := by
    simp only [referenceValues, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> dsimp only <;> decide
  rw [writeController_word _ _ _ hv _ (by omega_using [hj])]
  have he : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  rcases he with rfl | rfl | rfl <;>
    simp only [controllerValue, referenceValues, List.foldl_cons, List.foldl_nil,
      Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false]

theorem outgoing_nat {s : State} (h : 32 ≤ (s.gpr .rsp).toNat) :
    (outgoingSP s).toNat = (s.gpr .rsp).toNat - 32 := by
  have he : (32 : BitVec 64) ≤ s.gpr .rsp := by
    change (32 : BitVec 64).toNat ≤ (s.gpr .rsp).toNat
    exact h
  rw [outgoingSP, BitVec.toNat_sub_of_le he]
  rfl

end VG.Proof.Ffdh.X86_64.Generation
