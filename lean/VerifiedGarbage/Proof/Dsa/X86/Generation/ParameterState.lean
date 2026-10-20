module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterBody
import VerifiedGarbage.Proof.Dsa.Generation.Chunks

/-! # The outer seed-loop invariant tracks both independent finite tapes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def parameterRemaining (P : SearchContextPlan) (seedUsed witnessUsed : Nat) : Option Spec.Dsa.Params :=
  Spec.Dsa.generateParameters.attempt (8 * P.geometry.pLen)
    ((Spec.Dsa.generationChunks P.geometry.pLen P.hs.bytes).map Spec.Dsa.decodeBE) (8 * P.geometry.qLen)
    (Spec.Dsa.generationChunks P.geometry.qLen (P.seeds.bytes.drop seedUsed)) (P.witnesses.bytes.drop witnessUsed)

def ParameterInvariant (P : SearchContextPlan) (expected : Option Spec.Dsa.Params) (initial : State)
    (seedUsed : Nat) (s : State) : Prop :=
  ∃ W witnessUsed, SearchContext P W s ∧ W 10 = BitVec.ofNat 32 seedUsed ∧
    W 16 = BitVec.ofNat 32 witnessUsed ∧ witnessUsed ≤ P.witnesses.bytes.length ∧ seedUsed ≤ P.seeds.bytes.length ∧
    expected = parameterRemaining P seedUsed witnessUsed ∧ Frame (parameterWrites P.geometry) initial.mem s.mem ∧
    s.rd = initial.rd ∧ s.wr = initial.wr

def ParameterFinished (P : SearchContextPlan) (expected : Option Spec.Dsa.Params) (initial s : State) : Prop :=
  ∃ W, SearchContext P W s ∧
    (((W 19 = 0 ∨ W 19 = 3) ∧ expected = none) ∨ ∃ params, W 19 = 1 ∧ expected = some params ∧
      Spec.Rsa.bytesAt s.mem (off P.geometry.base packed) (2 * P.geometry.pLen + P.geometry.qLen) =
        Spec.Dsa.encodeParams P.geometry.pLen P.geometry.qLen params) ∧
    Frame (parameterWrites P.geometry) initial.mem s.mem ∧ s.rd = initial.rd ∧ s.wr = initial.wr

theorem parameterRemaining_done (P : SearchContextPlan) {seedUsed : Nat} (witnessUsed : Nat)
    (exhausted : P.seeds.bytes.length - seedUsed < P.geometry.qLen) :
    parameterRemaining P seedUsed witnessUsed = none := by
  unfold parameterRemaining
  rw [VG.Proof.Dsa.Generation.generationChunks_done (width := P.geometry.qLen) (bytes := P.seeds.bytes.drop seedUsed) (by simpa only [List.length_drop] using exhausted)]
  rfl

theorem parameterRemaining_step (P : SearchContextPlan) {seedUsed witnessUsed : Nat}
    (available : seedUsed + P.geometry.qLen ≤ P.seeds.bytes.length) :
    parameterRemaining P seedUsed witnessUsed =
      match seedExpected P ((P.seeds.bytes.drop seedUsed).take P.geometry.qLen) witnessUsed with
      | none => none
      | some (none, rest) => Spec.Dsa.generateParameters.attempt (8 * P.geometry.pLen)
          ((Spec.Dsa.generationChunks P.geometry.pLen P.hs.bytes).map Spec.Dsa.decodeBE) (8 * P.geometry.qLen)
          (Spec.Dsa.generationChunks P.geometry.qLen (P.seeds.bytes.drop (seedUsed + P.geometry.qLen))) rest
      | some (some params, _) => some params := by
  have qw := P.geometry.qWidth
  unfold parameterRemaining
  rw [VG.Proof.Dsa.Generation.generationChunks_step (by omega : 0 < P.geometry.qLen)
    (by simp only [List.length_drop]; omega)]
  rw [VG.Proof.Dsa.Generation.parameterAttempt_seedResult _ _ _ _ _ _ (by
    simp only [List.length_take, List.length_drop]; omega)]
  simp only [List.drop_drop]
  rfl
end VG.Proof.Dsa.X86.Generation
