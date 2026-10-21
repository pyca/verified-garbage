module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInputPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWidthTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # One public-width dispatch theorem serves input and output adapters -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.Candidate (WithValue compare_value_trace width_comparison branch_true branch_false)
open VG.Proof.RsaKeyGen.X86.Key (Environment InputPair widthArgs_ok)
open VG.Impl.RsaKeyGen.X86.Key (widths)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

def KeepIO (P : State → State → Prop) : Prop := ∀ s t u v, P s t →
  Keeps [.eax] s u → u.mem = s.mem → Keeps [.eax] t v → v.mem = t.mem → P u v

theorem dispatchIO_trace {P Q : State → State → Prop} {part : Nat → Prog isa} {w : Nat}
    (small : w < 2 ^ 32) (choices : List Nat) (member : w ∈ choices)
    (bounded : ∀ v ∈ choices, v < 2 ^ 32) (keep : KeepIO P)
    (correct : RelCT isa P (part (4 * w)) Q) :
    RelCT isa (WithValue P (BitVec.ofNat 32 w)) (dispatchIO part choices) Q := by
  induction choices with
  | nil => cases member
  | cons v rest ih =>
    unfold dispatchIO
    have compare := compare_value_trace (P := P) (BitVec.ofNat 32 w) (BitVec.ofNat 32 v)
      (fun s t u z H U V => keep s t u z H ((U.keeps []).mono (by decide)) U.mem
        ((V.keeps []).mono (by decide)) V.mem)
    rw [width_comparison small (bounded v List.mem_cons_self)] at compare
    by_cases same : w = v
    · rw [decide_eq_true same] at compare
      refine RelCT.seq compare (branch_true ?_)
      rw [← same]
      exact correct.mono (fun _ _ P => P.1) (fun _ _ P => P)
    · rw [decide_eq_false same] at compare
      exact RelCT.seq compare (branch_false (ih (List.mem_cons.mp member |>.resolve_left same)
        (fun j hj => bounded j (List.mem_cons_of_mem _ hj))))

theorem selectIO_trace {E : Environment} {P Q : State → State → Prop} {part : Nat → Prog isa}
    (valid : E.Valid) (input : ∀ s t, P s t → InputPair E s t) (keep : KeepIO P)
    (correct : RelCT isa P (part E.n) Q) : RelCT isa P (selectIO part) Q := by
  have lengths := valid.length
  have width : E.n = 4 * (E.primeLength / 8) := by
    unfold VG.Proof.RsaKeyGen.X86.Key.Environment.n
    obtain ⟨_, _, _⟩ := lengths
    omega
  have bounds : 4 ≤ E.primeLength / 8 ∧ E.primeLength / 8 ≤ 64 := by
    obtain ⟨_, _, _⟩ := lengths
    omega
  have first : RelCT isa P (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc 4)), .shift .shr .eax 4])
      (WithValue P (BitVec.ofNat 32 (E.primeLength / 8))) := by
    intro s t tr ur u v H A C
    have inputs := input s t H
    have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
        (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc 4)), .shift .shr .eax 4])
        (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
    obtain ⟨_, leftMem, leftValue, leftKeeps⟩ := wp_result (widthArgs_ok inputs.left) A
    obtain ⟨_, rightMem, rightValue, rightKeeps⟩ := wp_result (widthArgs_ok inputs.right) C
    exact ⟨(raw _ _ _ _ _ _ inputs.agree A C).1,
      keep s t u v H leftKeeps leftMem rightKeeps rightMem, leftValue, rightValue⟩
  unfold selectIO
  apply RelCT.seq first
  apply dispatchIO_trace (by omega) widths ?_ ?_ keep
    (by rw [← width]; exact correct)
  · exact List.mem_map.mpr ⟨E.primeLength / 8 - 4, List.mem_range.mpr (by omega), by omega⟩
  · intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := List.mem_range.mp hi
    omega

end VG.Proof.RsaKeyGen.X86.KeyRuntime
