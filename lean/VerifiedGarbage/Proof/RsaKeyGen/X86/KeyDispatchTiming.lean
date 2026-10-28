module

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySizedTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDispatch

/-! # Public native key width dispatch retains all secret input snapshots -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.Candidate
open VG.Impl.RsaKeyGen.X86.Key

theorem SizedStart.keepFlags {E : Environment} {e p q p' q' : Nat} {s t u v : State}
    (P : SizedStart E e p q p' q' s t) (U : Fupd s u) (V : Fupd t v) : SizedStart E e p q p' q' u v := by
  have left := P.inputs.left.keep (P.inputs.left.ws.rest (U.keeps [])) (U.keeps [])
    (by intro d hd; rw [U.mem])
  have right := P.inputs.right.keep (P.inputs.right.ws.rest (V.keeps [])) (V.keeps [])
    (by intro d hd; rw [V.mem])
  refine ⟨⟨left, right, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [U.gpr, V.gpr]
    exact P.inputs.stack
  · rw [U.mem]
    exact P.leftExponent
  · rw [V.mem]
    exact P.rightExponent
  · rw [U.mem]
    exact P.leftP
  · rw [U.mem]
    exact P.leftQ
  · rw [V.mem]
    exact P.rightP
  · rw [V.mem]
    exact P.rightQ

theorem dispatch_trace (E : Environment) (e p q p' q' w : Nat) (width : E.n = 4 * w) (small : w < 2 ^ 32)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ()))
    (choices : List Nat) (member : w ∈ choices) (bounded : ∀ v ∈ choices, v < 2 ^ 32) :
    RelCT isa (WithValue (SizedStart E e p q p' q') (BitVec.ofNat 32 w)) (dispatch choices) (fun _ _ => True) := by
  induction choices with
  | nil => cases member
  | cons v rest ih =>
    unfold dispatch
    have compare := compare_value_trace (P := SizedStart E e p q p' q') (BitVec.ofNat 32 w) (BitVec.ofNat 32 v)
      (fun _ _ _ _ P U V => P.keepFlags U V)
    rw [width_comparison small (bounded v List.mem_cons_self)] at compare
    by_cases same : w = v
    · rw [decide_eq_true same] at compare
      refine RelCT.seq compare (branch_true ?_)
      rw [← same, ← width]
      exact (sized_trace E e p q p' q' release).mono (fun _ _ P => P.1) (fun _ _ _ => trivial)
    · rw [decide_eq_false same] at compare
      exact RelCT.seq compare (branch_false (ih (List.mem_cons.mp member |>.resolve_left same)
        (fun j hj => bounded j (List.mem_cons_of_mem _ hj))))

end VG.Proof.RsaKeyGen.X86.Key
