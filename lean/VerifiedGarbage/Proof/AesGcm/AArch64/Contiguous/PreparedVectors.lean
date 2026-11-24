module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.ForwardCall
public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Prepared
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Inline

/-! The forwarded batch borrows the preserved vectors. Compose its save/restore
proof with the syntactic checks for the ordinary AES-GCM caller and leaves. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Prepared
open VG VG.AArch64 VG.Impl.AesGcm.AArch64.Contiguous

private def VectorSafe (before after : Prog isa) : Prop :=
  before.allInstrs keepsV = true → ∀ {s t : State} {tr : List Leak}, Exec isa after s tr t →
    ∀ v ∈ preservedV, (t.v v).extractLsb' 0 64 = (s.v v).extractLsb' 0 64

private theorem same (c : Prog isa) : VectorSafe c c := by
  intro k s t tr e
  exact Exec.preservedV e k

variable {p q u v : Prog isa} {i j : Instr}

private theorem sequential (a : VectorSafe p q) (b : VectorSafe u v) :
    VectorSafe (.seq p u) (.seq q v) := by
  intro k s t tr e r hr
  simp only [Code.allInstrs, Bool.and_eq_true] at k
  obtain ⟨ka,kb⟩ := k
  cases e with | seq first second => exact (b kb second r hr).trans (a ka first r hr)

private theorem branch {c : isa.Cond} (a : VectorSafe p q) (b : VectorSafe u v) :
    VectorSafe (.ite c p u) (.ite c q v) := by
  intro k s t tr e r hr
  simp only [Code.allInstrs, Bool.and_eq_true] at k
  obtain ⟨ka,kb⟩ := k
  cases e with
  | iteT _ ex => exact a ka ex r hr
  | iteF _ ex => exact b kb ex r hr

private theorem framed (body : VectorSafe p q) :
    VectorSafe (.frame i p j) (.frame i q j) := by
  intro k s t tr e r hr
  simp only [Code.allInstrs, Bool.and_eq_true] at k
  have checks := k.1.2
  cases e with | frame hp ex hq => rw [pop_vec hq, ← push_vec hp]; exact body checks ex r hr

private theorem switched (forward : Bool) : VectorSafe (batchCall false) (batchCall forward) := by
  cases forward
  · exact same _
  · intro _ s t tr e r hr
    cases e with | call hc ex ret =>
      rw [ret_eq ret, ← call_vec hc]
      exact Proof.Gcm.AArch64.Stitch.forwardSeal_preserves ex r hr

private theorem batchVectors (forward : Bool) : VectorSafe (batches false) (batches forward) :=
  sequential (same _) (branch (same _) (sequential (same _) (sequential (same _)
    (sequential (switched forward) (same _)))))

theorem preparedVectors (v : Impl.AesGcm.AArch64.Calls) (g : Impl.AesGcm.AArch64.Fn) (f : Bool)
    (check : (Impl.StackScratch.AArch64.withStackArgScratch (v.pwWn+32) 3
      (preparedBody v.callees g f false)).allInstrs keepsV = true)
    {s t : State} {tr : List Leak} (e : Exec isa (preparedFrame v g f) s tr t) :
    ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  apply (framed (sequential (same _) (sequential (same _) (sequential (same _) (sequential ?_ (same _)))))) check e
  cases f
  · exact same _
  · exact batchVectors _

end VG.Proof.AesGcm.AArch64.Contiguous.Prepared
