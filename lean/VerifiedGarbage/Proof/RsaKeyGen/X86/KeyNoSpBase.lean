module

import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace

/-! # Native key word loops and inverse steps preserve ESP -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyNoSp
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.RsaKeyGen.X86.Key
open VG.Impl.Mont.X86.Dynamic

theorem checked {c : Prog isa} (H : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  rw [H i hi]
  rfl

theorem sequence {a b : Prog isa} (A : NoSp a) (B : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact A i hi
  · exact B i hi

theorem constant (n out value : Nat) : NoSp (setConstW n out value) := by
  unfold setConstW
  apply sequence (NoSp.of_all (by rfl))
  intro i hi
  obtain ⟨j, _, hi⟩ := List.mem_flatMap.mp hi
  split at hi
  · simp only [List.not_mem_nil] at hi
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> rfl

end VG.Proof.RsaKeyGen.X86.KeyNoSp
