module

public import VerifiedGarbage.Impl.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Call

/-! # Native candidate word initialization never assigns ESP -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateNoSp
open VG VG.X86 VG.Impl.Mont.X86.Dynamic

theorem sequence {a b : Prog isa} (A : NoSp a) (B : NoSp b) : NoSp (.seq a b) := by
  intro i mem
  rcases List.mem_append.mp mem with mem | mem
  · exact A i mem
  · exact B i mem

theorem zeros (out n : Nat) : NoSp (zerosW out n) := NoSp.of_all (by rfl)

theorem constant (n out value : Nat) : NoSp (setConstW n out value) := by
  unfold setConstW
  apply sequence (zeros out n)
  intro i mem
  obtain ⟨j, _, mem⟩ := List.mem_flatMap.mp mem
  split at mem
  · simp only [List.not_mem_nil] at mem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl <;> rfl

end VG.Proof.RsaKeyGen.X86.CandidateNoSp
