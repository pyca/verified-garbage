module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Round
public import VerifiedGarbage.Impl.Dsa.X86.Generation.TestWitness
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundMinus
import VerifiedGarbage.Proof.Dsa.X86.Generation.TestWitness

/-! # Classify the loaded draw against the original candidate minus one -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

def sampleTestWrites (n : Nat) : List (Nat × Nat) :=
  [(slot n 8, 8 * n), (slot n 7, 8 * n), (primeIsUniform, 4)]

theorem sampleTest_ok {s : State} {base : Addr} {size n m : Nat}
    (C : Context n m base size s) (width : n ≤ 48) (room : primeIsUniform + 4 ≤ size)
    (one : wordsVal s.mem base (slot n 3) n = 1) :
    WP isa (.seq (roundMinusOne n) (testWitness n)) s fun t =>
      let good := 2 ≤ wordsVal s.mem base (slot n 5) n ∧ wordsVal s.mem base (slot n 5) n < m - 1
      Context n m base size t ∧ t.mem.readW (off base primeIsUniform) 32 = mask32 good ∧
      t.zf = some (decide (¬good)) ∧ wordsVal t.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n ∧
      Outs base (sampleTestWrites n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.seq (WP.mono (roundMinusOne_ok C one) fun a ⟨Ca, minus, Oa, Ka⟩ => ?_)
  have inputa : wordsVal a.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n :=
    Oa.wordsVal (by simp only [slot, stride]; omega) (by simp only [slot, stride]; omega)
  refine WP.mono (testWitness_ok Ca.scr Ca.modulus.n0 width room) fun t ⟨flag, zf, Ot, Kt⟩ => ?_
  rw [inputa, minus] at flag zf
  have wide : Outside base (slot n 7) (primeIsUniform + 4 - slot n 7) a.mem t.mem := by
    intro x hx
    apply Ot x
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rcases hx with hx | hx <;>
      simp only [slot, stride, primeIsUniform] at * <;> omega
  have Ct := Ca.outside_keep Kt (by decide) (by decide) wide
    (by simp only [slot, stride]; omega) (by simp only [slot]; omega)
  refine ⟨Ct, flag, zf, ?_, ?_, (Ka.mono (by decide)).trans Kt⟩
  · rw [wide.wordsVal (by simp only [slot, stride]; omega) (by simp only [slot, stride]; omega), inputa]
  · exact (Outs.of_outside Oa (by simp [sampleTestWrites])).trans (Ot.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [sampleTestWrites]))
end VG.Proof.Dsa.X86.Generation
