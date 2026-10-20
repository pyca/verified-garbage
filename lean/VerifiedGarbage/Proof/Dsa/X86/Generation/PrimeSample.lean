module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeReady
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleLayout
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeEffects
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleWitness

/-! # Sampling preserves draw consumption and the running uniform count -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

theorem sampleFrame_control {G : PrimeConfig} {s t : Mem} {d : Nat}
    (O : Frame (sampleWrites G.base G.n (G.witness.setWidth 64) G.len) s t)
    (hd : d = primeUsed ∨ d = primeUniform) : t.readW (off G.base d) 32 = s.readW (off G.base d) 32 := by
  have width := G.width
  have bound : d + 4 ≤ G.size := by have := G.room; rcases hd with rfl | rfl <;> simp only [primeUsed, primeUniform, primeExponent] at * <;> omega
  apply O.readW (Region.contains_self _ 4) ?_ (by decide)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
    have itemFit : item.1 + item.2 ≤ 2 ^ 64 := by
      simp only [sampleArithmeticWrites, sampleTestWrites, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> simp only [slot, stride, primeIsUniform] <;> omega
    apply Offset.disjoint G.base ?_ (by rcases hd with rfl | rfl <;> decide) itemFit
    simp only [sampleArithmeticWrites, sampleTestWrites, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl <;>
      simp only [slot, stride, primeIsUniform, primeUsed, primeUniform] <;> omega
  · obtain rfl := List.mem_singleton.mp hr
    exact G.witnessScratch.symm.sub_left (Offset.sub_base _ bound)

theorem primeSample_ok {G : PrimeConfig} {s : State} (R : PrimeReady G s) (pointer : s.gpr .esi = G.witness) :
    WP isa (sampleWitness G.len) s fun t =>
      let witness := Spec.RsaKeyGen.witness (G.modulus - 1)
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (G.witness.setWidth 64) G.len))
      PrimeReady G t ∧ wordsVal t.mem G.base (slot G.n 5) G.n = witness.1 ∧
      t.mem.readW (off G.base primeIsUniform) 32 = mask32 (witness.2 = true) ∧
      t.mem.readW (off G.base primeUsed) 32 = s.mem.readW (off G.base primeUsed) 32 ∧
      t.mem.readW (off G.base primeUniform) 32 = s.mem.readW (off G.base primeUniform) 32 ∧
      PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  refine WP.mono (sampleWitness_ok R.context G.width G.flagRoom R.one rfl G.lenMin G.lenWords pointer G.witnessFit
    G.predecessorBits R.witnessRead R.witnessReadByte R.witnessWrite G.witnessScratch)
    fun t ⟨_, value, flag, O, K⟩ => ?_
  have F := primeFrame_sample O
  exact ⟨R.keep F K (by decide) (by decide), value, flag,
    sampleFrame_control O (.inl rfl), sampleFrame_control O (.inr rfl), F, K⟩
end VG.Proof.Dsa.X86.Generation
