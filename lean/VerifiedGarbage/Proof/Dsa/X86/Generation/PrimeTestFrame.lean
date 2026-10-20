module
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInputs
public import VerifiedGarbage.Spec.Rsa.Contract
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleMemory

/-! # The complete test writes only arithmetic scratch and the witness buffer -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation

def PrimeTestFrame (G : PrimeConfig) (s t : Mem) : Prop :=
  Frame [⟨G.base, G.size⟩, ⟨G.witness.setWidth 64, G.len⟩] s t

theorem primePrepareWrites_bound {G : PrimeConfig} : ∀ r ∈ primePrepareWrites G.n, r.1 + r.2 ≤ G.size := by
  have width := G.width
  have room := G.room
  change primeExponent + 8 * G.n ≤ G.size at room
  intro r hr
  simp only [primePrepareWrites, setupRanges, prepareWrites, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl) <;>
    simp only [slot, stride, primeTwos, primeExponent] at * <;> omega

theorem primePrepare_testFrame {G : PrimeConfig} {s t : Mem}
    (O : Outs G.base (primePrepareWrites G.n) s t) (bound : G.size ≤ 2 ^ 64) : PrimeTestFrame G s t := by
  apply (sampleOuts_frame O (fun r hr => Nat.le_trans (primePrepareWrites_bound r hr) bound)).sub
  intro r hr
  obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
  exact ⟨⟨G.base, G.size⟩, by simp, Offset.sub_base _ (primePrepareWrites_bound item hi)⟩

theorem PrimeFrame.testFrame {G : PrimeConfig} {s t : Mem}
    (O : PrimeFrame G.base G.n (G.witness.setWidth 64) G.len s t) : PrimeTestFrame G s t := by
  apply O.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hr
    exact ⟨⟨G.base, G.size⟩, by simp, Offset.sub_base _ (primeWrites_bound G.width G.flagRoom item hi)⟩
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨⟨G.witness.setWidth 64, G.len⟩, by simp, fun _ h => h⟩

theorem PrimeTestFrame.tape {G : PrimeConfig} {s t : Mem} (O : PrimeTestFrame G s t) :
    Spec.Rsa.bytesAt t (G.tape.setWidth 64) G.tapeLen = Spec.Rsa.bytesAt s (G.tape.setWidth 64) G.tapeLen := by
  apply drawFrame_bytes O ?_ (by have := G.tapeLen32; omega)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact G.tapeScratch
  · exact G.tapeWitness
end VG.Proof.Dsa.X86.Generation
