module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCore
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareMetadata

/-! # Prepared testing retains the output pointers required by every finish branch -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateTest
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def protectedHeader (d bytes : Nat) : Prop := d + bytes ≤ 8 ∨ 16 ≤ d ∧ d + bytes ≤ 48

theorem ranges_apart {g : Geometry} {d bytes : Nat} (safe : protectedHeader d bytes)
    {r : Nat × Nat} (mem : r ∈ ranges g) : d + bytes ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  rcases List.mem_append.mp mem with mem | mem
  · exact Prepare.ranges_apart (by unfold protectedHeader at safe; left; omega) mem
  · simp only [MillerRabinLoop.ranges, WitnessChecks.ranges, WitnessStep.ranges,
      WitnessRound.ranges, WitnessMont.ranges, montWrites, roundWrites,
      WitnessCount.ranges, WitnessCount.nextRanges, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    repeat' first
      | (rcases mem with mem | mem)
      | (rcases mem with rfl)
    all_goals
      simp only [Geometry.array, Geometry.words, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes,
        VG.Impl.RsaKeyGen.X86.WitnessRound.uniformOffset,
        VG.Impl.RsaKeyGen.X86.WitnessCount.statusOffset,
        VG.Impl.RsaKeyGen.X86.WitnessCount.roundsOffset,
        VG.Impl.RsaKeyGen.X86.WitnessCount.uniformOffset]
      unfold protectedHeader at safe
      omega

theorem metadata32 {g : Geometry} (v : g.Valid) {m m' : Mem}
    (W : WorkspaceFrame g (ranges g) m m') {d : Nat} (safe : protectedHeader d 4) :
    m'.readW (off g.W d) 32 = m.readW (off g.W d) 32 := by
  apply W.read32 (by have := v.headerFit; unfold protectedHeader at safe; omega)
  exact fun _ mem => ranges_apart safe mem

end VG.Proof.RsaKeyGen.X86.CandidateTest
