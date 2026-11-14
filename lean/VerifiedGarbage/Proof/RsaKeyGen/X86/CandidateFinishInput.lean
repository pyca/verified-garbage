module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCore
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareMetadata

/-! ### `RsaKeyGen.X86.CandidateTestMetadata`, which only this module used -/

section

/-! # Prepared testing retains the output pointers required by every finish branch -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateTest
open VG VG.Proof.Mont VG.Proof.MillerRabin.X86

def protectedHeader (d bytes : Nat) : Prop := d + bytes ≤ 8 ∨ 16 ≤ d ∧ d + bytes ≤ 48

theorem ranges_apart {g : Geometry} {d bytes : Nat} (safe : protectedHeader d bytes)
    {r : Nat × Nat} (mem : r ∈ ranges g) : d + bytes ≤ r.1 ∨ r.1 + r.2 ≤ d := by
  rcases List.mem_append.mp mem with mem | mem
  · exact Prepare.ranges_apart (by unfold protectedHeader at safe; left; omega_using [safe]) mem
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
      omega_using [safe]

theorem metadata32 {g : Geometry} (v : g.Valid) {m m' : Mem}
    (W : WorkspaceFrame g (ranges g) m m') {d : Nat} (safe : protectedHeader d 4) :
    m'.readW (off g.W d) 32 = m.readW (off g.W d) 32 := by
  apply W.read32 (by have := v.headerFit; unfold protectedHeader at safe; omega_using [safe, this])
  exact fun _ mem => ranges_apart safe mem

end VG.Proof.RsaKeyGen.X86.CandidateTest

end

end


/-! # Live candidate state supplies every pointer and permission needed by the finish paths -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

def FinishReady (E : Environment) (c : Nat) (s : State) : Prop :=
  CandidateFinish.PrimeInput E.base E.size E.width c E.out E.used (s.mem.readW (off E.base 152) 32) s ∧
  Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0

theorem finish_ready {E : Environment} (v : E.Valid) {c : Nat} {s : State}
    (S : Scr s E.base E.size)
    (out : s.mem.readW (off E.base 0) 32 = E.out)
    (length : s.mem.readW (off E.base 4) 32 = BitVec.ofNat 32 E.length)
    (used : s.mem.readW (off E.base 44) 32 = E.used)
    (outWrite : InRegions s.wr (E.out.setWidth 64) E.length)
    (usedWrite : VG.Proof.Mont.X86.Rt.Ws s (E.used.setWidth 64) 8)
    (value : val32 s.mem E.base (slot E.width 0) (2 * E.width) = c)
    (zeros : Spec.Rsa.bytesAt s.mem (E.out.setWidth 64) E.length = List.replicate E.length 0) : FinishReady E c s := by
  have space : 256 ≤ E.size := v.geometry.headerFit
  refine ⟨⟨S, by have := v.width_bounds.1; omega_using [this], v.slotFit (by decide), by omega_using [space],
    out, ?_, used, rfl, value, ?_, ?_, usedWrite, ?_, ?_⟩, zeros⟩
  · rw [v.length_eq]; exact length
  · rw [v.length_eq]; exact v.outFit
  · rw [v.length_eq]; exact outWrite
  · rw [v.length_eq]; exact v.outWorkspace.symm
  · rw [v.length_eq]; exact v.outUsed

theorem Drawn.finishReady {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) : FinishReady E (candidateValue E entropy) s :=
  finish_ready v D.input.scratch D.input.out_eq (D.input.header 1 (by decide)) D.input.usedPointer
    D.input.outWrite D.input.usedWrite D.candidate D.zeros

theorem Drawn.finishReady_after_test {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (D : Drawn E eBytes pBytes entropy s)
    (value : val32 t.mem E.base (slot E.width 0) (2 * E.width) = candidateValue E entropy)
    (W : WorkspaceFrame E.geometry (CandidateTest.ranges E.geometry) s.mem t.mem)
    (F : WorkFrame E s.mem t.mem) (K : Keeps WitnessStep.clob s t) :
    FinishReady E (candidateValue E entropy) t := by
  have out := CandidateTest.metadata32 v.geometry W (d := 0) (by left; decide)
  have length := CandidateTest.metadata32 v.geometry W (d := 4) (by left; decide)
  have used := CandidateTest.metadata32 v.geometry W (d := 44) (by right; constructor <;> decide)
  exact finish_ready v (D.input.scratch.of_keeps K (by unfold WitnessStep.clob; decide))
    (out.trans D.input.out_eq) (length.trans (D.input.header 1 (by decide))) (used.trans D.input.usedPointer)
    (by rw [K.2.2]; exact D.input.outWrite) (D.input.usedWrite.of_keeps K) value ((F.output v).trans D.zeros)

end VG.Proof.RsaKeyGen.X86.Candidate
