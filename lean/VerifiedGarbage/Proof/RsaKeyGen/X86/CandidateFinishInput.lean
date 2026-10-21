module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestMetadata
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCore

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
  refine ⟨⟨S, by have := v.width_bounds.1; omega, v.slotFit (by decide), by omega,
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
