module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Params
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Tape
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! The candidate writes its u64 consumption result into private controller word 14. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.ParameterCandidate (CandidateParams)

theorem SearchParams.used_addr (p : SearchParams) :
    State.addr (p.control + 112#32) = off (State.addr p.control) 112 :=
  VG.Arm.addr_add (by have := p.controlFits; omega)

theorem SearchParams.used_fits (p : SearchParams) : (p.control + 112#32).toNat + 8 ≤ 2 ^ 32 := by
  have control := p.controlFits
  rw [BitVec.toNat_add]
  change (p.control.toNat + 112) % 2 ^ 32 + 8 ≤ 2 ^ 32
  rw [Nat.mod_eq_of_lt (by omega : p.control.toNat + 112 < 2 ^ 32)]
  omega

theorem SearchParams.used_sub (p : SearchParams) :
    (⟨State.addr (p.control + 112#32), 8⟩ : Region).Sub ⟨State.addr p.control, 128⟩ := by
  rw [p.used_addr]
  exact Offset.sub_base _ (by decide)

def SearchParams.candidateParams (p : SearchParams) (used : Nat)
    (room : used + p.c.length ≤ p.c.bytes.length) : CandidateParams where
  out := p.c.out
  usedPtr := p.control + 112#32
  tape := p.c.tape + BitVec.ofNat 32 used
  base := p.c.base
  bits := p.c.bits
  generator := p.c.generator
  capacity := p.c.capacity
  bytes := p.c.bytes.drop used
  minBits := p.c.minBits
  maxBits := p.c.maxBits
  generatorAllowed := p.c.generatorAllowed
  space := p.c.space
  scratchFits := p.c.scratchFits
  outputFits := p.c.outputFits
  usedFits := by exact p.used_fits
  tapeFits := by simpa only [List.length_drop] using p.source_fits used room
  tapeCount := by rw [List.length_drop]; have := p.c.tapeCount; omega
  outputUsed := by exact p.controlOutput.symm.sub_right p.used_sub
  outputScratch := p.c.outputScratch
  outputTape := by simpa only [List.length_drop] using p.c.outputTape.sub_right (p.source_sub used room)
  usedScratch := by exact p.controlScratch.sub_left p.used_sub
  usedTape := by
    simpa only [List.length_drop] using (p.controlTape.sub_left p.used_sub).sub_right (p.source_sub used room)
  tapeScratch := by simpa only [List.length_drop] using p.c.tapeScratch.sub_left (p.source_sub used room)

end VG.Proof.Ffdh.Arm.ParameterSearch
