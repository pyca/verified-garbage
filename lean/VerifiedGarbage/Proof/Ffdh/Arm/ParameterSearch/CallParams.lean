module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay

/-! ### `Ffdh.Arm.ParameterSearch.Tape`, which this module and modules that import it used -/

section

/-! A candidate sees exactly the nonempty remaining suffix of the public entropy tape. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

theorem SearchParams.source_addr (p : SearchParams) (used : Nat)
    (room : used + p.c.length ≤ p.c.bytes.length) :
    State.addr (p.c.tape + BitVec.ofNat 32 used) = off (State.addr p.c.tape) used := by
  have := p.c.tapeFits
  have := p.width_bounds.1
  exact VG.Arm.addr_add (by omega_arith)

theorem SearchParams.source_fits (p : SearchParams) (used : Nat)
    (room : used + p.c.length ≤ p.c.bytes.length) :
    (p.c.tape + BitVec.ofNat 32 used).toNat + (p.c.bytes.length - used) ≤ 2 ^ 32 := by
  have width := p.width_bounds.1
  have tape := p.c.tapeFits
  have usedFit : used < 2 ^ 32 := by have := p.c.tapeCount; omega_using [room, width, tape]
  have startFit : p.c.tape.toNat + used < 2 ^ 32 := by omega_using [room, width, tape]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedFit, Nat.mod_eq_of_lt startFit]
  omega_using [room, tape]

theorem SearchParams.source_sub (p : SearchParams) (used : Nat)
    (room : used + p.c.length ≤ p.c.bytes.length) :
    (⟨State.addr (p.c.tape + BitVec.ofNat 32 used), p.c.bytes.length - used⟩ : Region).Sub
      ⟨State.addr p.c.tape, p.c.bytes.length⟩ := by
  rw [p.source_addr used room]
  exact Offset.sub_base _ (by omega_using [room])

theorem SearchLive.source_read {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (room : used + p.c.length ≤ p.c.bytes.length) :
    InRegions (s.rd ++ s.wr) (State.addr (p.c.tape + BitVec.ofNat 32 used)) (p.c.bytes.length - used) := by
  rw [p.source_addr used room]
  exact VG.CallLay.inRegions_sub h.buffers.tapeRead (by omega_using [room]) (by have := p.c.tapeCount; omega_using [this])

theorem SearchLive.source_bytes {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (room : used + p.c.length ≤ p.c.bytes.length) :
    Spec.Rsa.bytesAt s.mem (State.addr (p.c.tape + BitVec.ofNat 32 used)) (p.c.bytes.length - used) = p.c.bytes.drop used := by
  rw [p.source_addr used room]
  have slice := VG.Proof.Dsa.bytesAt_slice s.mem (State.addr p.c.tape)
    (offset := used) (len := p.c.bytes.length - used) (by omega_using [room] : used + (p.c.bytes.length - used) ≤ p.c.bytes.length)
  rw [h.buffers.tapeBytes] at slice
  have taken : (p.c.bytes.drop used).take (p.c.bytes.length - used) = p.c.bytes.drop used := by
    rw [← (List.length_drop (i := used) (l := p.c.bytes)), List.take_length]
  rw [taken] at slice
  exact slice.symm

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! The candidate writes its u64 consumption result into private controller word 14. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.ParameterCandidate (CandidateParams)

theorem SearchParams.used_addr (p : SearchParams) :
    State.addr (p.control + 112#32) = off (State.addr p.control) 112 :=
  VG.Arm.addr_add (by have := p.controlFits; omega_using [this])

theorem SearchParams.used_fits (p : SearchParams) : (p.control + 112#32).toNat + 8 ≤ 2 ^ 32 := by
  have control := p.controlFits
  rw [BitVec.toNat_add]
  change (p.control.toNat + 112) % 2 ^ 32 + 8 ≤ 2 ^ 32
  rw [Nat.mod_eq_of_lt (by omega_using [control] : p.control.toNat + 112 < 2 ^ 32)]
  omega_using [control]

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
  tapeCount := by rw [List.length_drop]; have := p.c.tapeCount; omega_using [this]
  outputUsed := by exact p.controlOutput.symm.sub_right p.used_sub
  outputScratch := p.c.outputScratch
  outputTape := by simpa only [List.length_drop] using p.c.outputTape.sub_right (p.source_sub used room)
  usedScratch := by exact p.controlScratch.sub_left p.used_sub
  usedTape := by
    simpa only [List.length_drop] using (p.controlTape.sub_left p.used_sub).sub_right (p.source_sub used room)
  tapeScratch := by simpa only [List.length_drop] using p.c.tapeScratch.sub_left (p.source_sub used room)

end VG.Proof.Ffdh.Arm.ParameterSearch
