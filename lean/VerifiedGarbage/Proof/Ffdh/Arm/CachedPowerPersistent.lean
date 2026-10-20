module

import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerCorrect
import VerifiedGarbage.Proof.Ffdh.Arm.CachedGenerationTable
public import VerifiedGarbage.Proof.Bignum.Arm.CombExpBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.CachedPowerMetadata
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

/-! Canonical contexts and the sampled scalar form the evaluator's read-only invariant. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CachedPower
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Bignum.Arm

theorem persistent {p : Inputs} {l : ScalarLayout p} {s : State} {eb : List Byte} {sp : BitVec 32}
    (cached : CachedGenerationContext p s) (calls : KeyCallMemory p s)
    (exponent : Octets p.base l.start p.len eb s) (size : eb.length=l.width) (stack : s.sp=sp) :
    CombExp.Persistent p.base l.start (table p) sp p.len p.w p.P p.G (bits p) eb s := by
  refine ⟨⟨calls.stack,stack⟩,⟨exponent.fits,exponent.readable,exponent.byte⟩,cached.table,?_,?_⟩
  · intro r hr
    simp only [CombExp.writeRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact exponent.separate
    · rw [size,←stack]; exact significant_below calls
  · intro r hr
    apply cached.tableSeparate r
    simp only [CombExp.writeRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · simp [keyCallWrites,keyWrites]
    · simp [keyCallWrites,keyWrites,stack]

end VG.Proof.Ffdh.Arm.CachedPower
