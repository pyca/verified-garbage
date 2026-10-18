module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Last

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Spec.MlKem

structure LastOutcomeW (w16 : Bool) (B : List Byte) (p out : Addr) (s t : State) : Prop where
 keep : Keep pairRegs s t
 frame : Frame (fullWrites p out) s.mem t.mem
 reduced : ReducedW (cw w16) t.mem out
 result : sampleNTT 280 B=none ∨ sampleNTT 280 B=some (polyAtW (cw w16) t.mem out)
 status : t.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleNTT 280 B).isSome then 1 else 0)

abbrev LastOutcome := LastOutcomeW false

theorem LastPostW.outcome {w16 : Bool} {B : List Byte} {p out : Addr} {s t : State} (h : LastPostW w16 B p out s t) :
    LastOutcomeW w16 B p out s t := by
  refine ⟨h.keep,h.frame,h.reduced,?_,?_⟩
  · rcases h.result with ⟨_,hr⟩ | ⟨_,hr⟩; exact Or.inr hr; exact Or.inl hr
  · rw [h.status]
    rcases h.result with ⟨hl,hr⟩ | ⟨hl,hr⟩ <;> simp [hl,hr]

end VG.Proof.MlKem.AArch64.Paired
