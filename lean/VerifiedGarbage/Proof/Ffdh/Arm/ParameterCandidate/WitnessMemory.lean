module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundStack
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Reconstruct arithmetic arguments from saved phase state and retain that
state across calls to the shared primality machinery. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem WitnessState.ready {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (ptr : s.gpr .r0 = p.base) :
    ArithmeticReady p.base p.capacity p.words s := by
  refine h.data.data.ready h.workspace ptr ?_
    (h.stackScratch.sub_left (Region.sub_prefix (by decide : 4 ≤ 72))) ?_
  · simpa only [BitVec.add_zero] using h.saved.read (d := 0) (by decide)
  · have saved := h.saved.saved 0 (by simp [witnessSlots])
    simpa only [BitVec.add_zero, witnessValues] using saved

theorem WitnessState.after_round {s t : State} {p : WitnessParams} {used passed : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (data : RoundData p.base p.capacity p.words p.modulus t.mem)
    (changed : Frame [⟨State.addr p.base, 8 * p.capacity⟩, FrameStack.belowA s.sp 56] s.mem t.mem)
    (rest : Rest rs s t) : WitnessState p used passed t :=
  h.after_frame data (h.saved.after_round (fun _ hd => witnessSlots_bound hd) h.stackBelow h.stackScratch changed rest)
    h.usedBound h.passedBound (changed.mono (by simp [witnessRegions])) rest

theorem WitnessState.after_workspace {s t : State} {p : WitnessParams} {used passed : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (data : RoundData p.base p.capacity p.words p.modulus t.mem)
    (changed : Frame [⟨State.addr p.base, 8 * p.capacity⟩] s.mem t.mem) (rest : Rest rs s t) :
    WitnessState p used passed t := h.after_round data (changed.mono (by simp)) rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
