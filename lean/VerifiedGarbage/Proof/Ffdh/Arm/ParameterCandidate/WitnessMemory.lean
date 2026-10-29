module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
/-! Reconstruct arithmetic arguments from saved phase state and retain that
state across calls to the shared primality machinery. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/RoundStack.lean`, which only this module imported.
section

/-! The shared Miller–Rabin call writes below the caller's saved arguments. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem SavedFrame.after_round {s t : State} {base : BitVec 32} {capacity : Nat}
    {values : Nat → BitVec 32} {slots : List Nat} {rs : List Reg}
    (h : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 72)
    (stackBelow : 56 ≤ s.sp.toNat)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (changed : Frame [⟨State.addr base, 8 * capacity⟩, FrameStack.belowA s.sp 56] s.mem t.mem)
    (rest : Rest rs s t) : SavedFrame values slots t := by
  refine h.after_frame changed rest ?_
  intro d hd r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have fit := bounds d hd
  rcases hr with rfl | rfl
  · rw [VG.Arm.addr_add (by have := h.space.nowrap; omega)]
    exact separate.sub_left (Offset.sub_base _ fit)
  · change (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
      ⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩
    rw [VG.Arm.addr_add (by have := h.space.nowrap; omega), FrameStack.addr_sub' stackBelow]
    exact Offset.disjoint_below _ (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

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
