module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LocalStore
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The witness controller changes only its consumed-byte and passed-round counts. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

private theorem values_used (p : WitnessParams) (used passed next : Nat) :
    (fun d => if d = 40 then BitVec.ofNat 32 next else witnessValues p used passed d) =
      witnessValues p next passed := by
  funext d
  by_cases same : d = 40
  · subst d; simp [witnessValues]
  · rw [ite_eq_right same]
    unfold witnessValues
    split <;> simp_all

private theorem values_passed (p : WitnessParams) (used passed next : Nat) :
    (fun d => if d = 56 then BitVec.ofNat 32 next else witnessValues p used passed d) =
      witnessValues p used next := by
  funext d
  by_cases same : d = 56
  · subst d; simp [witnessValues]
  · rw [ite_eq_right same]
    unfold witnessValues
    split <;> simp_all

private theorem storeLocal {s t : State} {p : WitnessParams} {used passed nextUsed nextPassed offset : Nat}
    {value : BitVec 32} {rs : List Reg} (h : WitnessState p used passed s)
    (slot : offset = 40 ∨ offset = 56)
    (values : (fun d => if d = offset then value else witnessValues p used passed d) =
      witnessValues p nextUsed nextPassed)
    (usedBound : nextUsed ≤ p.bytes.length) (passedBound : nextPassed ≤ p.checks)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 offset)) value)
    (rest : Rest rs s t) : WitnessState p nextUsed nextPassed t := by
  have fit : offset + 4 ≤ 72 := by rcases slot with rfl | rfl <;> decide
  have saved := h.saved.after_store fit (fun _ hd => witnessSlots_bound hd) (by
    intro d hd different
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases slot with rfl | rfl <;> omega) memory rest
  rw [values] at saved
  have data : RoundData p.base p.capacity p.words p.modulus t.mem := by
    rw [memory]
    exact h.data.after_workspaceEq (stackWrite_workspaceEq h.workspace h.saved.space h.stackScratch fit value)
  have changed : Frame [⟨State.addr (s.sp + BitVec.ofNat 32 offset), 4⟩] s.mem t.mem := by
    rw [memory]
    exact (Frame.refl _ _).writeW (by simp) value (Region.contains_self _ _)
  exact h.after_frame data saved usedBound passedBound (changed.mono (by
    rcases slot with rfl | rfl <;> simp [witnessRegions])) rest

theorem WitnessState.store_used {s t : State} {p : WitnessParams} {used passed next : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (bound : next ≤ p.bytes.length)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + 40#32)) (BitVec.ofNat 32 next))
    (rest : Rest rs s t) : WitnessState p next passed t :=
  storeLocal h (.inl rfl) (values_used p used passed next) bound h.passedBound memory rest

theorem WitnessState.store_passed {s t : State} {p : WitnessParams} {used passed next : Nat} {rs : List Reg}
    (h : WitnessState p used passed s) (bound : next ≤ p.checks)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + 56#32)) (BitVec.ofNat 32 next))
    (rest : Rest rs s t) : WitnessState p used next t :=
  storeLocal h (.inr rfl) (values_passed p used passed next) h.usedBound bound memory rest

end VG.Proof.Ffdh.Arm.ParameterCandidate
