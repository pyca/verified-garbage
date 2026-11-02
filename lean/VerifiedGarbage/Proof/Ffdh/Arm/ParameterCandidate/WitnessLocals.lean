module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
/-! The witness controller changes only its consumed-byte and passed-round counts. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/LocalStore.lean`, which only this module imported.
section

/-! Update one saved native policy word while retaining the other arguments. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem SavedFrame.after_store {s t : State} {values : Nat → BitVec 32} {slots : List Nat}
    {offset : Nat} {value : BitVec 32} {rs : List Reg} (h : SavedFrame values slots s)
    (fit : offset + 4 ≤ 72) (bounds : ∀ d ∈ slots, d + 4 ≤ 72)
    (separate : ∀ d ∈ slots, d ≠ offset → d + 4 ≤ offset ∨ offset + 4 ≤ d)
    (memory : t.mem = s.mem.writeW (State.addr (s.sp + BitVec.ofNat 32 offset)) value)
    (rest : Rest rs s t) :
    SavedFrame (fun d => if d = offset then value else values d) slots t := by
  refine ⟨?_, ?_⟩
  · rw [rest.sp]
    exact h.space.congr rest.wr
  · intro d hd
    rw [rest.sp, memory]
    by_cases same : d = offset
    · subst d
      rw [Mem.readW_writeW_self32, ite_eq_left rfl]
    · have disjoint : (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
          ⟨State.addr (s.sp + BitVec.ofNat 32 offset), 4⟩ := by
        rw [VG.Arm.addr_add (by have := h.space.nowrap; have := bounds d hd; omega),
          VG.Arm.addr_add (by have := h.space.nowrap; omega)]
        exact Offset.disjoint _ (separate d hd same) (by have := bounds d hd; omega) (by omega)
      rw [Mem.readW_writeW_sep (disjoint.sep (Region.contains_self _ 4) (Region.contains_self _ 4)) (by decide),
        ite_eq_right same]
      exact h.saved d hd

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/RoundMemory.lean`, which only this module imported.
section

/-! Local controller stores leave all shared primality constants unchanged. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt)

theorem RoundData.after_workspaceEq {base : BitVec 32} {capacity w n : Nat} {m m' : Mem}
    (h : RoundData base capacity w n m) (equal : WorkspaceEq (VG.Arm.State.addr base) (8 * capacity) m m') :
    RoundData base capacity w n m' := by
  have headerFits : 128 ≤ 8 * capacity := Nat.le_trans (by
    simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes]
    omega : 128 ≤ arrAt w 28) h.fits
  refine h.after_reads (fun _ fit => equal.word (bits := 64) (by omega)) ?_ ?_
  · intro q member
    have bound : q < 28 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    have arrayFits := Nat.le_trans (array_end_le (w := w) bound) h.fits
    unfold numAt
    rw [equal.read (arrAt w q) (8 * w) (by omega)]
  · have arrayFits := Nat.le_trans (array_end_le (w := w) (j := 27) (k := 28) (by decide)) h.fits
    exact equal.word (bits := 64) (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

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
