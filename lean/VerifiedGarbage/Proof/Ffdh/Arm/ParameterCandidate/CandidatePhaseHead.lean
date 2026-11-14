module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseHeader
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseState
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Ffdh.Arm.ParameterCandidate.PhasePieces`, which only this module used -/

section

/-! Public policy setup in small instruction blocks, without increasing
symbolic-execution budgets for the complete frame initialization. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PhaseMath.lean`, which only this module imported.
section

/-! Native public bit-length policy for the two safe-prime phases. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate

theorem witnessWidth_word {bits : Nat} (bound : bits ≤ 8192) :
    (BitVec.ofNat 32 bits + 7) >>> 3 = BitVec.ofNat 32 ((bits + 7) / 8) := by
  change (BitVec.ofNat 32 bits + BitVec.ofNat 32 7) >>> 3 = _
  rw [BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : bits + 7 < 2 ^ 32), Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : (bits + 7) / 8 < 2 ^ 32)]

theorem checks_word {bits : Nat} (positive : 0 < bits) (bound : bits ≤ 8192) :
    (((if decide (2048 ≤ (BitVec.ofNat 32 bits - 1).toNat) = true then (1 : BitVec 32) else 0) <<< 6) + 64) =
      BitVec.ofNat 32 (VG.Spec.Ffdh.primeChecks bits) := by
  have sub : BitVec.ofNat 32 bits - 1 = BitVec.ofNat 32 (bits - 1) := by
    change BitVec.ofNat 32 bits - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive]
  rw [sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : bits - 1 < 2 ^ 32)]
  by_cases small : bits ≤ 2048
  · have flag : ¬ 2048 ≤ bits - 1 := by omega
    simp only [flag, decide_false, Bool.false_eq_true, ite_false,
      VG.Spec.Ffdh.primeChecks, small, ite_true]
    rfl
  · have flag : 2048 ≤ bits - 1 := by omega
    simp only [flag, decide_true, ite_true, VG.Spec.Ffdh.primeChecks, small, ite_false]
    rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Bignum.Arm (Workspace)

private theorem flagsWr (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
private theorem flagsSp (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl

theorem phaseBitHead_ok (q : Bool) (s : State) {bits : Nat} (positive : 0 < bits)
    (read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 24#32)) 4)
    (write : InRegions s.wr (State.addr (s.sp + 44#32)) 4)
    (value : s.mem.readW (State.addr (s.sp + 24#32)) 32 = BitVec.ofNat 32 bits) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseBitHead q)) s fun t =>
      (t.gpr .r3 = BitVec.ofNat 32 (phaseBits q bits) ∧
        t.mem = s.mem.writeW (State.addr (s.sp + 44#32)) (BitVec.ofNat 32 (phaseBits q bits))) ∧
        Rest [.r3, .r12] s t := by
  refine withRest_all [.r3, .r12] ?_ (by cases q <;> rfl) (by rfl)
  have sub : BitVec.ofNat 32 bits - 1 = BitVec.ofNat 32 (bits - 1) := by
    change BitVec.ofNat 32 bits - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive]
  cases q <;> unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseBitHead VG.Impl.Ffdh.Arm.ParameterCandidate.save <;>
    ffrun [List.cons_append, List.nil_append, BitVec.add_zero, read, write, value, sub, phaseBits]

theorem phaseWidth_ok (s : State) {bits : Nat} (bound : bits ≤ 8192)
    (value : s.gpr .r3 = BitVec.ofNat 32 bits)
    (write : InRegions s.wr (State.addr (s.sp + 48#32)) 4) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.phaseWidth) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 48#32)) (BitVec.ofNat 32 ((bits + 7) / 8))) ∧
        Rest [.r4, .r12] s t := by
  refine withRest_all [.r4, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseWidth VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, value, write, witnessWidth_word bound]

theorem phaseChecks_ok (s : State) {bits : Nat} (positive : 0 < bits) (bound : bits ≤ 8192)
    (value : s.gpr .r3 = BitVec.ofNat 32 bits)
    (write : InRegions s.wr (State.addr (s.sp + 52#32)) 4) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.phaseChecks) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 52#32)) (BitVec.ofNat 32 (VG.Spec.Ffdh.primeChecks bits))) ∧
        Rest [.r3, .r5, .r12] s t := by
  refine withRest_all [.r3, .r5, .r12] ?_ (by rfl) (by rfl)
  have count := checks_word positive bound
  simp only [show (0 : BitVec 32) = 0#32 from rfl, decide_eq_true_eq] at count
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseChecks VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, BitVec.zero_add,
    show (0 : BitVec 32) = 0#32 from rfl, show (2048 : BitVec 32).toNat = 2048 from rfl,
    show encodable (2048 : BitVec 32) = true from by decide,
    value, write, count, decide_eq_true_eq, flagsWr, flagsSp]

theorem phasePassed_ok (s : State) (write : InRegions s.wr (State.addr (s.sp + 56#32)) 4) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.phasePassed) s fun t =>
      (t.mem = s.mem.writeW (State.addr (s.sp + 56#32)) (0#32)) ∧ Rest [.r1, .r12] s t := by
  refine withRest_all [.r1, .r12] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phasePassed VG.Impl.Ffdh.Arm.ParameterCandidate.save
  ffrun [List.cons_append, List.nil_append, BitVec.add_zero, write,
    show (0 : BitVec 32) = 0#32 from rfl]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Initialize the q/p policy without changing candidate metadata or entropy accounting. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PhaseHead.lean`, which only this module imported.
section

/-! Compose the native policy setup for q and p. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Bignum.Arm (Workspace)

theorem phaseHead_ok (q : Bool) (s : State) {bits : Nat} (lower : 512 ≤ bits) (upper : bits ≤ 8192)
    (space : Workspace s s.sp 72)
    (value : s.mem.readW (State.addr (s.sp + 24#32)) 32 = BitVec.ofNat 32 bits) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) s fun t =>
      (t.mem = phaseMemory s q bits) ∧ Rest [.r1, .r3, .r4, .r5, .r12] s t := by
  have read24 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 24#32)) 4 := by
    rw [VG.Arm.addr_add (by have := space.nowrap; omega)]
    exact space.read (by decide)
  have writes (d : Nat) (bound : d + 4 ≤ 72) : InRegions s.wr (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := space.nowrap; omega)]
    exact space.write bound
  have phasePositive : 0 < phaseBits q bits := by cases q <;> simp [phaseBits] <;> omega
  have phaseBound : phaseBits q bits ≤ 8192 := by cases q <;> simp [phaseBits] <;> omega
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (phaseBitHead_ok q s (by omega) read24 (writes 44 (by decide)) value) ?_
  rintro u ⟨⟨bitValue, memU⟩, restU⟩
  rw [WP.block_append_iff]
  refine WP.mono (phaseWidth_ok u phaseBound bitValue (by rw [restU.wr, restU.sp]; exact writes 48 (by decide))) ?_
  rintro v ⟨memV, restV⟩
  rw [WP.block_append_iff]
  have stable : v.gpr .r3 = BitVec.ofNat 32 (phaseBits q bits) := (restV.gpr .r3 (by simp)).trans bitValue
  refine WP.mono (phaseChecks_ok v phasePositive phaseBound stable (by
    rw [restV.wr, restU.wr, restV.sp, restU.sp]; exact writes 52 (by decide))) ?_
  rintro w ⟨memW, restW⟩
  refine WP.mono (phasePassed_ok w (by
    rw [restW.wr, restV.wr, restU.wr, restW.sp, restV.sp, restU.sp]; exact writes 56 (by decide))) ?_
  rintro t ⟨memT, restT⟩
  refine ⟨?_, (restU.mono (by simp)).trans ((restV.mono (by simp)).trans
    ((restW.mono (by simp)).trans (restT.mono (by simp))))⟩
  rw [memT, memW, memV, memU, restW.sp, restV.sp, restU.sp]
  rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem candidatePhaseHead_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (q : Bool) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) s fun t =>
      CandidateContext p consumed t ∧
      SavedFrame (witnessValues (candidatePhase p q) consumed 0) witnessSlots t ∧
      Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have bits : s.mem.readW (State.addr (s.sp + 24#32)) 32 = BitVec.ofNat 32 p.bits :=
    h.saved.saved 24 (by decide)
  refine WP.mono (phaseHead_ok q s p.minBits p.maxBits h.saved.space bits) ?_
  rintro t ⟨memory, rest⟩
  have changed : Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem t.mem := by
    rw [memory]
    exact phaseMemory_frame q p.bits h.saved.space.nowrap
  have candidateChanged : Frame (candidateRegions p s.sp) s.mem t.mem := by
    refine changed.sub ?_
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    refine ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [candidateRegions], ?_⟩
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this]), VG.Arm.addr_add (by have := h.saved.space.nowrap; omega_using [this])]
    exact Offset.sub _ (by decide) (by decide)
  have context : CandidateContext p consumed t := by
    refine h.after_frame h.consumedBound ?_ candidateChanged rest
    rw [rest.sp, memory, phaseMemory_word h.saved.space.nowrap (by decide : 40 + 4 ≤ 72) (by decide)]
    exact h.saved.saved 40 (by decide)
  refine ⟨context, ⟨?_, ?_⟩, changed, rest.mono (by simp [roundClobbers])⟩
  · rw [rest.sp]
    exact h.saved.space.congr rest.wr
  · intro d hd
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [rest.sp, memory, phaseMemory_word h.saved.space.nowrap (by decide) (by decide)]
    all_goals first | rfl | exact h.saved.saved _ (by decide)

end VG.Proof.Ffdh.Arm.ParameterCandidate
