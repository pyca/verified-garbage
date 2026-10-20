module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessLocals
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SaveWord
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Load one witness prefix and consume its exact byte count in native code. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem drawArgs_ok {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.drawArgs) s fun t =>
      (t.gpr .r0 = p.base ∧ t.gpr .r4 = p.tape + BitVec.ofNat 32 used ∧
        t.gpr .r6 = BitVec.ofNat 32 ((p.bits + 7) / 8) ∧
        t.gpr .r1 = BitVec.ofNat 32 (used + (p.bits + 7) / 8) ∧ t.mem = s.mem) ∧
        Rest [.r0, .r1, .r4, .r6] s t := by
  have base : s.mem.readW (State.addr s.sp) 32 = p.base := by
    simpa only [BitVec.add_zero, witnessValues] using h.saved.saved 0 (by simp [witnessSlots])
  have tape : s.mem.readW (State.addr (s.sp + 16#32)) 32 = p.tape := by
    simpa only [witnessValues] using h.saved.saved 16 (by simp [witnessSlots])
  have usedWord : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 used := by
    simpa only [witnessValues] using h.saved.saved 40 (by simp [witnessSlots])
  have width : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 ((p.bits + 7) / 8) := by
    simpa only [witnessValues] using h.saved.saved 48 (by simp [witnessSlots])
  refine withRest [.r0, .r1, .r4, .r6] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block VG.Impl.Ffdh.Arm.ParameterCandidate.drawArgs : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  have read0 : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4 := by
    simpa only [BitVec.add_zero] using h.saved.read (d := 0) (by decide)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.drawArgs
  ffrun [BitVec.add_zero, read0, h.saved.read (d := 16) (by decide), h.saved.read (d := 40) (by decide),
    h.saved.read (d := 48) (by decide), base, tape, usedWord, width, BitVec.ofNat_add_ofNat]

theorem drawHead_ok {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (enough : used + (p.bits + 7) / 8 ≤ p.bytes.length) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawHead s fun t =>
      WitnessState p (used + (p.bits + 7) / 8) passed t ∧
      t.gpr .r0 = p.base ∧ t.gpr .r4 = p.tape + BitVec.ofNat 32 used ∧
      t.gpr .r6 = BitVec.ofNat 32 ((p.bits + 7) / 8) ∧
      Frame [⟨State.addr (s.sp + 40#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.drawHead
  refine WP.seq (WP.mono (drawArgs_ok h) ?_)
  rintro u ⟨⟨base, tape, width, usedWord, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  refine WP.mono (saveR1_ok ctx.saved.space (d := 40) (by decide)) ?_
  rintro t ⟨memoryT, restT⟩
  rw [usedWord] at memoryT
  have finalState := ctx.store_used enough memoryT restT
  refine ⟨finalState, (restT.gpr .r0 (by simp)).trans base, (restT.gpr .r4 (by simp)).trans tape,
    (restT.gpr .r6 (by simp)).trans width, ?_, (rest.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))⟩
  rw [memoryT, memory, rest.sp]
  exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)

end VG.Proof.Ffdh.Arm.ParameterCandidate
