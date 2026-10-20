module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhasePrepared
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontPrepare
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData

/-! Montgomery and exponent preparation preserve the witness-loop policy slots. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem locals_disjoint {s : State} {d offset : Nat} (stack : Workspace s s.sp 72)
    (before : d + 4 ≤ offset) (fit : offset + 4 ≤ 72) :
    (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
      ⟨State.addr (s.sp + BitVec.ofNat 32 offset), 4⟩ := by
  rw [VG.Arm.addr_add (by have := stack.nowrap; omega), VG.Arm.addr_add (by have := stack.nowrap; omega)]
  exact Offset.disjoint _ (.inl before) (by omega) (by omega)

theorem SavedFrame.after_preparation {s t : State} {base : BitVec 32} {capacity : Nat}
    {values : Nat → BitVec 32} {slots : List Nat} {rs : List Reg}
    (h : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 60)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (changed : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
      ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem) (rest : Rest rs s t) : SavedFrame values slots t := by
  refine h.after_frame changed rest ?_
  intro d hd r hr
  have fit := bounds d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [VG.Arm.addr_add (by have := h.space.nowrap; omega)]
    exact separate.sub_left (Offset.sub_base _ (by omega))
  · exact locals_disjoint h.space fit (by decide : 60 + 4 ≤ 72)
  · exact locals_disjoint h.space (by omega) (by decide : 64 + 4 ≤ 72)

theorem phasePrepared_saved_ok {s : State} {base src : BitVec 32} {capacity k : Nat}
    {values : Nat → BitVec 32} {slots : List Nat}
    (h : MontPrepInput base src capacity k s) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (saved : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 60)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s fun t =>
      RoundData base capacity (Spec.Rsa.modulusWords k)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) t.mem ∧
      SavedFrame values slots t ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (phasePrepared_ok h space saved.space separate) ?_
  rintro t ⟨data, changed, rest⟩
  exact ⟨data, saved.after_preparation bounds separate changed rest, changed, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
