module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtBothPowers
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerSelection
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Exact validation evidence entering the two private powers -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)

structure CrtCheckedState (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  selected : CrtSelected g bs g.base s
  p : numAt s.mem (State.addr (crtP g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 2)
  q : numAt s.mem (State.addr (crtQ g.base g.words)) g.words 0 = Spec.Rsa.os2ip (bs 3)
  flag : s.mem.readW (off (State.addr s.sp) 48) 32 = (if crtAccepted bs then 1 else 0)

theorem CrtCheckedState.pSelection {s : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtCheckedState g bs s) : CrtPowerSelection g bs (crtP g.base g.words) 224 1 s := by
  refine ⟨h.selected, Or.inl ⟨rfl, rfl⟩, ?_, ?_, h.p⟩
  · rw [h.flag]; split <;> decide
  · rw [h.flag, h.p]
    by_cases accepted : crtAccepted bs
    · intro _; exact (h.selected.1.accepted_factors accepted).1
    · simp [accepted]

theorem crt_firstPower_qInput (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte}
    (h : CrtCheckedState g bs s) :
    WP isa (CrtFn.power 224 64 80) s (CrtPowerSelection g bs (crtQ g.base g.words) 228 2) := by
  have input := h.pSelection
  refine WP.mono (crt_powerStage_ok s h.selected.1 h.selected.2 input.kind 1 3 (Or.inl ⟨rfl, rfl⟩)
    input.bit input.valid input.prime) ?_
  rintro t ⟨sharedT, readyT, _, flag, frame, _⟩
  have eq := h.selected.1.workspace_eq_after_power h.selected.1.buffers.context.q (by simp [crtRegions])
    h.selected.1.buffers.context.sepPQ.symm h.selected.1.buffers.context.sepQN frame
  have qValue := (eq.number h.selected.1.buffers.context.arraysFit (by decide : 0 < 8)).trans h.q
  refine ⟨⟨sharedT, readyT⟩, Or.inr ⟨rfl, rfl⟩, ?_, ?_, qValue⟩
  · rw [flag]; exact input.bit
  · rw [flag, h.flag, qValue]
    by_cases accepted : crtAccepted bs
    · intro _; exact (h.selected.1.accepted_factors accepted).2
    · simp [accepted]

end VG.Proof.Bignum.Arm
