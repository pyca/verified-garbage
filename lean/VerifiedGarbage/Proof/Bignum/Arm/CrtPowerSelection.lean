module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
public import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
public import VerifiedGarbage.Proof.Bignum.Arm.CrtNarrowShared
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimePowerInput
import VerifiedGarbage.Proof.Bignum.Arm.CrtSelectWorkspace
import VerifiedGarbage.Proof.Bignum.Arm.CrtSharedPowerSources
import VerifiedGarbage.Proof.Bignum.Layout

/-! # Public selection geometry and secret safe-modulus evidence for a factor power -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)

structure CrtPowerSelection (g : CrtGeometry) (bs : Fin 7 → List Byte) (child : BitVec 32) (slot : Nat) (j : Fin 6)
    (s : State) : Prop where
  selected : CrtSelected g bs g.base s
  kind : CrtChild g child slot
  bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1
  valid : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
    1 < numAt s.mem (State.addr child) g.words 0 ∧ numAt s.mem (State.addr child) g.words 0 % 2 = 1
  prime : numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs j.succ)

/-- The paired input of a factor's narrow power. -/
def CrtNarrowInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (child : BitVec 32) (j i : Fin 6) (s : State) : Prop :=
  CrtShared g bs s ∧ CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words) g.words
    g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ) s ∧
    numAt s.mem (State.addr child) g.words 0 = Spec.Rsa.os2ip (bs j.succ)

theorem crt_selectPower_input (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    {j : Fin 6} (h : CrtPowerSelection g bs child slot j s) (i : Fin 6) (exponent : i = 3 ∨ i = 4) :
    WP isa (selectChild slot) s (CrtNarrowInput g bs child j i) := by
  obtain ⟨member, ws, layout, _, slotFit, slotSmall, link⟩ := h.selected.1.child h.kind
  refine WP.mono (crt_selectLinked_ready s h.selected.1 ws layout member slotFit slotSmall h.selected.2.ptr link) ?_
  rintro t ⟨sharedT, readyT, frame, rest⟩
  have eq := h.selected.1.workspace_eq_after_base ws member frame
  have flag := acceptance_after_base_save frame rest
  have modulus := eq.number h.selected.1.buffers.context.arraysFit (by decide : 0 < 8)
  exact ⟨sharedT, ⟨⟨readyT, by have := sharedT.stack.nowrap; omega, sharedT.stack.read (by decide),
    by rw [flag]; exact h.bit, by rw [flag, modulus]; exact h.valid⟩,
    sharedT.power_sources i exponent member⟩, by rw [modulus]; exact h.prime⟩

end VG.Proof.Bignum.Arm
