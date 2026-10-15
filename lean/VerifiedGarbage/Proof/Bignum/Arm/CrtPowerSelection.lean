module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPowerStage
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStageCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Public selection geometry and secret safe-modulus evidence for a factor power -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)

structure CrtPowerSelection (g : CrtGeometry) (bs : Fin 7 → List Byte) (child : BitVec 32) (slot : Nat) (s : State) : Prop where
  selected : CrtSelected g bs g.base s
  workspace : Workspace s child (8 * workspaceWords g.words)
  layout : CrtLayoutState child (workspaceWords g.words) g.words s.mem
  member : (⟨State.addr child, 8 * workspaceWords g.words⟩ : Region) ∈ crtRegions g.base (workspaceWords g.words) g.words
  slotFit : slot + 4 ≤ 8 * workspaceWords g.words
  slotSmall : slot < 4096
  link : s.mem.readW (off (State.addr g.base) slot) 32 = child
  bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1
  valid : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
    1 < numAt s.mem (State.addr child) g.words 0 ∧ numAt s.mem (State.addr child) g.words 0 % 2 = 1

theorem crt_selectPower_input (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} {child : BitVec 32} {slot : Nat}
    (h : CrtPowerSelection g bs child slot s) (i : Fin 6) (exponent : i = 3 ∨ i = 4) :
    WP isa (selectChild slot) s (CrtPrimePowerInput child g.input (g.source i.succ) (workspaceWords g.words)
      g.words g.length (g.sourceLength i.succ) (56 + 8 * i.val) (bs 1) (bs i.succ)) := by
  refine WP.mono (crt_selectLinked_ready s h.selected.1 h.workspace h.layout h.member h.slotFit h.slotSmall h.selected.2.ptr h.link) ?_
  rintro t ⟨sharedT, readyT, frame, rest⟩
  have eq := h.selected.1.workspace_eq_after_base h.workspace h.member frame
  have flag := acceptance_after_base_save frame rest
  have modulus := eq.number h.selected.1.buffers.context.arraysFit (by decide : 0 < 8)
  exact ⟨⟨readyT, by have := sharedT.stack.nowrap; omega, sharedT.stack.read (by decide),
    by rw [flag]; exact h.bit, by rw [flag, modulus]; exact h.valid⟩,
    sharedT.power_sources i exponent h.member⟩

end VG.Proof.Bignum.Arm
