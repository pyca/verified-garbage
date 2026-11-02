module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtPrepareState
public import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout

/-! # Import the public modulus without disturbing either CRT factor workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure CrtLoaded (base : BitVec 32) (size w : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  context : CrtSetupContext base (workspaceWords w) w s
  ready : LayoutFrameReady base (workspaceWords w) w s
  main : CrtMainState base (workspaceWords w) w s.mem
  p : CrtPrimeState (crtP base w) base (workspaceWords w) w s.mem
  q : CrtPrimeState (crtQ base w) base (workspaceWords w) w s.mem
  stackFits : s.sp.toNat + 12 ≤ 2 ^ 32
  stackWrite : InRegions s.wr (off (State.addr s.sp) 8) 4
  stackSeparate : Region.Disjoint ⟨State.addr s.sp, 112⟩ ⟨State.addr base, size⟩
  storageFits : totalBytes w ≤ size

theorem crt_importModulus_ok (s : State) {base np : BitVec 32} {size w k : Nat} {nb : List Byte}
    (h : CrtInitialized base np size w k nb s) :
    WP isa (savedOperand 0 8 12) s fun t => CrtLoaded base size w t ∧
      numAt t.mem (State.addr base) w 0 = Spec.Rsa.os2ip nb ∧
      Frame [⟨State.addr base, 8 * workspaceWords w⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (savedOperandLayout_ok s h.ready h.source (by decide : 0 < 8) h.positive h.inputFits) ?_
  rintro t ⟨ready, value, keeps, frame, rest⟩
  have size := h.context.size
  have main : CrtMainState base (workspaceWords w) w t.mem :=
    ⟨⟨ready.layout, ready.width⟩,
      (keeps_header_readW keeps size (d := 224) (bits := 32) (by decide)).trans h.main.p,
      (keeps_header_readW keeps size (d := 228) (bits := 32) (by decide)).trans h.main.q,
      (keeps_header_readW keeps size (d := 232) (bits := 32) (by decide)).trans h.main.product,
      (keeps_header_readW keeps size (d := 236) (bits := 32) (by decide)).trans h.main.compare,
      (keeps_header_readW keeps size (d := 240) (bits := 32) (by decide)).trans h.main.modulus⟩
  exact ⟨⟨h.workspace.congr rest.wr, h.context.congr rest.wr, ready, main,
    h.p.congr (h.context.p.eq_of_frame h.context.sepMP.symm frame),
    h.q.congr (h.context.q.eq_of_frame h.context.sepMQ.symm frame),
    by rw [rest.sp]; have := h.source.nowrap; omega,
    by rw [rest.wr, rest.sp]; exact h.stackWrite,
    by rw [rest.sp]; exact h.stackSeparate, h.storageFits⟩, value, frame, rest⟩

end VG.Proof.Bignum.Arm
