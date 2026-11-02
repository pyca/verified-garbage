module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Proof.Bignum.Arm.PrepareAcceptedPrime
import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandLayout
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.Block

/-! # Import and prepare a factor in the narrow workspace

The factor is imported again from its saved argument, at the narrow width,
and replaced by three exactly when the full-width one was, so both workspaces
hold the same safe modulus.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure NarrowPrimeInput (base pp : BitVec 32) (len v k ps : Nat) (pb : List Byte) (s : State) : Prop
    extends LayoutFrameReady base len v s where
  source : SavedOperand base pp len k ps (ps + 4) pb s
  positive : 0 < k
  fit : k ≤ 8 * v
  stackFit : s.sp.toNat + 52 ≤ 2 ^ 32
  flagRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 48) 4
  bit : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≤ 1
  valid : (s.mem.readW (off (State.addr s.sp) 48) 32).toNat ≠ 0 →
    1 < Spec.Rsa.os2ip pb ∧ Spec.Rsa.os2ip pb % 2 = 1

theorem crt_narrowImport_ok (s : State) {base pp : BitVec 32} {len v k ps : Nat} {pb : List Byte}
    (h : NarrowPrimeInput base pp len v k ps pb s) :
    WP isa (savedOperand 0 ps (ps + 4)) s fun t =>
      AcceptedPrimeInput base len v t ∧ numAt t.mem (State.addr base) v 0 = Spec.Rsa.os2ip pb ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (savedOperandLayout_ok s h.toLayoutFrameReady h.source (by decide : 0 < 8) h.positive h.fit) ?_
  rintro t ⟨ready, value, _, frame, rest⟩
  have eq : WorkspaceEq (State.addr s.sp) 112 s.mem t.mem := WorkspaceEq.of_frame (by decide) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.source.stackSeparate)
  have flag : t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 := by
    rw [rest.sp]; exact eq.word (d := 48) (bits := 32) (by decide)
  refine ⟨⟨ready, by rw [rest.sp]; exact h.stackFit, by rw [rest.rd, rest.wr, rest.sp]; exact h.flagRead,
    by rw [flag]; exact h.bit, by rw [flag, value]; exact h.valid⟩, value, flag, frame, rest⟩

theorem crt_narrowPrime_ok (s : State) {base pp : BitVec 32} {len v k ps : Nat} {pb : List Byte}
    (h : NarrowPrimeInput base pp len v k ps pb s) (countFits : 128 * v < 2 ^ 32) :
    WP isa (narrowPrime ps) s fun t =>
      let M := safePrime (s.mem.readW (off (State.addr s.sp) 48) 32).toNat (Spec.Rsa.os2ip pb)
      ArithmeticReady base len v t ∧ numAt t.mem (State.addr base) v 0 = M ∧ M % 2 = 1 ∧
      numAt t.mem (State.addr base) v 4 = 2 ^ (128 * v) % M ∧
      t.mem.readW (off (State.addr t.sp) 48) 32 = s.mem.readW (off (State.addr s.sp) 48) 32 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [narrowPrime, WP.seq_iff]
  refine WP.mono (crt_narrowImport_ok s h) ?_
  rintro u ⟨accepted, value, flagU, frameU, restU⟩
  have valid := safePrime_valid accepted.valid
  refine WP.mono (prepareAcceptedPrime_ok u accepted countFits) ?_
  rintro t ⟨done, modulus, r2, frameT, restT⟩
  rw [value, flagU] at modulus r2 valid
  have eq : WorkspaceEq (State.addr u.sp) 112 u.mem t.mem := WorkspaceEq.of_frame (by decide) frameT
    (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      have sep := h.source.stackSeparate
      rw [← restU.sp] at sep
      exact sep)
  have flagT : t.mem.readW (off (State.addr t.sp) 48) 32 = u.mem.readW (off (State.addr u.sp) 48) 32 := by
    rw [restT.sp]; exact eq.word (d := 48) (bits := 32) (by decide)
  refine ⟨⟨done.workspace, done.layout, done.width, done.ptr, done.inverse,
      by rw [modulus]; exact valid.1, done.stackRead, done.stackSep, done.saved⟩,
    modulus, valid.2, r2, flagT.trans flagU, frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Bignum.Arm
