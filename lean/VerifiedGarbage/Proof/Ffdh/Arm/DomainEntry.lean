module

import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! The imported-domain ABI arguments are retained in native locals. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

structure DomainEntryRegs (p : Inputs) (s : State) : Prop where
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  scratch : s.gpr .r3 = p.base
  stackBase : s.gpr .r12 = s.sp

theorem DomainEntryRegs.after {p : Inputs} {s t : State}
    (h : DomainEntryRegs p s) (rest : Rest [] s t) : DomainEntryRegs p t :=
  ⟨(rest.gpr .r0 (by simp)).trans h.domain, (rest.gpr .r1 (by simp)).trans h.domainLength,
    (rest.gpr .r2 (by simp)).trans h.count, (rest.gpr .r3 (by simp)).trans h.scratch,
    (rest.gpr .r12 (by simp)).trans (h.stackBase.trans rest.sp.symm)⟩

theorem domainEntry_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (scratch : s.gpr .r3 = p.base) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry) s fun t =>
      Context p [0, 32, 28, 24] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckDomain.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun u moved => ?_
  have restU : Rest [.r12] s u := moved.rest (by simp)
  have argsU := h.of_mem moved.mem restU
  have frameU : Frame [⟨State.addr s.sp, 72⟩] s.mem u.mem := by rw [moved.mem]; exact Frame.refl _ _
  have regsU : DomainEntryRegs p u :=
    ⟨(moved.other .r0 (by decide)).trans domain, (moved.other .r1 (by decide)).trans domainLength,
      (moved.other .r2 (by decide)).trans count, (moved.other .r3 (by decide)).trans scratch,
      by rw [moved.gpr, moved.sp, BitVec.add_zero]⟩
  refine wp_store_arg .r0 24 argsU (by decide) (by decide) (by decide) regsU.domain regsU.stackBase fun v argsV frameV restV => ?_
  have regsV := regsU.after restV
  rw [restU.sp] at frameV
  have fullV := frameU.trans frameV
  refine wp_store_arg .r1 28 argsV (by decide) (by decide) (by decide) regsV.domainLength regsV.stackBase fun w argsW frameW restW => ?_
  have regsW := regsV.after restW
  rw [restV.sp, restU.sp] at frameW
  have fullW := fullV.trans frameW
  refine wp_store_arg .r2 32 argsW (by decide) (by decide) (by decide) regsW.count regsW.stackBase fun x argsX frameX restX => ?_
  have regsX := regsW.after restX
  rw [restW.sp, restV.sp, restU.sp] at frameX
  have fullX := fullW.trans frameX
  refine wp_mov (op2_reg _ _) fun y moved => ?_
  have restY : Rest [.r0] x y := moved.rest (by simp)
  have argsY := argsX.of_mem moved.mem restY
  have baseY : y.gpr .r0 = p.base := moved.gpr.trans regsX.scratch
  have stackY : y.gpr .r12 = y.sp := (moved.other .r12 (by decide)).trans (regsX.stackBase.trans moved.sp.symm)
  refine wp_store_arg .r0 0 argsY (by decide) (by decide) (by decide) baseY stackY fun t argsT frameT restT => WP.block_nil ?_
  refine ⟨⟨argsT, (restT.gpr .r0 (by simp)).trans baseY⟩, ?_⟩
  rw [restY.sp, restX.sp, restW.sp, restV.sp, restU.sp] at frameT
  rw [moved.mem] at frameT
  exact fullX.trans frameT

end VG.Proof.Ffdh.Arm
