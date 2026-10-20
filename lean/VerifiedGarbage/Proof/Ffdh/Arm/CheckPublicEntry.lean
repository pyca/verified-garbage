module

public import VerifiedGarbage.Proof.Ffdh.Arm.EntryStore
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack

/-! The imported-public-value ABI arguments are retained in native locals. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PublicEntryRegs (p : Inputs) (s : State) : Prop where
  domain : s.gpr .r0 = p.domain
  domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length
  count : s.gpr .r2 = BitVec.ofNat 32 p.k
  publicValue : s.gpr .r3 = p.publicValue
  stackBase : s.gpr .r12 = s.sp

theorem PublicEntryRegs.after {p : Inputs} {s t : State}
    (h : PublicEntryRegs p s) (rest : Rest [] s t) : PublicEntryRegs p t :=
  ⟨(rest.gpr .r0 (by simp)).trans h.domain, (rest.gpr .r1 (by simp)).trans h.domainLength,
    (rest.gpr .r2 (by simp)).trans h.count, (rest.gpr .r3 (by simp)).trans h.publicValue,
    (rest.gpr .r12 (by simp)).trans (h.stackBase.trans rest.sp.symm)⟩

theorem checkPublicEntry_ok (s : State) {p : Inputs}
    (h : ArgumentMemory p [] s) (incoming : IncomingScratch p s)
    (domain : s.gpr .r0 = p.domain) (domainLength : s.gpr .r1 = BitVec.ofNat 32 p.dom.length)
    (count : s.gpr .r2 = BitVec.ofNat 32 p.k) (publicValue : s.gpr .r3 = p.publicValue) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry) s fun t =>
      Context p [0, 36, 32, 28, 24] t ∧ Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem := by
  unfold VG.Impl.Ffdh.Arm.Domain.CheckPublic.entry VG.Impl.Ffdh.Arm.Domain.st
  refine wp_stackAddr (by decide) fun u moved => ?_
  have restU : Rest [.r12] s u := moved.rest (by simp)
  have argsU := h.of_mem moved.mem restU
  have frameU : Frame [⟨State.addr s.sp, 72⟩] s.mem u.mem := by rw [moved.mem]; exact Frame.refl _ _
  have incomingU := incoming.after frameU restU
  have regsU : PublicEntryRegs p u :=
    ⟨(moved.other .r0 (by decide)).trans domain, (moved.other .r1 (by decide)).trans domainLength,
      (moved.other .r2 (by decide)).trans count, (moved.other .r3 (by decide)).trans publicValue,
      by rw [moved.gpr, moved.sp, BitVec.add_zero]⟩
  refine wp_store_arg .r0 24 argsU (by decide) (by decide) (by decide) regsU.domain regsU.stackBase fun v argsV frameV restV => ?_
  have regsV := regsU.after restV
  have incomingV := incomingU.after frameV restV
  rw [restU.sp] at frameV
  have fullV := frameU.trans frameV
  refine wp_store_arg .r1 28 argsV (by decide) (by decide) (by decide) regsV.domainLength regsV.stackBase fun w argsW frameW restW => ?_
  have regsW := regsV.after restW
  have incomingW := incomingV.after frameW restW
  rw [restV.sp, restU.sp] at frameW
  have fullW := fullV.trans frameW
  refine wp_store_arg .r2 32 argsW (by decide) (by decide) (by decide) regsW.count regsW.stackBase fun x argsX frameX restX => ?_
  have regsX := regsW.after restX
  have incomingX := incomingW.after frameX restX
  rw [restW.sp, restV.sp, restU.sp] at frameX
  have fullX := fullW.trans frameX
  refine wp_store_arg .r3 36 argsX (by decide) (by decide) (by decide) regsX.publicValue regsX.stackBase fun y argsY frameY restY => ?_
  have regsY := regsX.after restY
  have incomingY := incomingX.after frameY restY
  rw [restX.sp, restW.sp, restV.sp, restU.sp] at frameY
  have fullY := fullX.trans frameY
  refine wp_loadStack (a := off (State.addr y.sp) 132) (by decide)
    (addr_add (by have := incomingY.fits; omega)) incomingY.readable fun z loaded => ?_
  have restZ : Rest [.r0] y z := loaded.rest (by simp)
  have argsZ := argsY.of_mem loaded.mem restZ
  have baseZ : z.gpr .r0 = p.base := loaded.gpr.trans incomingY.value
  have spZ : z.gpr .r12 = z.sp := (loaded.other .r12 (by decide)).trans (regsY.stackBase.trans loaded.sp.symm)
  refine wp_store_arg .r0 0 argsZ (by decide) (by decide) (by decide) baseZ spZ fun t argsT frameT restT => WP.block_nil ?_
  refine ⟨⟨argsT, (restT.gpr .r0 (by simp)).trans baseZ⟩, ?_⟩
  rw [restZ.sp, restY.sp, restX.sp, restW.sp, restV.sp, restU.sp] at frameT
  rw [loaded.mem] at frameT
  exact fullY.trans frameT

end VG.Proof.Ffdh.Arm
