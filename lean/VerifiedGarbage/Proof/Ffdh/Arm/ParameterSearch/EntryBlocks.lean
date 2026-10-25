module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Incoming
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Save the register arguments before reading and retaining the incoming stack arguments. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (writeLow)
open VG.Proof.X25519.Arm (Rest)

theorem entryHead_ok (s : State) {p : SearchParams} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (out : s.gpr .r0 = p.c.out) (used : s.gpr .r2 = p.c.usedPtr)
    (bits : s.gpr .r3 = BitVec.ofNat 32 p.c.bits) :
    WP isa (.block [.ldrSp .r4 44, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r0 5,
      VG.Impl.Ffdh.Arm.ParameterSearch.stf .r2 6, VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 7]) s fun t =>
      (t.gpr .r4 = p.control ∧ t.mem = writeLow s.mem p.control
        [(5, p.c.out), (6, p.c.usedPtr), (7, BitVec.ofNat 32 p.c.bits)]) ∧ Rest [.r4] s t := by
  refine withRest_all [.r4] ?_ (by rfl) (by rfl)
  have arg := h.incoming 5 (by decide)
  have addr44 : State.addr (s.sp + 44#32) = off (State.addr s.sp) 44 :=
    VG.Arm.addr_add (by have := arg.fits; omega)
  have addr40 : State.addr (p.control + 40#32) = off (State.addr p.control) 40 :=
    VG.Arm.addr_add (by have := space.nowrap; omega)
  have addr48 : State.addr (p.control + 48#32) = off (State.addr p.control) 48 :=
    VG.Arm.addr_add (by have := space.nowrap; omega)
  have addr56 : State.addr (p.control + 56#32) = off (State.addr p.control) 56 :=
    VG.Arm.addr_add (by have := space.nowrap; omega)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf writeLow
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [addr44, arg.readable, arg.word, incomingValue, addr40, addr48, addr56,
    space.write (off := 40) (by decide), space.write (off := 48) (by decide),
    space.write (off := 56) (by decide), out, used, bits]

theorem entryZero_ok (s : State) {p : SearchParams} (h : EntryContext p s) :
    WP isa (.block [.mov .r3 (.imm 0), VG.Impl.Ffdh.Arm.ParameterSearch.stf .r3 4]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr p.control) 32) (0#32) ∧ Rest [.r3] s t := by
  refine withRest_all [.r3] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.stf
  ffrun [h.controller.addr (by decide : 4 < 16), h.controller.write (by decide : 4 < 16)]
  rfl

end VG.Proof.Ffdh.Arm.ParameterSearch
