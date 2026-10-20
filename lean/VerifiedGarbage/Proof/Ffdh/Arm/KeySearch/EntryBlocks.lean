module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Incoming
import VerifiedGarbage.Proof.Framework.Offset

/-! Loading the controller pointer and retaining the two output pointers;
finishing the native argument snapshot with a zero consumed-byte count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem entryHead_ok (s : State) {p : KeyPublic} (h : EntryArguments p s)
    (space : Workspace s p.control 128) (x : s.gpr .r0 = p.xp) (y : s.gpr .r2 = p.yp) :
    WP isa (.block [.ldrSp .r4 56, VG.Impl.Ffdh.Arm.KeySearch.stf .r0 5,
      VG.Impl.Ffdh.Arm.KeySearch.stf .r2 6]) s fun t =>
      (t.gpr .r4 = p.control ∧ t.mem = writeLow s.mem p.control [(5, p.xp), (6, p.yp)]) ∧ Rest [.r4] s t := by
  refine withRest [.r4] ?_ (by
    intro r hr instr hi
    simp only [instrs, List.mem_cons, List.not_mem_nil, or_false] at hi
    have ne : r ≠ .r4 := by simpa only [List.mem_singleton] using hr
    rcases hi with rfl | rfl | rfl <;>
      simp [VG.Impl.Ffdh.Arm.KeySearch.stf, clobbers, dstOf, Ne.symm ne]) (by rfl)
  have arg := h.incoming 8 (by decide)
  have addr56 : State.addr (s.sp + 56#32) = off (State.addr s.sp) 56 :=
    VG.Arm.addr_add (by have := arg.fits; omega)
  have addr40 : State.addr (p.control + 40#32) = off (State.addr p.control) 40 :=
    VG.Arm.addr_add (by have := space.nowrap; omega)
  have addr48 : State.addr (p.control + 48#32) = off (State.addr p.control) 48 :=
    VG.Arm.addr_add (by have := space.nowrap; omega)
  unfold VG.Impl.Ffdh.Arm.KeySearch.stf writeLow
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [addr56, arg.readable, arg.word, incomingValue, addr40, addr48,
    space.write (off := 40) (by decide), space.write (off := 48) (by decide), x, y]

theorem entryZero_ok (s : State) {p : KeyPublic} (h : EntryContext p s) :
    WP isa (.block [.mov .r3 (.imm 0), VG.Impl.Ffdh.Arm.KeySearch.stf .r3 11]) s fun t =>
      t.mem = s.mem.writeW (off (State.addr p.control) 88) (0#32) ∧ Rest [.r3] s t := by
  refine withRest [.r3] ?_ (by
    intro r hr instr hi
    simp only [instrs, List.mem_cons, List.not_mem_nil, or_false] at hi
    have ne : r ≠ .r3 := by simpa only [List.mem_singleton] using hr
    rcases hi with rfl | rfl <;>
      simp [VG.Impl.Ffdh.Arm.KeySearch.stf, clobbers, dstOf, Ne.symm ne]) (by rfl)
  unfold VG.Impl.Ffdh.Arm.KeySearch.stf
  ffrun [h.controller.addr (by decide : 11 < 16), h.controller.write (by decide : 11 < 16)]
  rfl

end VG.Proof.Ffdh.Arm.KeySearch
