module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductCounterState
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeControl
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeCore

/-! Initialize the first nontrivial public comb basis counter. -/
@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

private theorem tableInit_raw (s : State) {base : BitVec 32} {len : Nat}
    (locals : Locals base len s) :
    WP isa (.block [.mov .r3 (.imm 2),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 36]) s fun t =>
      t.mem=s.mem.writeW (off (State.addr s.sp) 36) (2:BitVec 32) ∧ Rest [.r3,.r12] s t := by
  have addr : State.addr (s.sp+BitVec.ofNat 32 36)=off (State.addr s.sp) 36 := addr_add (by have := locals.space.nowrap; omega)
  have write := locals.space.write (off:=36) (by decide)
  refine withRest_all (c:=.block _) [.r3,.r12] ?_ (by rfl) rfl
  unfold VG.Impl.Ffdh.Arm.Domain.st
  ffrun [addr,write,off,BitVec.add_zero]

theorem tableInit_state (s : State) {p : Inputs} {sp : BitVec 32} {E : Nat}
    (h : Core p sp s) (power : Power5 p E s) :
    WP isa (.block [.mov .r3 (.imm 2),.addSp .r12 0,VG.Impl.Ffdh.Arm.Domain.st .r3 36]) s fun t =>
      Core p sp t ∧ Power5 p E t ∧
      t.mem.readW (off (State.addr sp) 36) 32=2 ∧
      Frame [⟨off (State.addr sp) 36,4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (tableInit_raw s h.memory.context.locals) ?_
  rintro t ⟨mem,rest⟩
  have raw : Frame [⟨off (State.addr s.sp) 36,4⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have r : Rest roundClobbers s t := rest.mono (by simp [roundClobbers])
  have next := h.memory.after_control (by simp) raw r ((rest.gpr .r0 (by simp)).trans h.memory.context.ptr)
  refine ⟨h.after_workspace next.1 next.2,power.after_workspace h next.2,?_,?_,r⟩
  · rw [mem,h.memory.fixed,Mem.readW_writeW_self32]
  · rw [←h.memory.fixed]
    exact raw

end VG.Proof.Ffdh.Arm.CombBuilder
