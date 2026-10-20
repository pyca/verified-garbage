module

public import VerifiedGarbage.Impl.Bignum.Arm.PcFn
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Public precomputation arguments saved in the outer frame -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure PcStack (base dst src : BitVec 32) (len k : Nat) (s : State) : Prop where
  nowrap : s.sp.toNat + 16 ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (State.addr s.sp) 16
  separate : Region.Disjoint ⟨State.addr s.sp, 16⟩ ⟨State.addr base, 8 * len⟩
  savedBase : s.mem.readW (State.addr s.sp) 32 = base
  savedOutput : s.mem.readW (off (State.addr s.sp) 4) 32 = dst
  savedInput : s.mem.readW (off (State.addr s.sp) 8) 32 = src
  savedCount : s.mem.readW (off (State.addr s.sp) 12) 32 = BitVec.ofNat 32 k

theorem PcStack.read {base dst src : BitVec 32} {len k d : Nat} {s : State}
    (h : PcStack base dst src len k s) (fit : d + 4 ≤ 16) :
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) d) 4 :=
  CallLay.inRegions_sub h.readable fit (by decide)

theorem PcStack.after_workspace {base dst src : BitVec 32} {len k : Nat} {s t : State} {rs : List Reg}
    (h : PcStack base dst src len k s) (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem)
    (rest : Rest rs s t) : PcStack base dst src len k t := by
  have eq : WorkspaceEq (State.addr s.sp) 16 s.mem t.mem :=
    WorkspaceEq.of_frame (by decide) frame
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.separate)
  refine ⟨by rw [rest.sp]; exact h.nowrap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.readable
  · rw [rest.sp]; exact h.separate
  · rw [rest.sp]
    have keep := eq.word (d := 0) (bits := 32) (by decide)
    simp only [off, BitVec.add_zero] at keep
    exact keep.trans h.savedBase
  · rw [rest.sp, eq.word (d := 4) (bits := 32) (by decide)]; exact h.savedOutput
  · rw [rest.sp, eq.word (d := 8) (bits := 32) (by decide)]; exact h.savedInput
  · rw [rest.sp, eq.word (d := 12) (bits := 32) (by decide)]; exact h.savedCount

theorem pcInputs_ok (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcStack base dst src len k s) :
    WP isa (.block PcFn.inputs) s fun t => t.gpr .r4 = src ∧ t.gpr .r6 = BitVec.ofNat 32 k ∧
      t.mem = s.mem ∧ Rest [.r4, .r6] s t := by
  have nowrap := h.nowrap
  unfold PcFn.inputs
  refine wp_loadStack (a := off (State.addr s.sp) 8) (by decide) (addr_add (by omega)) (h.read (by decide)) fun u j => ?_
  refine wp_loadStack (a := off (State.addr s.sp) 12) (by decide)
    (by rw [j.sp]; exact addr_add (by omega)) (by rw [j.rd, j.wr]; exact h.read (by decide)) fun t l => WP.block_nil ?_
  exact ⟨(l.other .r4 (by decide)).trans (j.gpr.trans h.savedInput),
    by rw [l.gpr, j.mem]; exact h.savedCount, l.mem.trans j.mem,
    (j.rest (by simp)).trans (l.rest (by simp))⟩

theorem pcOutput_ok (s : State) {base dst src : BitVec 32} {len k : Nat}
    (h : PcStack base dst src len k s) :
    WP isa (.block [.ldrSp .r4 4]) s fun t =>
      t.gpr .r4 = dst ∧ t.mem = s.mem ∧ Rest [.r4] s t := by
  refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide)
    (addr_add (by have := h.nowrap; omega)) (h.read (by decide)) fun t j => WP.block_nil ?_
  exact ⟨j.gpr.trans h.savedOutput, j.mem, j.rest (by simp)⟩

end VG.Proof.Bignum.Arm
