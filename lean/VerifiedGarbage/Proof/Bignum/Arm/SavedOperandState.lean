module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Stable frame slots and source bytes for private-key imports -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure SavedOperand (base src : BitVec 32) (len k pointerSlot countSlot : Nat) (bs : List Byte) (s : State) : Prop where
  nowrap : s.sp.toNat + 112 ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) pointerSlot) 4 ∧
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) countSlot) 4
  stackSeparate : Region.Disjoint ⟨State.addr s.sp, 112⟩ ⟨State.addr base, 8 * len⟩
  pointerFit : pointerSlot + 4 ≤ 112
  countFit : countSlot + 4 ≤ 112
  pointer : s.mem.readW (off (State.addr s.sp) pointerSlot) 32 = src
  count : s.mem.readW (off (State.addr s.sp) countSlot) 32 = BitVec.ofNat 32 k
  source : PublicBytes src k bs s
  sourceSeparate : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr base, 8 * len⟩

theorem SavedOperand.after_frame {s t : State} {base src : BitVec 32}
    {len k ps cs : Nat} {bs : List Byte} {rs : List Reg} {regions : List Region} (h : SavedOperand base src len k ps cs bs s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (stackSep : ∀ r ∈ regions, (⟨State.addr s.sp, 112⟩ : Region).Disjoint r)
    (sourceSep : ∀ r ∈ regions, (⟨State.addr src, k⟩ : Region).Disjoint r) :
    SavedOperand base src len k ps cs bs t := by
  have eq : WorkspaceEq (State.addr s.sp) 112 s.mem t.mem := WorkspaceEq.of_frame (by decide) frame
    stackSep
  refine ⟨by rw [rest.sp]; exact h.nowrap,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.readable,
    by rw [rest.sp]; exact h.stackSeparate, h.pointerFit, h.countFit, ?_, ?_,
    h.source.after_frame frame rest
      sourceSep, h.sourceSeparate⟩
  · rw [rest.sp, eq.word (d := ps) (bits := 32) h.pointerFit]; exact h.pointer
  · rw [rest.sp, eq.word (d := cs) (bits := 32) h.countFit]; exact h.count

theorem SavedOperand.after_workspace {s t : State} {base src : BitVec 32}
    {len k ps cs : Nat} {bs : List Byte} {rs : List Reg} (h : SavedOperand base src len k ps cs bs s)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem) (rest : Rest rs s t) :
    SavedOperand base src len k ps cs bs t := by
  have eq : WorkspaceEq (State.addr s.sp) 112 s.mem t.mem := WorkspaceEq.of_frame (by decide) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.stackSeparate)
  refine ⟨by rw [rest.sp]; exact h.nowrap,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.readable,
    by rw [rest.sp]; exact h.stackSeparate, h.pointerFit, h.countFit, ?_, ?_,
    h.source.after_frame frame rest
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sourceSeparate), h.sourceSeparate⟩
  · rw [rest.sp, eq.word (d := ps) (bits := 32) h.pointerFit]; exact h.pointer
  · rw [rest.sp, eq.word (d := cs) (bits := 32) h.countFit]; exact h.count

end VG.Proof.Bignum.Arm
