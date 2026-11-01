module

import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductLoad
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProduct
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductStore
import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeProductCounter
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.CombPrecomputeTableState

/-! Shared memory boundaries for the public subset-product loop. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.CombBuilder
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def productWrites (p : Inputs) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,
    ⟨State.addr sp,72⟩,FrameStack.belowA sp 48]

def ProductCount (sp : BitVec 32) (high low : Nat) (s : State) : Prop :=
  s.mem.readW (off (State.addr sp) 36) 32=BitVec.ofNat 32 high ∧
  s.mem.readW (off (State.addr sp) 40) 32=BitVec.ofNat 32 low

theorem product_frame_arithmetic {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem) :
    Frame (productWrites p sp) s.mem t.mem := by
  apply frame.sub
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact ⟨_,by simp [productWrites],fun _ hx => hx⟩
  · rw [h.fixed]
    exact ⟨_,by simp [productWrites],fun _ hx => hx⟩

theorem product_frame_store {p : Inputs} {sp : BitVec 32} {s t : State} {digit : Nat}
    (hd : digit < 32)
    (frame : Frame [⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩] s.mem t.mem) :
    Frame (productWrites p sp) s.mem t.mem := by
  apply frame.sub
  intro r hr
  have eq := List.mem_singleton.mp hr
  subst r
  exact ⟨_,by simp [productWrites],entry_sub p hd⟩


def productBodyWrites (p : Inputs) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,FrameStack.belowA sp 48]

theorem ProductCount.after_frame {p : Inputs} {sp : BitVec 32} {s t : State} {high low : Nat}
    (count : ProductCount sp high low s) (h : Memory p sp s)
    (frame : Frame (productBodyWrites p sp) s.mem t.mem) : ProductCount sp high low t := by
  have frame' : Frame [⟨State.addr p.base,8*p.len⟩,⟨State.addr p.output,bytes p⟩,
      FrameStack.belowA s.sp 48] s.mem t.mem := by simpa only [productBodyWrites,h.fixed] using frame
  constructor
  · rw [←h.fixed,h.controlRead frame' 36 (by decide),h.fixed]
    exact count.1
  · rw [←h.fixed,h.controlRead frame' 40 (by decide),h.fixed]
    exact count.2

theorem product_body_arithmetic {p : Inputs} {sp : BitVec 32} {s t : State}
    (h : Memory p sp s)
    (frame : Frame [⟨State.addr p.base,8*p.len⟩,FrameStack.belowA s.sp 48] s.mem t.mem) :
    Frame (productBodyWrites p sp) s.mem t.mem := by
  apply frame.mono
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · simp [productBodyWrites]
  · simp [productBodyWrites,h.fixed]

theorem product_body_store {p : Inputs} {sp : BitVec 32} {s t : State} {digit : Nat}
    (hd : digit < 32)
    (frame : Frame [⟨off (State.addr p.output) (entryOffset p digit),8*p.w⟩] s.mem t.mem) :
    Frame (productBodyWrites p sp) s.mem t.mem := by
  apply frame.sub
  intro r hr
  have eq := List.mem_singleton.mp hr
  subst r
  exact ⟨_,by simp [productBodyWrites],entry_sub p hd⟩


theorem Memory.controlContextEq {p : Inputs} {sp : BitVec 32} {s t : State} {d : Nat}
    (h : Memory p sp s) (hd : d+4≤72)
    (frame : Frame [⟨off (State.addr sp) d,4⟩] s.mem t.mem) :
    WorkspaceEq (State.addr p.output) (bytes p) s.mem t.mem := by
  apply WorkspaceEq.of_frame (by have := h.output.fits; omega) frame
  intro r hr
  have eq := List.mem_singleton.mp hr
  subst r
  exact h.localSeparate.symm.sub_right (Offset.sub_base _ hd)

end VG.Proof.Ffdh.Arm.CombBuilder
