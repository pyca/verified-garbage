module

public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Framework.Offset

/-! Saved public scalar geometry while entropy cutting advances the output pointer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure SampleMemory (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (s : State)
    extends ArgumentMemory p slots s where
  scalarStart : s.mem.readW (off (State.addr s.sp) 16) 32 = l.start
  scalarWidth : s.mem.readW (off (State.addr s.sp) 20) 32 = BitVec.ofNat 32 l.width
  scalarMask : s.mem.readW (off (State.addr s.sp) 68) 32 = l.mask

theorem SampleContext.toSampleMemory {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {s : State}
    (h : SampleContext p l slots s) : SampleMemory p l slots s :=
  ⟨h.toContext.toArgumentMemory, h.scalarStart, h.scalarWidth, h.scalarMask⟩

theorem SampleMemory.withPtr {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {s : State}
    (h : SampleMemory p l slots s) (ptr : s.gpr .r0 = p.base) : SampleContext p l slots s :=
  ⟨⟨h.toArgumentMemory, ptr⟩, h.scalarStart, h.scalarWidth, h.scalarMask⟩

theorem SampleMemory.after_output {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    {s t : State} {rs : List Reg} {dst : BitVec 32} {n : Nat}
    (h : SampleMemory p l slots s) (frame : Frame [⟨State.addr dst, n⟩] s.mem t.mem)
    (rest : Rest rs s t)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr dst, n⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr dst, n⟩)
    (saved : ∀ d ∈ slots, d + 4 ≤ 72) : SampleMemory p l slots t := by
  have keep (d : Nat) (hd : d + 4 ≤ 72) :
      t.mem.readW (off (State.addr t.sp) d) 32 = s.mem.readW (off (State.addr s.sp) d) 32 := by
    rw [rest.sp]
    exact frame.readW (Region.contains_self _ _)
      (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact stackSep.sub_left (Offset.sub_base _ hd))
      (by decide)
  exact ⟨h.toArgumentMemory.after_output frame rest domainSep stackSep saved,
    (keep 16 (by decide)).trans h.scalarStart, (keep 20 (by decide)).trans h.scalarWidth,
    (keep 68 (by decide)).trans h.scalarMask⟩


theorem SampleMemory.after_workspace {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    {s t : State} {rs : List Reg} (h : SampleMemory p l slots s)
    (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem) (rest : Rest rs s t)
    (fit : ∀ d ∈ slots, d + 4 ≤ 72) : SampleMemory p l slots t := by
  have keep (d : Nat) (hd : d + 4 ≤ 72) :
      t.mem.readW (off (State.addr t.sp) d) 32 = s.mem.readW (off (State.addr s.sp) d) 32 := by
    rw [rest.sp]
    exact frame.readW (Region.contains_self _ _)
      (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact h.locals.separate.sub_left (Offset.sub_base _ hd))
      (by decide)
  exact ⟨h.toArgumentMemory.after_workspace frame rest fit,
    (keep 16 (by decide)).trans h.scalarStart, (keep 20 (by decide)).trans h.scalarWidth,
    (keep 68 (by decide)).trans h.scalarMask⟩

theorem SampleContext.after_workspace {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    {s t : State} {rs : List Reg} (h : SampleContext p l slots s)
    (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = p.base) (fit : ∀ d ∈ slots, d + 4 ≤ 72) : SampleContext p l slots t :=
  (h.toSampleMemory.after_workspace frame rest fit).withPtr ptr

end VG.Proof.Ffdh.Arm
