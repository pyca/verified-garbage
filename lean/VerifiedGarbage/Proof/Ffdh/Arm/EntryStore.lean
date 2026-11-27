module

import VerifiedGarbage.Proof.Ffdh.Arm.StoreSlot
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

/-! ### `Ffdh.Arm.Entered`, which the modules that import this one used -/

section

/-! The local and saved-register frames sit inside the ABI's 128-byte reservation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont

theorem entered_sp (s : State) : (entered s).sp = s.sp - BitVec.ofNat 32 128 := by
  change s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 72 = _
  rw [BitVec.sub_sub, ← BitVec.ofNat_add]

theorem entered_nat (s : State) (fit : 128 ≤ s.sp.toNat) :
    (entered s).sp.toNat = s.sp.toNat - 128 := by
  rw [entered_sp, FrameStack.sub_toNat' fit]

theorem entered_frame (s : State) (fit : 128 ≤ s.sp.toNat) :
    Frame [⟨State.addr (pcPushed s).sp, 56⟩] s.mem (entered s).mem := by
  have f := FrameStack.pushed_frameA
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := s) (by change 56 ≤ s.sp.toNat; omega_using [fit])
  exact f

theorem entered_read {s : State} {a : Addr} {n : Nat} (read : InRegions (s.rd ++ s.wr) a n) :
    InRegions ((entered s).rd ++ (entered s).wr) a n := by
  obtain ⟨r, hr, contains⟩ := read
  refine ⟨r, ?_, contains⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact List.mem_append_left _ hr
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem entered_workspace {s : State} {base : BitVec 32} {size : Nat} (h : Workspace s base size) :
    Workspace (entered s) base size :=
  ⟨h.nowrap, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h.writable)⟩

theorem locals_sub_reserved (s : State) (fit : 128 ≤ s.sp.toNat) :
    Region.Sub ⟨State.addr (entered s).sp, 72⟩ (FrameStack.belowA s.sp 128) :=
  FrameStack.belowA_inner (a := 72) (k := 56) (by decide) fit

theorem saved_sub_reserved (s : State) (fit : 128 ≤ s.sp.toNat) :
    Region.Sub ⟨State.addr (pcPushed s).sp, 56⟩ (FrameStack.belowA s.sp 128) :=
  FrameStack.belowA_sub (by decide) fit

theorem entered_locals (s : State) {base : BitVec 32} {len : Nat} (fit : 128 ≤ s.sp.toNat)
    (separate : (FrameStack.belowA s.sp 128).Disjoint ⟨State.addr base, 8 * len⟩) :
    Locals base len (entered s) := by
  refine ⟨⟨?_, List.mem_cons_self⟩, separate.sub_left (locals_sub_reserved s fit)⟩
  rw [entered_nat s fit]
  have := s.sp.isLt
  omega_using []

theorem entered_octets {s : State} {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (h : Octets base src len bs s) (fit : 128 ≤ s.sp.toNat)
    (separate : (FrameStack.belowA s.sp 128).Disjoint ⟨State.addr src, bs.length⟩) :
    Octets base src len bs (entered s) := by
  refine ⟨h.fits, entered_read h.readable, h.separate, ?_⟩
  have frame := entered_frame s fit
  rw [rsa_bytes_frame frame (by have := h.fits; omega_using [this]) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact separate.symm.sub_right (saved_sub_reserved s fit))]
  exact h.bytes

theorem saved_separate_locals (s : State) (fit : 128 ≤ s.sp.toNat) :
    (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint ⟨State.addr (entered s).sp, 72⟩ := by
  have room : (entered s).sp.toNat + 72 < 2 ^ 32 := by rw [entered_nat s fit]; have := s.sp.isLt; omega_using []
  have addr : State.addr (pcPushed s).sp = off (State.addr (entered s).sp) 72 := by
    have same : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
    rw [same]
    exact addr_add room
  rw [addr]
  exact Offset.disjoint_base _ (by decide) (by decide)

end VG.Proof.Ffdh.Arm

end

end

/-! Argument stores can precede installing the workspace pointer in r0. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem ArgumentMemory.of_mem {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    (h : ArgumentMemory p slots s) (mem : t.mem = s.mem) (rest : Rest rs s t) : ArgumentMemory p slots t := by
  have frame : Frame [] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact h.after_frame frame rest (by simp) (by simp)

theorem wp_store_arg {s : State} {p : Inputs} {slots : List Nat} {is : List Instr} {Q : State → Prop}
    (r : Reg) (d : Nat) (h : ArgumentMemory p slots s) (stable : stableSlots slots = true)
    (aligned : d % 4 = 0) (fit : d + 4 ≤ 72) (source : s.gpr r = p.slotValue d)
    (stackBase : s.gpr .r12 = s.sp)
    (next : ∀ t, ArgumentMemory p (d :: slots) t →
      Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem → Rest [] s t → WP isa (.block is) t Q) :
    WP isa (.block (.str r .r12 d :: is)) s Q := by
  refine wp_str (a := off (State.addr s.sp) d) (by omega_using [fit])
    (by rw [stackBase]; exact addr_add (by have := h.locals.space.nowrap; omega_using [fit, this]))
    (h.locals.space.write fit) fun t stored => ?_
  have mem : t.mem = s.mem.writeW (off (State.addr s.sp) d) (p.slotValue d) := by rw [stored.mem, source]
  have rest := stored.rest []
  have args := h.store_slot stable d aligned fit mem rest
  apply next t args _ rest
  rw [mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ fit (by omega_using [fit]))

structure IncomingScratch (p : Inputs) (s : State) : Prop where
  fits : s.sp.toNat + 136 ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 132) 4
  value : s.mem.readW (off (State.addr s.sp) 132) 32 = p.base

theorem IncomingScratch.after {p : Inputs} {s t : State} {rs : List Reg} (h : IncomingScratch p s)
    (frame : Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem) (rest : Rest rs s t) : IncomingScratch p t := by
  refine ⟨by rw [rest.sp]; exact h.fits, ?_, ?_⟩
  · rw [rest.rd, rest.wr, rest.sp]; exact h.readable
  · rw [rest.sp]
    have word := frame.readW (w := 32) (r := ⟨off (State.addr s.sp) 132, 4⟩) (Region.contains_self _ _)
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact Offset.disjoint_base _ (by decide) (by decide)) (by decide)
    exact word.trans h.value

end VG.Proof.Ffdh.Arm
