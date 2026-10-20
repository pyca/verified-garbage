module

public import VerifiedGarbage.Proof.Ffdh.Arm.Frame
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

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
    (s := s) (by change 56 ≤ s.sp.toNat; omega)
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
  omega

theorem entered_octets {s : State} {base src : BitVec 32} {len : Nat} {bs : List Byte}
    (h : Octets base src len bs s) (fit : 128 ≤ s.sp.toNat)
    (separate : (FrameStack.belowA s.sp 128).Disjoint ⟨State.addr src, bs.length⟩) :
    Octets base src len bs (entered s) := by
  refine ⟨h.fits, entered_read h.readable, h.separate, ?_⟩
  have frame := entered_frame s fit
  rw [rsa_bytes_frame frame (by have := h.fits; omega) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact separate.symm.sub_right (saved_sub_reserved s fit))]
  exact h.bytes

theorem saved_separate_locals (s : State) (fit : 128 ≤ s.sp.toNat) :
    (⟨State.addr (pcPushed s).sp, 56⟩ : Region).Disjoint ⟨State.addr (entered s).sp, 72⟩ := by
  have room : (entered s).sp.toNat + 72 < 2 ^ 32 := by rw [entered_nat s fit]; have := s.sp.isLt; omega
  have addr : State.addr (pcPushed s).sp = off (State.addr (entered s).sp) 72 := by
    have same : (pcPushed s).sp = (entered s).sp + BitVec.ofNat 32 72 := (BitVec.sub_add_cancel _ _).symm
    rw [same]
    exact addr_add room
  rw [addr]
  exact Offset.disjoint_base _ (by decide) (by decide)

end VG.Proof.Ffdh.Arm
