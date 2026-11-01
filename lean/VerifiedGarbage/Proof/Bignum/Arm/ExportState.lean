module
public import VerifiedGarbage.Impl.Bignum.Arm.ExportArray
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Workspace invariants preserved by exporting an array -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt wOf Layout)

structure ExportState (base dst : BitVec 32) (len w capacity : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base
  output : s.gpr .r4 = dst
  size : 8 * w ≤ capacity
  fits : dst.toNat + capacity ≤ 2 ^ 32
  write : InRegions s.wr (State.addr dst) capacity
  separate : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr dst, capacity⟩

theorem ExportState.of_mem {s t : State} {base dst : BitVec 32} {len w capacity : Nat} {rs : List Reg}
    (h : ExportState base dst len w capacity s) (mem : t.mem = s.mem)
    (rest : VG.Proof.X25519.Arm.Rest rs s t) (ptr : t.gpr .r0 = base) (output : t.gpr .r4 = dst) :
    ExportState base dst len w capacity t := by
  refine ⟨h.workspace.congr rest.wr, ?_, ?_, ptr, output, h.size, h.fits, ?_, h.separate⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [rest.wr]; exact h.write

theorem exportArray_state (s : State) {base dst : BitVec 32} {len w o capacity : Nat}
    (h : ExportState base dst len w capacity s) (ho : o < 8) (index : s.gpr .r2 = BitVec.ofNat 32 o) :
    WP isa exportArray s (ExportState base dst len w capacity) := by
  have fit := h.fits
  have size := h.size
  have write : InRegions s.wr (State.addr dst) (8 * w) := by
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) h.write (by omega) (by omega)
  have sep := h.separate.sub_right (Region.sub_prefix size)
  refine WP.mono (exportArray_ok s h.workspace h.layout h.width ho (by omega) write sep h.ptr index h.output) ?_
  rintro t ⟨_, frame, ptr, out, rest⟩
  have nowrap := h.workspace.nowrap
  have fits := h.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have eq := WorkspaceEq.of_frame (by omega : 8 * len < 2 ^ 64) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep)
  exact ⟨h.workspace.congr rest.wr, eq.layout h.layout, (eq.width (by omega)).trans h.width,
    ptr, out, h.size, h.fits, by rw [rest.wr]; exact h.write, h.separate⟩

end VG.Proof.Bignum.Arm
