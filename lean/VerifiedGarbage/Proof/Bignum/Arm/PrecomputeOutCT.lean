module

public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut
import VerifiedGarbage.Proof.Bignum.Arm.StageCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut
meta import VerifiedGarbage.Proof.Bignum.Arm.StageCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Impl.Bignum.Arm.ExportArray
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFnCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Bignum.Arm.ExportArrayCT
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Impl.Bignum.Arm.ExportArray
meta import VerifiedGarbage.Proof.Bignum.Arm.Workspace
meta import VerifiedGarbage.Proof.Rsa.MontContract
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
meta import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
meta import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Bignum.Arm.ExportAdvance`, which this module and modules that import it used -/

section

/-! ### `Bignum.Arm.ExportState`, which this module and modules that import it used -/

section

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
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) h.write (by omega_using [size]) (by omega_using [fit])
  have sep := h.separate.sub_right (Region.sub_prefix size)
  refine WP.mono (exportArray_ok s h.workspace h.layout h.width ho (by omega_using [fit, size]) write sep h.ptr index h.output) ?_
  rintro t ⟨_, frame, ptr, out, rest⟩
  have nowrap := h.workspace.nowrap
  have fits := h.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have eq := WorkspaceEq.of_frame (by omega_using [nowrap] : 8 * len < 2 ^ 64) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact sep)
  exact ⟨h.workspace.congr rest.wr, eq.layout h.layout, (eq.width (by omega_using [size])).trans h.width,
    ptr, out, h.size, h.fits, by rw [rest.wr]; exact h.write, h.separate⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Move to the second half of the RSA precomputation output -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/ExportStateCT.lean`, which only this module imported.
section

/-! # Array export preserves the public state needed by the next export -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

def IndexedExport (base dst : BitVec 32) (len w capacity o : Nat) (s : State) : Prop :=
  ExportState base dst len w capacity s ∧ s.gpr .r2 = BitVec.ofNat 32 o

theorem IndexedExport.small {base dst : BitVec 32} {len w capacity o : Nat} {s : State}
    (h : IndexedExport base dst len w capacity o s) : SmallFnReady base len w o s :=
  ⟨h.1.workspace, h.1.layout, h.1.width, h.1.ptr, h.2⟩

theorem exportArray_indexed_ct {base dst : BitVec 32} {len w capacity o : Nat} (ho : o < 8) :
    RelCT isa (fun s t => IndexedExport base dst len w capacity o s ∧ IndexedExport base dst len w capacity o t)
      exportArray (fun s t => ExportState base dst len w capacity s ∧ ExportState base dst len w capacity t) := by
  have ct := (exportArray_ct (base := base) (dst := dst) (len := len) (w := w) ho).mono
    (P' := fun s t => IndexedExport base dst len w capacity o s ∧ IndexedExport base dst len w capacity o t)
    (fun _ _ h => ⟨h.1.small, h.2.small, h.1.1.output, h.2.1.output⟩)
    (fun _ _ h => h)
  exact (ct.wp (fun s t h => ⟨exportArray_state s h.1.1 ho h.1.2,
    exportArray_state t h.2.1 ho h.2.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)

end VG.Proof.Bignum.Arm
end

end

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt)

theorem exportAdvance_ready (s : State) {base dst : BitVec 32} {len w : Nat}
    (h : ExportState base dst len w (16 * w) s) :
    WP isa (.block precomputeOutAdvance) s
      (IndexedExport base (dst + BitVec.ofNat 32 (8 * w)) len w (8 * w) 4) := by
  have fits := h.layout.2.2.1
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have dstFit := h.fits
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  refine WP.mono (precomputeOutAdvance_ok s h.workspace (by omega_using [size]) h.ptr header.count) ?_
  rintro t ⟨output, index, mem, rest⟩
  have addr : State.addr (dst + BitVec.ofNat 32 (8 * w)) = off (State.addr dst) (8 * w) := addr_add (by omega_using [dstFit])
  have val : (dst + BitVec.ofNat 32 (8 * w)).toNat = dst.toNat + 8 * w := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [dstFit] : 8 * w < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [dstFit] : dst.toNat + 8 * w < 2 ^ 32)]
  refine ⟨⟨h.workspace.congr rest.wr, ?_, ?_, (rest.gpr .r0 (by simp)).trans h.ptr,
    by rw [output, h.output], by omega_using [], by rw [val]; omega_using [dstFit], ?_, ?_⟩, index⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · rw [rest.wr, addr]; exact CallLay.inRegions_sub h.write (by omega_using []) (by omega_using [dstFit])
  · rw [addr]; exact h.separate.sub_right (Offset.sub_base _ (by omega_using []))

end VG.Proof.Bignum.Arm

end

end

/-! # Serializing RSA precomputation has a public execution trace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (wp_mov op2_imm)

theorem precomputeOut_ct {base dst : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => ExportState base dst len w (16 * w) s ∧ ExportState base dst len w (16 * w) t)
      precomputeOut (fun _ _ => True) := by
  let P := ExportState base dst len w (16 * w)
  have init : RelCT isa (fun s t => P s ∧ P t) (.block [.mov .r2 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wp (s : State) (h : P s) :
      WP isa (.block [.mov .r2 (.imm 0)]) s (IndexedExport base dst len w (16 * w) 0) := by
    refine wp_mov (op2_imm (by decide)) fun u moved => WP.block_nil ?_
    exact ⟨h.of_mem moved.mem (moved.rest (ws := [.r2]) (by simp))
      ((moved.other .r0 (by decide)).trans h.ptr) ((moved.other .r4 (by decide)).trans h.output), moved.gpr⟩
  have advance : RelCT isa (fun s t => P s ∧ P t) (.block precomputeOutAdvance) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ptr.trans h.2.ptr.symm
  have advanceReady := pair_posts advance (fun s h => exportAdvance_ready s h)
  have finish : RelCT isa
      (fun s t => ExportState base (dst + BitVec.ofNat 32 (8 * w)) len w (8 * w) s ∧
        ExportState base (dst + BitVec.ofNat 32 (8 * w)) len w (8 * w) t)
      (.block [.mov .r0 (.imm 1)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  exact (pair_posts init wp).seq ((exportArray_indexed_ct (by decide)).seq
    (advanceReady.seq ((exportArray_indexed_ct (by decide)).seq finish)))

end VG.Proof.Bignum.Arm
