module

public import VerifiedGarbage.Proof.Bignum.Arm.PdImport
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayCT
import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.Arm.PdImport
meta import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayCT
meta import VerifiedGarbage.Proof.Bignum.Arm.ImportArrayLayout
meta import VerifiedGarbage.Proof.Bignum.Arm.LayoutFrameReady
meta import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOutArgs
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Reading the public precomputation has only public addresses and counts -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

theorem pdImport_first_ok (s : State) {base pp : BitVec 32} {len w : Nat}
    (h : PdImportInput base pp len w s) :
    WP isa (.seq (.block [.mov .r2 (.imm 0)]) importArray) s (PdImportInput base pp len w) := by
  rw [WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun u moved => WP.block_nil ?_
  have ready := h.ready.of_mem moved.mem (moved.rest (by simp : Reg.r2 ∈ [.r2]))
    ((moved.other .r0 (by decide)).trans h.ready.ptr)
  have sourceFit := h.sourceFit
  have read : InRegions (u.rd ++ u.wr) (State.addr pp) (8 * w) := by
    rw [moved.rd, moved.wr]
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub (off := 0) h.read (by omega) (by omega)
  refine WP.mono (importArrayLayout_ok u ready (by decide : 0 < 8)
    (by have := h.sourceFit; omega) read (h.separate.sub_right (Region.sub_prefix (by omega)))
    moved.gpr ((moved.other .r4 (by decide)).trans h.source)) ?_
  rintro t ⟨readyT, _, _, _, rest, source⟩
  exact ⟨readyT, h.sourceFit, by rw [rest.rd, rest.wr, moved.rd, moved.wr]; exact h.read,
    h.separate, source⟩

theorem pdImport_ct {base pp : BitVec 32} {len w : Nat} :
    RelCT isa (fun s t => PdImportInput base pp len w s ∧ PdImportInput base pp len w t)
      pdImport (fun _ _ => True) := by
  let P := PdImportInput base pp len w
  let Q := fun s : State => SmallFnReady base len w 0 s ∧ s.gpr .r4 = pp
  have args : RelCT isa (fun s t => P s ∧ P t) (.block [.mov .r2 (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have wpArgs (s : State) (h : P s) : WP isa (.block [.mov .r2 (.imm 0)]) s Q := by
    refine wp_mov (op2_imm (by decide)) fun t moved => WP.block_nil ?_
    exact ⟨⟨h.ready.workspace.congr moved.wr, by rw [moved.mem]; exact h.ready.layout,
      by rw [moved.mem]; exact h.ready.width, (moved.other .r0 (by decide)).trans h.ready.ptr, moved.gpr⟩,
      (moved.other .r4 (by decide)).trans h.source⟩
  have first := ((pair_posts args wpArgs).seq ((importArray_ct (by decide : 0 < 8)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩) (fun _ _ h => h))).wp
    (fun s t h => ⟨pdImport_first_ok s h.1, pdImport_first_ok t h.2⟩)
  let R := fun s : State => SmallFnReady base len w 4 s ∧ s.gpr .r4 = pp + BitVec.ofNat 32 (8 * w)
  have advance : RelCT isa (fun s t => P s ∧ P t) (.block precomputeOutAdvance) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
    intro s t h
    apply Taint.agree_ofRegs
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h.1.ready.ptr.trans h.2.ready.ptr.symm
  have wpAdvance (s : State) (h : P s) : WP isa (.block precomputeOutAdvance) s R := by
    have fits := h.ready.layout.2.2.1
    have size : 52 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
    have header := nativeHeader_of_layout s.mem base h.ready.workspace.nowrap (Nat.le_refl _) h.ready.layout
    rw [h.ready.width] at header
    refine WP.mono (precomputeOutAdvance_ok s h.ready.workspace size h.ready.ptr header.count) ?_
    rintro t ⟨source, index, mem, rest⟩
    exact ⟨⟨h.ready.workspace.congr rest.wr, by rw [mem]; exact h.ready.layout,
      by rw [mem]; exact h.ready.width, (rest.gpr .r0 (by simp)).trans h.ready.ptr, index⟩,
      by rw [source, h.source]⟩
  have second := (pair_posts advance wpAdvance).seq ((importArray_ct (by decide : 4 < 8)).mono
    (fun _ _ h => ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩) (fun _ _ h => h))
  exact ((first.seq (second.mono (fun _ _ h => h.2) (fun _ _ h => h))).assoc)

end VG.Proof.Bignum.Arm
