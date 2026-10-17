module

public import VerifiedGarbage.Proof.Bignum.Arm.ExportAdvance
public import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeOut
meta import VerifiedGarbage.Impl.Bignum.Arm.PrecomputeOut
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
