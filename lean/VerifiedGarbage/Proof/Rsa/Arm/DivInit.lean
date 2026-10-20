module

public import VerifiedGarbage.Proof.Rsa.Arm.DivReduce
import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Rsa.Arm.DivArgs
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Division starts from a zero remainder and a public bit count -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

theorem initCount_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (.block [.ldr .r6 .r8 16, .mov .r6 (.shifted .r6 .lsl 5)]) s fun t =>
      t.gpr .r6 = BitVec.ofNat 32 (32 * g.n) ∧ t.mem = s.mem ∧
      Context g t ∧ Rest [.r6] s t := by
  refine h.loadCount (by decide) fun u a hu => ?_
  refine wp_mov (op2_lsl (by decide)) fun t b => WP.block_nil ?_
  refine ⟨?_, b.mem.trans a.mem, hu.of_update b (by decide),
    (a.rest (by simp)).trans (b.rest (by simp))⟩
  rw [b.gpr, a.gpr, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 32 g.n * BitVec.ofNat 32 32 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm]

theorem clear_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa (.seq (.block (remainderArgs ++ ([.mov .r3 (.imm 0)] : List Instr))) VG.Impl.Bignum.Arm.zero)
      s (Context g) := by
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (remainderArgs_ok h) ?_
  rintro u ⟨ptr, count, _, ctxU, _⟩
  refine wp_mov (op2_imm (by decide)) fun v upd => WP.block_nil ?_
  have ctxV := ctxU.of_update upd (by decide)
  have zeroCtx : ZeroCtx v g.base g.size (g.offsets 1) (g.n + 1) :=
    ⟨h.workspace.nowrap, h.fits 1, ⟨_, ctxV.workspace.writable, Region.contains_self _ _⟩⟩
  refine WP.mono (zero_ok v zeroCtx (by omega)
    ((upd.other .r0 (by decide)).trans ptr) ((upd.other .lr (by decide)).trans count) upd.gpr) ?_
  intro z inv
  exact ctxV.after (Outs.of_outside inv.outside (by simp [Geometry.ranges]))
    inv.rest.wr (inv.rest.gpr .r8 (by simp))

theorem init_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa init s fun t =>
      g.value t.mem 1 = 0 ∧ g.value t.mem 0 = g.value s.mem 0 ∧
      t.gpr .r6 = BitVec.ofNat 32 (32 * g.n) ∧ Context g t ∧
      Outs (State.addr g.base) g.ranges s.mem t.mem ∧ Rest (.r6 :: clobbers) s t := by
  rw [init, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (remainderArgs_ok h) ?_
  rintro u ⟨ptr, count, memU, ctxU, restU⟩
  refine wp_mov (op2_imm (by decide)) fun v upd => WP.block_nil ?_
  have ctxV := ctxU.of_update upd (by decide)
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have zeroCtx : ZeroCtx v g.base g.size (g.offsets 1) (g.n + 1) :=
    ⟨h.workspace.nowrap, f1, ⟨_, ctxV.workspace.writable, Region.contains_self _ _⟩⟩
  rw [WP.seq_iff]
  refine WP.mono (zero_ok v zeroCtx (by omega)
    ((upd.other .r0 (by decide)).trans ptr) ((upd.other .lr (by decide)).trans count) upd.gpr) ?_
  intro z inv
  have frame : Outs (State.addr g.base) g.ranges v.mem z.mem :=
    Outs.of_outside inv.outside (by simp [Geometry.ranges])
  have ctxZ := ctxV.after frame inv.rest.wr (inv.rest.gpr .r8 (by simp))
  refine WP.mono (initCount_ok ctxZ) ?_
  rintro t ⟨cnt, memT, ctxT, restT⟩
  refine ⟨by change val32 _ _ _ (g.n + 1) = 0; rw [memT]; exact inv.value,
    ?_, cnt, ctxT, ?_, ?_⟩
  · have sep : g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
        g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 := h.separate 0 1 (by decide)
    have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
    have nowrap := h.workspace.nowrap
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    rw [memT, inv.outside.val32 sep (by omega), upd.mem, memU]
  · rw [memT, ← memU, ← upd.mem]; exact frame
  · exact (restU.mono (by simp [clobbers])).trans ((upd.rest (by simp [clobbers])).trans
      ((inv.rest.mono (by simp [clobbers])).trans (restT.mono (by simp))))

end VG.Proof.Rsa.Arm.Div
