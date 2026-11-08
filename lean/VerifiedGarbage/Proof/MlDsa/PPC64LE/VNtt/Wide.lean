module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Table
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.VNtt.Mem
public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run

/-! # ML-DSA's vector NTT on PPC64LE: the layers of `len ≥ 4` -/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.VNtt

open VG VG.PPC64LE VG.Impl.MlDsa.PPC64LE.VNtt

/-! ## One step -/

theorem loads_run (s : State) {x y : Addr} (h5 : s.gpr .r5 = x) (h9 : s.gpr .r9 = 0#64) (h8 : s.gpr .r8 = y)
    (ia : InRegions (s.rd ++ s.wr) x 16) (ib : InRegions (s.rd ++ s.wr) (x + y) 16) :
    WP isa (.block [.lxvd2x .v0 .r5 .r9, .lxvd2x .v1 .r5 .r8]) s fun t =>
      t = (s.writeV .v0 (swapDwords (s.mem.read x 16))).writeV .v1 (swapDwords (s.mem.read (x + y) 16)) := by
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v0 .r5 .r9 s (by decide) (by rw [h5, h9, BitVec.add_zero]; exact ia), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_lxvd2x .v1 .r5 .r8 _ (by decide) (by
    simp only [gpr_writeV, rd_writeV, wr_writeV, h5, h8]; exact ib), ?_⟩
  refine WP.block_nil ?_
  simp only [gpr_writeV, mem_writeV, h5, h8, h9, BitVec.add_zero]

theorem stores_run (s : State) {x y : Addr} (h5 : s.gpr .r5 = x) (h9 : s.gpr .r9 = 0#64) (h8 : s.gpr .r8 = y)
    (oa : InRegions s.wr x 16) (ob : InRegions s.wr (x + y) 16) :
    WP isa (.block [.stxvd2x .v0 .r5 .r9, .stxvd2x .v1 .r5 .r8, .addi .r5 .r5 16, .subi .r10 .r10 1]) s fun t =>
      t.mem = (s.mem.write x 16 (swapDwords (s.vpr .v0))).write (x + y) 16 (swapDwords (s.vpr .v1)) ∧
      t.gpr .r5 = x + 16 ∧ t.gpr .r10 = s.gpr .r10 - 1 ∧
      (∀ r, r ≠ .r5 → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.vpr = s.vpr ∧ t.syms = s.syms ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.lr = s.lr := by
  refine WP.block_cons_iff.2 ⟨_, exec_stxvd2x .v0 .r5 .r9 s (by decide) (by rw [h5, h9, BitVec.add_zero]; exact oa), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, exec_stxvd2x .v1 .r5 .r8 _ (by decide) (by simp only [h5, h8]; exact ob), ?_⟩
  crun [h5, h8, h9]
  intro r h1 h2
  simp [h1, h2]

end VG.Proof.MlDsa.PPC64LE.VNtt
