module

public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Rc2.Arm.Stream.Common
meta import VerifiedGarbage.Proof.Rc2.Arm.Stream.Common
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Rc2.PairMem
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Rc2.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Rc2.PairMem
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Rc2.CbcMemory
meta import VerifiedGarbage.Proof.Rc2.Stream
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Rc2.Arm.Lit

@[expose] public section

section

section

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init`

The checks of the lengths (`checks_ok`), then, if they pass, the IV copied to
`ctx + 128` and `lr` saved (`args_ok`), the call of `vg_rc2_expand_key`
(`key_call`), and `lr` restored with 0 returned (`tail_ok`). -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_sub wp_cmp wp_ldr wp_str
  wp_ldrSp eval_ne sub_beq)

theorem range7 (x : BitVec 32) :
    ((x - 1) >>> 7 - 0 == 0) = decide (1 ≤ x.toNat ∧ x.toNat ≤ 128) := by
  rw [show ((x - 1) >>> 7 - 0 : BitVec 32) = (x - 1) >>> 7 from BitVec.sub_zero _]
  have e : ((x - 1) >>> 7).toNat = (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 128 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]; rfl
  have h := x.isLt
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, show (0 : BitVec 32).toNat = 0 from rfl]
  omega_arith

theorem range10 (x : BitVec 32) :
    ((x - 1) >>> 10 - 0 == 0) = decide (1 ≤ x.toNat ∧ x.toNat ≤ 1024) := by
  rw [show ((x - 1) >>> 10 - 0 : BitVec 32) = (x - 1) >>> 10 from BitVec.sub_zero _]
  have e : ((x - 1) >>> 10).toNat = (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 1024 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]; rfl
  have h := x.isLt
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, show (0 : BitVec 32).toNat = 0 from rfl]
  omega_arith

theorem eq8 (x : BitVec 32) : (x - 8 == 0) = decide (x.toNat = 8) := by
  rw [ofNat_toNat32 x, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, sub_beq x.isLt (by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem setWidth_append (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt this]
  omega_arith

theorem wp_mov_imm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (he : encodable v = true) (k : WP isa (.block is) (s.setReg d v) Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (by simp [exec, Op2.eval, he]) k

/-- The lengths are valid. -/
abbrev IValid (s : State) : Prop :=
  (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) ∧ (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) ∧
    (stackArg s 0).toNat = 8

/-- The error code for invalid lengths. -/
abbrev ICode (s : State) : Nat :=
  if ¬(1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) then 1
  else if ¬(1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) then 2 else 3

/-- What the checks leave. -/
structure CheckPost (s c : State) : Prop where
  keep : ∀ r, r ≠ .r0 → r ≠ .r12 → c.gpr r = s.gpr r
  mem : c.mem = s.mem
  rd : c.rd = s.rd
  wr : c.wr = s.wr
  sp : c.sp = s.sp
  z : c.z = decide (IValid s)
  ok : IValid s → c.gpr .r0 = s.gpr .r0
  err : ¬ IValid s → (c.gpr .r0).toNat = ICode s

theorem checks_ok (s : State) (hs : initContract.pre s) : WP isa checks s (CheckPost s) := by
  obtain ⟨_, spfit, hrd, _⟩ := hs
  rw [checks]
  refine WP.seq (wp_sub (op2_imm (by decide)) fun c₁ u₁ => wp_mov (op2_lsr (by decide)) fun c₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun c₃ f₃ z₃ => WP.block_nil ?_)
  have hk : c₃.z = decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) := by
    rw [z₃, u₂.gpr, u₁.gpr, range7]
  have g₃ (r : Reg) (h : r ≠ .r12) : c₃.gpr r = s.gpr r := by rw [f₃.gpr, u₂.other _ h, u₁.other _ h]
  have mem₃ : c₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have rd₃ : c₃.rd = s.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
  have wr₃ : c₃.wr = s.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
  have sp₃ : c₃.sp = s.sp := by rw [f₃.sp, u₂.sp, u₁.sp]
  refine WP.ite (!decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128))
    (by show eval .ne c₃ = _; rw [eval_ne, hk]) (fun hb => wp_mov_imm (by decide) (WP.block_nil ?_)) fun hb => ?_
  · have hb : ¬(1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) := fun h => by simp [h] at hb
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₃ r h12], by rw [mem_setReg, mem₃],
      by rw [rd_setReg, rd₃], by rw [wr_setReg, wr₃], by rw [sp_setReg, sp₃], ?_, fun h => absurd h.1 hb,
      fun _ => ?_⟩
    · rw [z_setReg, hk]; simp only [IValid, hb, false_and, decide_false]
    · rw [gpr_setReg_self]; simp only [ICode, hb, not_false_eq_true, ite_true]; rfl
  have hb : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128 := by simpa using hb
  refine WP.seq (wp_sub (op2_imm (by decide)) fun c₄ u₄ => wp_mov (op2_lsr (by decide)) fun c₅ u₅ =>
    wp_cmp (op2_imm (by decide)) fun c₆ f₆ z₆ => WP.block_nil ?_)
  have he : c₆.z = decide (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) := by
    rw [z₆, u₅.gpr, u₄.gpr, g₃ _ (by decide), range10]
  have g₆ (r : Reg) (h : r ≠ .r12) : c₆.gpr r = s.gpr r := by rw [f₆.gpr, u₅.other _ h, u₄.other _ h, g₃ r h]
  have mem₆ : c₆.mem = s.mem := by rw [f₆.mem, u₅.mem, u₄.mem, mem₃]
  have rd₆ : c₆.rd = s.rd := by rw [f₆.rd, u₅.rd, u₄.rd, rd₃]
  have wr₆ : c₆.wr = s.wr := by rw [f₆.wr, u₅.wr, u₄.wr, wr₃]
  have sp₆ : c₆.sp = s.sp := by rw [f₆.sp, u₅.sp, u₄.sp, sp₃]
  refine WP.ite (!decide (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024))
    (by show eval .ne c₆ = _; rw [eval_ne, he]) (fun hb' => wp_mov_imm (by decide) (WP.block_nil ?_)) fun hb' => ?_
  · have hb' : ¬(1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) := fun h => by simp [h] at hb'
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₆ r h12], by rw [mem_setReg, mem₆],
      by rw [rd_setReg, rd₆], by rw [wr_setReg, wr₆], by rw [sp_setReg, sp₆], ?_, fun h => absurd h.2.1 hb',
      fun _ => ?_⟩
    · rw [z_setReg, he]; simp only [IValid, hb', false_and, and_false, decide_false]
    · rw [gpr_setReg_self]; simp only [ICode, hb, hb', not_false_eq_true, ite_true]
      rfl
  have hb' : 1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024 := by simpa using hb'
  rw [show checkIv = [.ldrSp .r12 0, .cmp .r12 (.imm 8)] from rfl]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [sp₆]; rfl)
    (by rw [rd₆, wr₆]; exact argIn (by rw [hrd]; simp) (by decide) spfit) fun c₇ u₇ =>
      wp_cmp (op2_imm (by decide)) fun c₈ f₈ z₈ => WP.block_nil ?_)
  have hi : c₈.z = decide ((stackArg s 0).toNat = 8) := by
    rw [z₈, u₇.gpr, mem₆, eq8]; rfl
  have g₈ (r : Reg) (h : r ≠ .r12) : c₈.gpr r = s.gpr r := by rw [f₈.gpr, u₇.other _ h, g₆ r h]
  have mem₈ : c₈.mem = s.mem := by rw [f₈.mem, u₇.mem, mem₆]
  have rd₈ : c₈.rd = s.rd := by rw [f₈.rd, u₇.rd, rd₆]
  have wr₈ : c₈.wr = s.wr := by rw [f₈.wr, u₇.wr, wr₆]
  have sp₈ : c₈.sp = s.sp := by rw [f₈.sp, u₇.sp, sp₆]
  refine WP.ite (!decide ((stackArg s 0).toNat = 8))
    (by show eval .ne c₈ = _; rw [eval_ne, hi]) (fun hb'' => wp_mov_imm (by decide) (WP.block_nil ?_))
    fun hb'' => WP.block_nil ?_
  · have hb'' : ¬(stackArg s 0).toNat = 8 := by simpa using hb''
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₈ r h12], by rw [mem_setReg, mem₈],
      by rw [rd_setReg, rd₈], by rw [wr_setReg, wr₈], by rw [sp_setReg, sp₈], ?_, fun h => absurd h.2.2 hb'',
      fun _ => ?_⟩
    · rw [z_setReg, hi]; simp only [IValid, hb'', and_false, decide_false]
    · rw [gpr_setReg_self]; simp only [ICode, hb, hb']; rfl
  · have hb'' : (stackArg s 0).toNat = 8 := by simpa using hb''
    refine ⟨fun r _ h12 => g₈ r h12, mem₈, rd₈, wr₈, sp₈, ?_, fun _ => g₈ _ (by decide),
      fun h => absurd ⟨hb, hb', hb''⟩ h⟩
    rw [hi]; simp only [IValid, hb, hb', hb'', and_self, decide_true]

end VG.Proof.Rc2.Arm.Stream

end

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` once the lengths are valid

-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_ldr wp_str wp_ldrSp eval_ne)

/-- The state before the call of `vg_rc2_expand_key`, from the entry state `s`. -/
structure ArgsPost (s u : State) : Prop where
  r0 : u.gpr .r0 = s.gpr .r0
  r1 : u.gpr .r1 = s.gpr .r1
  r2 : u.gpr .r2 = s.gpr .r2
  r3 : u.gpr .r3 = stackArg s 1
  r12 : u.gpr .r12 = stackArg s 2
  callee : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = s.gpr r
  sp : u.sp = s.sp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  frame : Frame [⟨State.addr (stackArg s 1) + BitVec.ofNat 64 128, 8⟩,
    ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩] s.mem u.mem
  lr : u.mem.readW (State.addr (stackArg s 2) + BitVec.ofNat 64 512) 32 = s.gpr .lr
  iv : Spec.Rc2.blockAt u.mem (State.addr (stackArg s 1) + BitVec.ofNat 64 128) =
    Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r3))

theorem args_ok (s : State) (hs : initContract.pre s) (hv : IValid s) (c : State) (hc : CheckPost s c) :
    WP isa (.block initArgs) c (ArgsPost s) := by
  obtain ⟨_, spfit, hrd, hwr, _, _, ivCtx, ivScr, ctxScr, ctxArgs, scrArgs, _, _, _, _, _, _, fitIV,
    fitC, fitS⟩ := hs
  have hL : (stackArg s 0).toNat = 8 := hv.2.2
  rw [hL] at ivCtx ivScr fitIV hrd
  have g (r : Reg) (h : r ≠ .r12) : c.gpr r = s.gpr r := by
    by_cases h0 : r = .r0
    · subst h0; exact hc.ok hv
    · exact hc.keep r h0 h
  have argR (i : Nat) (hi : i < 3) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 :=
    argIn (by rw [hrd]; simp) hi spfit
  generalize hIV : s.gpr .r3 = IV at *
  generalize hCt : stackArg s 1 = Ct at *
  generalize hS : stackArg s 2 = S at *
  generalize hLR : s.gpr .lr = LR at *
  have lrSub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ := Offset.sub_base _ (by decide)
  have ivSub' : Region.Sub ⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩ ⟨State.addr Ct, 144⟩ :=
    Offset.sub_base _ (by decide)
  have argsSep : ∀ r ∈ [(⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩ : Region),
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩], (Region.mk (stackArgAddr s 0) 12).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ctxArgs.symm.sub_right ivSub'
    · exact scrArgs.symm.sub_right lrSub
  rw [show initArgs = [.ldrSp .r12 8, .str .lr .r12 512, .ldr .lr .r3 0, .ldr .r3 .r3 4, .ldrSp .r12 4,
    .str .lr .r12 128, .str .r3 .r12 132, .mov .r3 (.reg .r12), .ldrSp .r12 8] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [hc.sp]; rfl)
    (by rw [hc.rd, hc.wr]; exact argR 2 (by decide)) fun u₁ v₁ => ?_
  have r12₁ : u₁.gpr .r12 = S := by rw [v₁.gpr, hc.mem]; exact hS
  refine wp_str (a := State.addr S + BitVec.ofNat 64 512) (by decide) (by rw [r12₁]; exact addr_add (by omega_arith))
    (by rw [v₁.wr, hc.wr, hwr]; exact ⟨⟨State.addr S, 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₂ v₂ => ?_
  have m₂ : u₂.mem = s.mem.writeW (State.addr S + BitVec.ofNat 64 512) LR := by
    rw [v₂.mem, v₁.mem, hc.mem, v₁.other _ (by decide), g _ (by decide), hLR]
  have f₂ : Frame [⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩, ⟨State.addr S + BitVec.ofNat 64 512, 4⟩]
      s.mem u₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have r3₂ : u₂.gpr .r3 = IV := by rw [v₂.gpr, v₁.other _ (by decide), g _ (by decide), hIV]
  have ivR : InRegions (u₂.rd ++ u₂.wr) (State.addr IV) 8 := by
    rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, hc.rd, hc.wr, hrd]; exact ⟨_, by simp, Region.contains_self _ _⟩
  have ivRead (k : Nat) (hk : k ≤ 4) : u₂.mem.readW (State.addr IV + BitVec.ofNat 64 k) 32 =
      s.mem.readW (State.addr IV + BitVec.ofNat 64 k) 32 := by
    rw [m₂]
    refine Mem.readW_writeW_sep (ivScr.sep (Offset.contains_base _ (by omega_arith) (by omega_arith)) ?_) (by decide)
    exact Offset.contains_base _ (by decide) (by decide)
  refine wp_ldr (a := State.addr IV + BitVec.ofNat 64 0) (by decide)
    (by rw [r3₂]; exact addr_add (by omega_arith))
    (by obtain ⟨r, hr, hc'⟩ := ivR; exact ⟨r, hr, by rw [add0]; unfold Region.Contains at hc' ⊢; omega_arith⟩)
    fun u₃ v₃ => ?_
  refine wp_ldr (a := State.addr IV + BitVec.ofNat 64 4) (by decide)
    (by rw [v₃.other _ (by decide), r3₂]; exact addr_add (by omega_arith))
    (by rw [v₃.rd, v₃.wr]; exact (Cbc.halves ivR).2) fun u₄ v₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) (by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]; rfl)
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, hc.rd, hc.wr]; exact argR 1 (by decide))
    fun u₅ v₅ => ?_
  have r12₅ : u₅.gpr .r12 = Ct := by
    rw [v₅.gpr, v₄.mem, v₃.mem, stackArg_frame f₂ spfit argsSep (by decide)]; exact hCt
  have wr₅ : u₅.wr = s.wr := by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, hc.wr]
  refine wp_str (a := State.addr Ct + BitVec.ofNat 64 128) (by decide) (by rw [r12₅]; exact addr_add (by omega_arith))
    (by rw [wr₅, hwr]; exact ⟨⟨State.addr Ct, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩) fun u₆ v₆ => ?_
  refine wp_str (a := State.addr Ct + BitVec.ofNat 64 128 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₆.gpr, r12₅, Offset.add_add]; exact addr_add (by omega_arith))
    (by rw [v₆.wr, wr₅, hwr, Offset.add_add]; exact ⟨⟨State.addr Ct, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₇ v₇ => wp_mov (op2_reg _ _) fun u₈ v₈ => ?_
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide)
    (by rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]; rfl)
    (by rw [v₈.rd, v₈.wr, v₇.rd, v₇.wr, v₆.rd, v₆.wr, v₅.rd, wr₅, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hc.rd]
        exact argR 2 (by decide)) fun u₉ v₉ => WP.block_nil ?_
  -- The memory.
  have w0 : u₅.gpr .lr = s.mem.readW (State.addr IV + BitVec.ofNat 64 0) 32 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, ivRead 0 (by decide)]
  have w1 : u₆.gpr .r3 = s.mem.readW (State.addr IV + BitVec.ofNat 64 4) 32 := by
    rw [v₆.gpr, v₅.other _ (by decide), v₄.gpr, v₃.mem, ivRead 4 (by decide)]
  have m₇ : u₇.mem = u₂.mem.writeW (State.addr Ct + BitVec.ofNat 64 128)
      (s.mem.readW (State.addr IV + BitVec.ofNat 64 4) 32 ++ s.mem.readW (State.addr IV + BitVec.ofNat 64 0) 32) := by
    rw [v₇.mem, w1, v₆.mem, w0, v₅.mem, v₄.mem, v₃.mem, VG.Proof.Rc2.Word32.write64_pair]
  have mem₉ : u₉.mem = u₇.mem := by rw [v₉.mem, v₈.mem]
  have f₇ : Frame [⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩, ⟨State.addr S + BitVec.ofNat 64 512, 4⟩]
      s.mem u₇.mem := by
    rw [m₇]; exact f₂.writeW (by simp) _ (Region.contains_self _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr hl => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.gpr, v₇.gpr, v₆.gpr, r12₅, hCt]
  · rw [v₉.gpr, v₈.mem, stackArg_frame f₇ spfit argsSep (by decide)]
  · obtain ⟨h0, h1, h2, h3, h12⟩ := preserved_ne hr hl
    rw [v₉.other _ h12, v₈.other _ h3, v₇.gpr, v₆.gpr, v₅.other _ h12, v₄.other _ h3, v₃.other _ hl, v₂.gpr,
      v₁.other _ h12, g _ h12]
  · rw [v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]
  · rw [v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hc.rd]
  · rw [v₉.wr, v₈.wr, v₇.wr, v₆.wr, wr₅]
  · rw [hCt, hS, mem₉]; exact f₇
  · rw [hS, hLR, mem₉, m₇, Mem.readW_writeW_sep (((ctxScr.sub_left ivSub').sub_right lrSub).symm.sep (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide), m₂, Mem.readW_writeW_self32]
  · rw [hCt, hIV, mem₉, m₇, Proof.Rc2.blockAt_store64, add0, ← VG.Proof.Rc2.Word32.read64_pair,
      ← Proof.Rc2.blockAt_read64]

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: helpers for the constant-time proofs

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`), with these
helpers.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (eval_eq)

theorem wp_nil_inv {s : State} {Q : State → Prop} (h : WP isa (.block []) s Q) : Q s := by
  obtain ⟨_, _, he, hq⟩ := h
  cases he with
  | block h => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]; exact hq

theorem sa0' (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  unfold stackArgAddr; rw [show s.sp + BitVec.ofNat 32 (4 * 0) = s.sp from BitVec.add_zero _]

/-- Two states agree on the registers `rs` and the 12 bytes of stack arguments. -/
theorem agree12 {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (hsp : s₁.sp = s₂.sp)
    (fit : s₁.sp.toNat + 12 ≤ 2 ^ 32)
    (hw₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨stackArgAddr s₁ 0, 12⟩ r)
    (hw₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨stackArgAddr s₂ 0, 12⟩ r)
    (ha : ∀ i < 3, stackArg s₁ i = stackArg s₂ i) : VG.Arm.Taint.Agree (argTaint rs 12) s₁ s₂ :=
  agree_argTaint h hsp ⟨fit, by rw [← sa0']; exact hw₁⟩ ⟨hsp ▸ fit, by rw [← sa0']; exact hw₂⟩
    (argMem_of (j := 3) hsp fit ha)

theorem stackArg_keep {s t : State} (ht : Keep s t) (i : Nat) : stackArg t i = stackArg s i := by
  unfold stackArg stackArgAddr; rw [ht.mem, ht.sp]

end VG.Proof.Rc2.Arm.Stream

end

section

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` is correct

-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_ldr wp_ldrSp eval_ne)

/-- The postcondition of `init`: the callee-saved registers and the contract's. -/
abbrev InitPost (s s' : State) : Prop := (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ initContract.post s s'

theorem key_pre (s : State) (hs : initContract.pre s) (ht : InitTab s) (hv : IValid s) (u : State)
    (hu : ArgsPost s u) (hsy : u.syms = s.syms) :
    KeyPre u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) := by
  obtain ⟨sp8, _, hrd, hwr, keyCtx, keyScr, _, _, ctxScr, _, _, bKey, _, bCtx, bScr, _, fitK, _, fitC, fitS⟩ := hs
  have p128 : Region.Sub ⟨State.addr (stackArg s 1), 128⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Region.sub_prefix (by decide)
  have p512 : Region.Sub ⟨State.addr (stackArg s 2), 512⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Region.sub_prefix (by decide)
  have eb : (⟨State.addr u.sp - 8, 8⟩ : Region) = ⟨State.addr s.sp - 8, 8⟩ := by rw [hu.sp]
  have et : tbl u = tbl s := by unfold tbl; rw [hsy]
  have tCtx : (tbl s).Disjoint ⟨State.addr (stackArg s 1), 144⟩ := ht.wr _ (by rw [hwr]; exact List.mem_cons_self)
  have tScr : (tbl s).Disjoint ⟨State.addr (stackArg s 2), 576⟩ := ht.wr _ (by rw [hwr]; simp)
  refine ⟨hu.r0, hu.r1, hu.r2, hu.r3, hu.r12, by rw [hu.sp]; exact sp8,
    ⟨hv.1.1, hv.1.2, hv.2.1.1, hv.2.1.2⟩, keyCtx.sub_right p128, keyScr.sub_right p512,
    (ctxScr.sub_left p128).sub_right p512, ?_, ?_, ?_, fitK, by omega_arith, by omega_arith, ?_, ?_,
    by rw [hsy]; exact ht.fit, ?_, by rw [et]; exact tCtx.sub_right p128, by rw [et]; exact tScr.sub_right p512,
    by show (Region.mk (State.addr u.sp - 8) 8).Disjoint (tbl u); rw [et, eb]; exact ht.below.symm,
    by rw [et, hu.rd, hrd]; simp, by rw [hsy]; exact ht.al⟩
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bKey
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bCtx.sub_right p128
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bScr.sub_right p512
  · rw [hu.rd, hu.wr, hrd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, 0, (add0 _).symm, by simp⟩
  · rw [hu.wr, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (stackArg s 1), 144⟩, by simp, 0, (add0 _).symm, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, 0, (add0 _).symm, by simp⟩
  · rw [hsy]
    intro i hi
    have hi' : i < 32 := by rw [piQuads_length] at hi; exact hi
    rw [hu.frame.readW (r := tbl s) (Offset.contains_base _ (by omega_arith)
        (by have := ht.fit; omega_arith)) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact tCtx.sub_right (ivSub _)
        · exact tScr.sub_right (lrSub _)) (by decide)]
    exact ht.held i hi

theorem tail_ok (s : State) (hs : initContract.pre s) (hv : IValid s) (u : State) (hu : ArgsPost s u)
    (v : State) (hk : KeyPost u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) v) :
    WP isa (.block (restoreLr ++ ([.mov .r0 (.imm 0)] : List Instr))) v (InitPost s) := by
  obtain ⟨_, spfit, hrd, hwr, keyCtx, keyScr, _, _, ctxScr, ctxArgs, scrArgs, bKey, _, bCtx, bScr, bArgs,
    fitK, _, fitC, fitS⟩ := hs
  have eb : below u = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, hu.sp]
  have frame₂ := hk.frame
  rw [eb] at frame₂
  have p128 : Region.Sub ⟨State.addr (stackArg s 1), 128⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Region.sub_prefix (by decide)
  have i128 : Region.Sub ⟨State.addr (stackArg s 1) + BitVec.ofNat 64 128, 8⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Offset.sub_base _ (by decide)
  have p512 : Region.Sub ⟨State.addr (stackArg s 2), 512⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Region.sub_prefix (by decide)
  have l512 : Region.Sub ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Offset.sub_base _ (by decide)
  rw [show restoreLr ++ [.mov .r0 (.imm 0)] = [.ldrSp .r12 8, .ldr .lr .r12 512, .mov .r0 (.imm 0)] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [hk.sp, hu.sp]; rfl)
    (by rw [hk.rd, hk.wr, hu.rd, hu.wr]; exact argIn (by rw [hrd]; simp) (by decide) spfit) fun v₁ w₁ => ?_
  have hc2 : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 2) (32 / 8) := by
    rw [stackArgAddr_eq s (i := 2) (by decide) spfit]; exact Offset.contains_base _ (by decide) (by decide)
  have argsS : v.mem.readW (stackArgAddr s 2) 32 = stackArg s 2 := by
    rw [frame₂.readW hc2 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ctxArgs.symm.sub_right p128
        · exact scrArgs.symm.sub_right p512
        · exact bArgs.symm) (by decide)]
    refine stackArg_frame hu.frame spfit (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ctxArgs.symm.sub_right i128
    · exact scrArgs.symm.sub_right l512
  refine wp_ldr (a := State.addr (stackArg s 2) + BitVec.ofNat 64 512) (by decide)
    (by rw [w₁.gpr, argsS]; exact addr_add (by omega_arith))
    (by rw [w₁.rd, w₁.wr, hk.rd, hk.wr, hu.rd, hu.wr, hwr]
        exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun v₂ w₂ => wp_mov_imm (by decide) (WP.block_nil ?_)
  have lr₂ : v₂.gpr .lr = s.gpr .lr := by
    rw [w₂.gpr, w₁.mem, frame₂.readW (r := ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ((ctxScr.sub_left p128).sub_right l512).symm
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (bScr.sub_right l512).symm) (by decide), hu.lr]
  have mem₂ : v₂.mem = v.mem := by rw [w₂.mem, w₁.mem]
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [gpr_setReg_of_ne _ _ (by decide), lr₂]
    · obtain ⟨h0, _, _, _, h12⟩ := preserved_ne hr hl
      rw [gpr_setReg_of_ne _ _ h0, w₂.other _ hl, w₁.other _ h12, hk.saved r hr hl, hu.callee r hr hl]
  · have hsched : Spec.Rc2.scheduleAt (v₂.setReg .r0 0).mem (State.addr (stackArg s 1)) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat := by
      rw [mem_setReg, mem₂, hk.sched, Proof.Rc2.bytesAt_frame hu.frame _ _ (by omega_arith) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact keyCtx.sub_right i128
        · exact keyScr.sub_right l512)]
    have hiv : Spec.Rc2.blockAt (v₂.setReg .r0 0).mem (State.addr (stackArg s 1) + 128) =
        Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r3)) := by
      rw [mem_setReg, mem₂, e128, Proof.Rc2.blockAt_frame frame₂ _ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (ctxScr.sub_left i128).sub_right p512
        · exact (bCtx.sub_right i128).symm), hu.iv]
    exact init_post hv.1 hv.2.1 hv.2.2 (by rw [setWidth_append, gpr_setReg_self]) hsched hiv

theorem init_wp (s : State) (hs' : initContractC.pre s) : WP isa init s (InitPost s) := by
  obtain ⟨hs, ht⟩ := hs'
  rw [init]
  refine WP.seq (WP.mono_syms (checks_ok s hs) fun c hc syc => ?_)
  by_cases hv : IValid s
  · refine WP.ite false (by show eval .ne c = _; rw [eval_ne, hc.z]; simp [hv]) (fun h => absurd h (by simp))
      fun _ => ?_
    rw [initBody]
    exact WP.seq (WP.mono_syms (args_ok s hs hv c hc) fun u hu syu =>
      WP.seq (WP.mono (key_call (key_pre s hs ht hv u hu (syu.trans syc))) fun v hk => tail_ok s hs hv u hu v hk))
  · refine WP.ite true (by show eval .ne c = _; rw [eval_ne, hc.z]; simp [hv]) (fun _ => WP.block_nil ?_)
      (fun h => absurd h (by simp))
    refine ⟨fun r hr => ?_, ?_⟩
    · have h : r ≠ .r0 ∧ r ≠ .r12 := by
        by_cases hl : r = .lr
        · subst hl; decide
        · obtain ⟨h0, _, _, _, h12⟩ := preserved_ne hr hl; exact ⟨h0, h12⟩
      exact hc.keep r h.1 h.2
    · exact init_post_error (by rw [setWidth_append]; exact hc.err hv) hv

theorem init_correct (s : State) (hs : initContractC.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initContractC.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := init_wp s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

end VG.Proof.Rc2.Arm.Stream

end

section

/-!
# Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` is constant time

The taint analysis does not analyse frames, so the runs are related piece by
piece (`RelCT`): the checks, the copy of the IV
and the restore of `lr` are checked by the taint analysis, from the public
arguments; the branch on the checks agrees in both runs, as the lengths are
public; and the call of `vg_rc2_expand_key`, in its frame, is constant time by
its own proof (`key_rel`).
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (eval_ne)
open VG.Impl.Rc2 (piSym)

/-- The stack arguments after the call are those on entry. -/
theorem args_after_key (s : State) (hs : initContract.pre s) (u : State) (hu : ArgsPost s u) (v : State)
    (hk : KeyPost u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) v) :
    ∀ i < 3, stackArg v i = stackArg s i := by
  obtain ⟨_, spfit, _, _, _, _, _, _, _, ctxArgs, scrArgs, _, _, _, _, bArgs, _⟩ := hs
  have eb : below u = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, hu.sp]
  have frame₂ := hk.frame
  rw [eb] at frame₂
  intro i hi
  have hc : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s i) (32 / 8) := by
    rw [stackArgAddr_eq s hi spfit]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have ea : stackArgAddr v i = stackArgAddr s i := by unfold stackArgAddr; rw [hk.sp, hu.sp]
  rw [stackArg, ea, frame₂.readW hc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ctxArgs.symm.sub_right (Region.sub_prefix (by decide))
      · exact scrArgs.symm.sub_right (Region.sub_prefix (by decide))
      · exact bArgs.symm) (by decide)]
  refine stackArg_frame hu.frame spfit (fun r hr => ?_) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ctxArgs.symm.sub_right (Offset.sub_base _ (by decide))
  · exact scrArgs.symm.sub_right (Offset.sub_base _ (by decide))

theorem iwrSep {s : State} (h : initContract.pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨stackArgAddr s 0, 12⟩ r := by
  obtain ⟨_, _, _, hwr, _, _, _, _, _, ctxArgs, scrArgs, _⟩ := h
  rw [hwr]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ctxArgs.symm
  · exact scrArgs.symm

theorem checks_taint : ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) checks hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem initArgs_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [.r0, .r1, .r2, .r3] 12) (.block initArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem tail_taint :
    ∃ hc, (VG.Taint.check taint (argTaint [] 12) (.block (restoreLr ++ ([.mov .r0 (.imm 0)] : List Instr))) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem init_rel {s₀ s₀' : State} (h0C : initContractC.pre s₀) (h0'C : initContractC.pre s₀')
    (hqC : initContractC.pub s₀ s₀') : RelCT isa (fun a b => a = s₀ ∧ b = s₀') init fun _ _ => True := by
  obtain ⟨h0, ht0⟩ := h0C
  obtain ⟨h0', ht0'⟩ := h0'C
  obtain ⟨hq, hsym⟩ := hqC
  obtain ⟨q₀, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := hq
  have fit := h0.2.1
  have qa : ∀ i < 3, stackArg s₀ i = stackArg s₀' i := by
    intro i hi
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact q₅
    · exact q₆
    · exact q₇
  have regs : ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  have hvq : IValid s₀ ↔ IValid s₀' := by simp only [IValid, q₂, q₃, q₅]
  rw [init]
  refine RelCT.seq (rel_agree (F := (· = s₀)) (F' := (· = s₀'))
    (G := fun c => CheckPost s₀ c ∧ c.syms = s₀.syms) (G' := fun c => CheckPost s₀' c ∧ c.syms = s₀'.syms)
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      exact agree12 regs q₀ fit (iwrSep h0) (iwrSep h0') qa) checks_taint
    (fun s e => by rw [e]; exact WP.mono_syms (checks_ok s₀ h0) fun c hc sy => ⟨hc, sy⟩)
    (fun s e => by rw [e]; exact WP.mono_syms (checks_ok s₀' h0') fun c hc sy => ⟨hc, sy⟩)) ?_
  refine RelCT.ite (fun c c' ⟨⟨hc, _⟩, ⟨hc', _⟩⟩ => by
    show eval .ne c = eval .ne c'; rw [eval_ne, eval_ne, hc.z, hc'.z]; simp only [hvq]) ?_ ?_
  · exact RelCT.block_nil fun _ _ _ => trivial
  by_cases hv : IValid s₀
  swap
  · refine RelCT.of_false fun c c' ⟨⟨⟨hc, _⟩, _⟩, he⟩ => ?_
    change eval .ne c = _ at he
    rw [eval_ne, hc.z] at he; simp [hv] at he
  have hv' : IValid s₀' := hvq.mp hv
  rw [initBody]
  refine RelCT.mono (P := fun (c c' : State) => (CheckPost s₀ c ∧ c.syms = s₀.syms) ∧ (CheckPost s₀' c' ∧ c'.syms = s₀'.syms))
    ?_ (fun _ _ h => h.1) fun _ _ h => h
  refine RelCT.seq (rel_agree (G := fun u => ArgsPost s₀ u ∧ u.syms = s₀.syms)
    (G' := fun u => ArgsPost s₀' u ∧ u.syms = s₀'.syms) (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun c c' hcC hc'C => ?_) initArgs_taint
    (fun c hc => WP.mono_syms (args_ok s₀ h0 hv c hc.1) fun u hu sy => ⟨hu, sy.trans hc.2⟩)
    (fun c hc => WP.mono_syms (args_ok s₀' h0' hv' c hc.1) fun u hu sy => ⟨hu, sy.trans hc.2⟩)) ?_
  · obtain ⟨hc, -⟩ := hcC
    obtain ⟨hc', -⟩ := hc'C
    have g : ∀ {s c}, IValid s → CheckPost s c → ∀ r ∈ ([.r0, .r1, .r2, .r3] : List Reg), c.gpr r = s.gpr r :=
      fun hv hc r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hc.ok hv
        all_goals exact hc.keep _ (by decide) (by decide)
    have st : ∀ {s c}, CheckPost s c → ∀ i, stackArg c i = stackArg s i := fun hc i => by
      unfold stackArg stackArgAddr; rw [hc.mem, hc.sp]
    exact agree12 (fun r hr => by rw [g hv hc r hr, g hv' hc' r hr]; exact regs r hr)
      (by rw [hc.sp, hc'.sp, q₀]) (by rw [hc.sp]; exact fit)
      (by rw [hc.wr, show stackArgAddr c 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [hc.sp]]
          exact iwrSep h0)
      (by rw [hc'.wr, show stackArgAddr c' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [hc'.sp]]
          exact iwrSep h0')
      (fun i hi => by rw [st hc, st hc']; exact qa i hi)
  have hct : RelCT isa (fun u u' => (ArgsPost s₀ u ∧ u.syms = s₀.syms) ∧ (ArgsPost s₀' u' ∧ u'.syms = s₀'.syms))
      keyCall fun _ _ => True :=
    key_rel (sp₀ := s₀.sp) (T₀ := s₀.syms piSym) fun u u' ⟨⟨a, ya⟩, ⟨a', ya'⟩⟩ => ⟨key_pre s₀ h0 ht0 hv u a ya, by
      have := key_pre s₀' h0' ht0' hv' u' a' ya'; rwa [← q₁, ← q₂, ← q₃, ← q₆, ← q₇] at this, a.sp,
      a'.sp.trans q₀.symm, by rw [ya], by rw [ya', hsym]⟩
  refine RelCT.seq (rel_wp (G := fun v => ∃ u, ArgsPost s₀ u ∧
      KeyPost u (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r2) (stackArg s₀ 1) (stackArg s₀ 2) v)
    (G' := fun v => ∃ u, ArgsPost s₀' u ∧
      KeyPost u (s₀'.gpr .r0) (s₀'.gpr .r1) (s₀'.gpr .r2) (stackArg s₀' 1) (stackArg s₀' 2) v) hct
    (fun u a => WP.mono (key_call (key_pre s₀ h0 ht0 hv u a.1 a.2)) fun v hk => ⟨u, a.1, hk⟩)
    (fun u a => WP.mono (key_call (key_pre s₀' h0' ht0' hv' u a.1 a.2)) fun v hk => ⟨u, a.1, hk⟩)) ?_
  refine (rel_agree (argTaint [] 12) (fun v v' ⟨u, a, k⟩ ⟨u', a', k'⟩ => ?_) tail_taint
    (fun v ⟨u, a, k⟩ => WP.mono (tail_ok s₀ h0 hv u a v k) fun _ _ => trivial)
    (fun v ⟨u, a, k⟩ => WP.mono (tail_ok s₀' h0' hv' u a v k) fun _ _ => trivial)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  exact agree12 (fun r hr => (List.not_mem_nil hr).elim) (by rw [k.sp, a.sp, k'.sp, a'.sp, q₀])
    (by rw [k.sp, a.sp]; exact fit)
    (by rw [k.wr, a.wr, show stackArgAddr v 0 = stackArgAddr s₀ 0 by unfold stackArgAddr; rw [k.sp, a.sp]]
        exact iwrSep h0)
    (by rw [k'.wr, a'.wr, show stackArgAddr v' 0 = stackArgAddr s₀' 0 by unfold stackArgAddr; rw [k'.sp, a'.sp]]
        exact iwrSep h0')
    (fun i hi => by
      rw [args_after_key s₀ h0 u a v k i hi, args_after_key s₀' h0' u' a' v' k' i hi]; exact qa i hi)

theorem init_constantTime : ConstantTime isa initContractC.pre initContractC.pub init :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Rc2.Arm.Stream

end

/-! # Verified streaming RC2-CBC on ARMv7 -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm
open VG.Impl.Rc2 (piConsts)

theorem init_verified :
    Verified target Impl.Rc2.Arm.Stream.init (Proof.Rc2.cbcInitScratchContract (abi.withConsts piConsts) 8) :=
  Verified.of_correct init_correct init_constantTime init_implies

end VG.Proof.Rc2.Arm.Stream
