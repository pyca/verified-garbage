module

public import VerifiedGarbage.Impl.AesCtr.Arm.Final
public import VerifiedGarbage.Proof.AesCtr.Final
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Proof.AesCfb.Arm.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCtr.Arm.Body
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Cmac.Block32
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Impl.AesCtr.Arm.Final
meta import VerifiedGarbage.Proof.AesCtr.Final
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesCfb.Arm.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.Arm
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCtr.Arm.Body
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.CmacAes.Arm.Words
meta import VerifiedGarbage.Proof.Cmac.Block32
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# AES-CTR of a message's last piece on ARMv7

`cryptFinal_framed`: `vg_aes_ctr_final` (`Impl/AesCtr/Arm/Final.lean`) meets
`Proof.AesCtr.finalRoundsContract`, from which the shared contract follows
(`Proof.AesCtr.final_keyed`).

The code is proven against `ctrFinalArm`, with a third stack argument `save`
of 56 bytes (`final_implies`: the shared contract with it,
`finalScratchContract`), as a caller of the whole-block function
`vg_aes_ctr` through its contract (`modeArm ctrMode`), in a frame that pushes
its stack arguments: what a call needs and leaves (`WCall`, `WPost`,
`w_call`, constant time by `w_rel`).

* `final_setup_wp`: as AES-CFB's final functions', `save`'s address loaded,
  the registers saved there, and the arguments set up (AES-CFB's `Setup`);
* `whole_wp`: the call on the `n = len / 16` whole blocks (AES-CFB's
  `Whole ctrMode`), which leaves `Tₙ₊₁` in `ctr`;
* `final_mid_wp`: if `u = len % 16` bytes are left, the block at `save + 40`
  zeroed and the call on that one block (`tail_args_wp`, `tail_call_wp`),
  which leaves `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and its first `u`
  bytes XORed into them (`Modes.Arm.xorLoop_wp`, `tail_xor_wp`); what is
  left before the registers are restored is `Done`;
* `final_end_wp`: the registers restored from `save`;
* `final_post`: `Done` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`).

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
the whole-block function's constant time, every address and branch from the
pointers and `len`, which agree in both runs. `cryptFinal_framed` runs the
code with `save` in a frame of 72 bytes on the stack
(`Arm.Verified.stackScratchWiped`), zeroed on return.
-/

@[expose] public section

namespace VG.Proof.AesCtr.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.CmacAes.Arm (mov)
open VG.Impl.AesCfb.Arm (finalSaved loadSave finalSave finalMoves finalSetup wholeFrame finalRestore finalEnd)
open VG.Impl.AesCtr.Arm (zeroArgs oneArgs tailArgs xorArgs finalTail final cryptFinal)
open VG.Proof.AesCfb.Arm (fW fR fIv fD fL fS fV fN fU fT fTa fSch fIvR fData fBlk fTail fScr fArg fStk fWk
  fIv0 fBlks svMem fN_eq fU_eq blk_sub tail_sub fL_lt fU_lt shr4 and15 shl4 finalMoves_eq Setup Whole
  Whole.of_fupd final_test_wp blocksAt_frame' below8_sub preserved_saved finalSat setup_taint test_taint
  end_taint nil_taint armStack_noFrames encBlocks_stack)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.Arm (modeArm)
open VG.Proof.AesGcm.Arm (below toNat_ofNat32 pushed_sp8 hspA hA fA view_gpr view_sp arg0 arg1 argAddr0
  cover_pushed cover_pushed' cover_frame covers_append' stackArg_callEntry stackArgAddr_callEntry)
open VG.Arm.FrameStack (armStack belowA)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_and wp_cmp wp_ldrSp eval_eq
  eval_ne ofNat_beq_zero)
open VG.Proof.Modes.Arm (XPre XInv XDone xorLoop_wp xf add0_32)

/-- The code's contract, with the arguments `(schedule = r0, rounds = r1,
ctr = r2, data = r3, len = [sp], scratch = [sp + 4], save = [sp + 8])`,
`save` of 56 bytes: the data and the counter block as `Spec.Ctr.CryptFinal`
says, by AES with the key schedule it is given. -/
def ctrFinalArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let iv : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let sv : Region := ⟨State.addr (stackArg s 2), 56⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧
      s.rd = [sched, args] ∧ s.wr = [iv, data, scr, sv] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint sv ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint sv ∧ iv.Disjoint args ∧
      data.Disjoint scr ∧ data.Disjoint sv ∧ data.Disjoint args ∧
      scr.Disjoint sv ∧ scr.Disjoint args ∧ sv.Disjoint args ∧
      stk.Disjoint sched ∧ stk.Disjoint iv ∧ stk.Disjoint data ∧ stk.Disjoint scr ∧
      stk.Disjoint sv ∧ stk.Disjoint args ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 56 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    Spec.Ctr.CryptFinal (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) s.mem s'.mem
      (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3)) (stackArg s 0).toNat
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2

/-- The contract the frame needs: the shared one, with `save`, 56 bytes, as
a seventh argument, and 16 bytes of stack (the whole-block function's frame
and the one it pushes around its calls). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract Arm.abi Spec.Ctr.aesFinalSig "save" .u64 7 (finalPre Arm.abi.ptrBits)
    (finalPost Arm.abi.ptrBits) false 16 (some (finalLeak Arm.abi.ptrBits))

/-- A state satisfying the precondition: AES-CFB's, with `save` of 56
bytes. -/
def ctrSat : State :=
  { finalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 56⟩] }

theorem final_implies : ctrFinalArm.Implies finalScratchContract := by
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, ctrFinalArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [ctrSat, finalSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using ctrSat

/-! ## The arguments, by name -/

section
variable (s₀ : State)

/-- `save`, the block in it, and the cipher. -/
abbrev cSv : Region := ⟨State.addr (fV s₀), 56⟩
abbrev cBk32 : BitVec 32 := fV s₀ + 40
abbrev cBk : Addr := State.addr (fV s₀) + BitVec.ofNat 64 40
abbrev cBlk : Region := ⟨cBk s₀, 16⟩
abbrev cCiph : Spec.Cbc.Cipher := Spec.Cbc.aesWith (fR s₀) (fWk s₀)

/-- What the function writes, after the save: the block, not the saved
registers. -/
abbrev cW : List Region := [fIvR s₀, fData s₀, fScr s₀, cBlk s₀, fStk s₀]

end

/-- The precondition, by name. -/
structure CPre (s₀ : State) : Prop where
  sp_lo : 16 ≤ s₀.sp.toNat
  sp_hi : s₀.sp.toNat + 12 ≤ 2 ^ 32
  rd : s₀.rd = [fSch s₀, fArg s₀]
  wr : s₀.wr = [fIvR s₀, fData s₀, fScr s₀, cSv s₀]
  sch_iv : (fSch s₀).Disjoint (fIvR s₀)
  sch_data : (fSch s₀).Disjoint (fData s₀)
  sch_scr : (fSch s₀).Disjoint (fScr s₀)
  sch_sv : (fSch s₀).Disjoint (cSv s₀)
  iv_data : (fIvR s₀).Disjoint (fData s₀)
  iv_scr : (fIvR s₀).Disjoint (fScr s₀)
  iv_sv : (fIvR s₀).Disjoint (cSv s₀)
  iv_arg : (fIvR s₀).Disjoint (fArg s₀)
  data_scr : (fData s₀).Disjoint (fScr s₀)
  data_sv : (fData s₀).Disjoint (cSv s₀)
  data_arg : (fData s₀).Disjoint (fArg s₀)
  scr_sv : (fScr s₀).Disjoint (cSv s₀)
  scr_arg : (fScr s₀).Disjoint (fArg s₀)
  sv_arg : (cSv s₀).Disjoint (fArg s₀)
  stk_sch : (fStk s₀).Disjoint (fSch s₀)
  stk_iv : (fStk s₀).Disjoint (fIvR s₀)
  stk_data : (fStk s₀).Disjoint (fData s₀)
  stk_scr : (fStk s₀).Disjoint (fScr s₀)
  stk_sv : (fStk s₀).Disjoint (cSv s₀)
  stk_arg : (fStk s₀).Disjoint (fArg s₀)
  sch_fit : (fW s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (fIv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (fD s₀).toNat + fL s₀ ≤ 2 ^ 32
  scr_fit : (fS s₀).toNat + 2176 ≤ 2 ^ 32
  sv_fit : (fV s₀).toNat + 56 ≤ 2 ^ 32
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem CPre.of {s₀ : State} (h : ctrFinalArm.pre s₀) : CPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30⟩

/-! ## Regions -/

theorem blk_sv_sub (s₀ : State) : Region.Sub (cBlk s₀) (cSv s₀) := Offset.sub_base _ (by decide)

section
variable {s₀ : State} (hp : CPre s₀)
include hp

theorem CPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [fN_eq, fU_eq]; omega)

theorem CPre.blk_fit : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 32 := by
  have := hp.data_fit; have := Nat.mul_div_le (fL s₀) 16; rw [fN_eq]; omega

theorem CPre.sched_sub : Region.Sub ⟨State.addr (fW s₀), 16 * (fR s₀ + 1)⟩ (fSch s₀) :=
  Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)

theorem CPre.sched_len : 16 * (fR s₀ + 1) ≤ 2 ^ 64 := by
  rcases hp.rounds with h | h | h <;> omega

/-- The stack arguments' addresses. -/
theorem CPre.argAddr {k : Nat} (hk : k < 3) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_hi
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem CPre.arg_in {k : Nat} (hk : k < 3) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨fArg s₀, by simp [hp.rd], ?_⟩
  rw [hp.argAddr hk]
  exact Offset.contains_base _ (by omega) (by omega)

/-- The tail, as `r7` holds it. -/
theorem CPre.tail_lt (hu : fU s₀ ≠ 0) : (fD s₀).toNat + 16 * fN s₀ < 2 ^ 32 := by
  have := hp.data_fit; have := Nat.div_add_mod (fL s₀) 16; rw [fN_eq]; rw [fU_eq] at hu; omega

theorem CPre.tailA (hu : fU s₀ ≠ 0) : State.addr (fT s₀) = fTa s₀ := addr_add (hp.tail_lt hu)

theorem CPre.tail_toNat (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.tail_lt hu
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- The block, as `r3` and `r0` hold it. -/
theorem CPre.bkA : State.addr (cBk32 s₀) = cBk s₀ := addr_add (k := 40) (by have := hp.sv_fit; omega)

theorem CPre.bk_toNat : (cBk32 s₀).toNat = (fV s₀).toNat + 40 := by
  have := hp.sv_fit
  rw [BitVec.toNat_add, show (40 : BitVec 32).toNat = 40 from rfl, Nat.mod_eq_of_lt (by omega)]

end

/-- The save changes only `save`. -/
theorem svMem_frame (s₀ : State) : Frame [cSv s₀] s₀.mem (svMem s₀) :=
  Spill.saveMem_frame _ _ _ (L := 56) (by decide) finalSaved (by decide)

/-- Everything the function writes, from entry. -/
theorem big_frame {s₀ : State} {m : Mem} (hf : Frame (cW s₀) (svMem s₀) m) :
    Frame [fIvR s₀, fData s₀, fScr s₀, cSv s₀, fStk s₀] s₀.mem m :=
  ((svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨cSv s₀, by simp, blk_sv_sub s₀⟩
      · exact ⟨_, by simp, fun _ h => h⟩)

/-- The stack arguments survive what the function writes. -/
theorem CPre.argMem {s₀ : State} (hp : CPre s₀) {m : Mem}
    (hf : Frame [fIvR s₀, fData s₀, fScr s₀, cSv s₀, fStk s₀] s₀.mem m) {k : Nat} (hk : k < 3) :
    m.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := by
  refine hf.readW (r := fArg s₀) ?_ (fun r hr => ?_) (by decide)
  · rw [hp.argAddr hk]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.iv_arg.symm
    · exact hp.data_arg.symm
    · exact hp.scr_arg.symm
    · exact hp.sv_arg.symm
    · exact hp.stk_arg.symm

/-- The stack arguments survive the save. -/
theorem CPre.svArg {s₀ : State} (hp : CPre s₀) {k : Nat} (hk : k < 3) :
    (svMem s₀).readW (stackArgAddr s₀ k) 32 = stackArg s₀ k :=
  hp.argMem ((svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]) hk

/-! ## Saving the registers -/

theorem final_setup_wp {s₀ : State} (hp : CPre s₀) : WP isa (.block finalSetup) s₀ (Setup s₀) := by
  show WP isa (.block (.ldrSp .r12 8 :: (finalSave ++ finalMoves))) s₀ _
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have r12₁ : s₁.gpr .r12 = fV s₀ := u₁.gpr
  have sv := hp.sv_fit
  refine Spill.save_slots_ok (lo := 0) (hi := 36) (by decide) (by rw [r12₁]; omega) (fun d _ hd => ?_) ?_
  · rw [u₁.wr, hp.wr, r12₁]
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have m₂ : Spill.saveMem s₁.mem (State.addr (s₁.gpr .r12)) s₁.gpr finalSaved = svMem s₀ := by
    rw [u₁.mem, r12₁]
    exact Spill.saveMem_congr _ _ _ fun p hp' => u₁.other _ (by
      simp only [finalSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  generalize hs₂ : ({ s₁ with mem := Spill.saveMem s₁.mem (State.addr (s₁.gpr .r12)) s₁.gpr finalSaved } : State) = s₂
  have g₂ : s₂.gpr = s₁.gpr := by rw [← hs₂]
  have mem₂ : s₂.mem = svMem s₀ := by rw [← hs₂, m₂]
  have rd₂ : s₂.rd = s₀.rd := by rw [← hs₂, u₁.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [← hs₂, u₁.wr]
  have sp₂ : s₂.sp = s₀.sp := by rw [← hs₂, u₁.sp]
  have keep₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂, u₁.other _ h]
  rw [finalMoves_eq]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  have in₅ : ∀ k < 3, InRegions (s₅.rd ++ s₅.wr) (stackArgAddr s₀ k) 4 := fun k hk => by
    rw [u₅.rd, u₄.rd, u₃.rd, u₅.wr, u₄.wr, u₃.wr, rd₂, wr₂]; exact hp.arg_in hk
  have spA : ∀ k, State.addr (s₅.sp + BitVec.ofNat 32 (4 * k)) = stackArgAddr s₀ k := fun k => by
    rw [u₅.sp, u₄.sp, u₃.sp, sp₂]; rfl
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (spA 0) (in₅ 0 (by decide)) fun s₆ u₆ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [u₆.sp]; exact spA 1) (by
      rw [u₆.rd, u₆.wr]; exact in₅ 1 (by decide)) fun s₇ u₇ => ?_
  have mem₅ : s₅.mem = svMem s₀ := by rw [u₅.mem, u₄.mem, u₃.mem, mem₂]
  have r8₆ : s₆.gpr .r8 = stackArg s₀ 0 := by rw [u₆.gpr, mem₅, hp.svArg (by decide)]
  have r10₇ : s₇.gpr .r10 = stackArg s₀ 1 := by rw [u₇.gpr, u₆.mem, mem₅, hp.svArg (by decide)]
  refine wp_mov (op2_lsr (by decide)) fun s₈ u₈ => wp_and (op2_imm (by decide)) fun s₉ u₉ => ?_
  refine wp_add (op2_lsl (by decide)) fun s₁₀ u₁₀ => wp_mov (op2_reg _ _) fun s₁₁ u₁₁ => WP.block_nil ?_
  have hN : 16 * fN s₀ < 2 ^ 32 := by have := fL_lt s₀; rw [fN_eq]; omega
  have r12₈ : s₈.gpr .r12 = BitVec.ofNat 32 (fN s₀) := by
    rw [u₈.gpr, u₇.other _ (by decide), r8₆, shr4]
  have r8₉ : s₉.gpr .r8 = BitVec.ofNat 32 (fU s₀) := by
    rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), r8₆]
    exact and15 _
  have k₃ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s₅.gpr r = s₀.gpr r := fun r h4 h5 h6 h12 => by
    rw [u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, keep₂ _ h12]
  have k₈ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r8 → r ≠ .r10 → r ≠ .r12 → r ≠ .r7 → r ≠ .lr →
      s₁₁.gpr r = s₀.gpr r := fun r h4 h5 h6 h8 h10 h12 h7 hlr => by
    rw [u₁₁.other _ hlr, u₁₀.other _ h7, u₉.other _ h8, u₈.other _ h12, u₇.other _ h10, u₆.other _ h8,
      k₃ _ h4 h5 h6 h12]
  exact {
    r0 := k₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r1 := k₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r2 := k₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r3 := k₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r4 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, keep₂ _ (by decide)]
    r5 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide), keep₂ _ (by decide)]
    r6 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), keep₂ _ (by decide)]
    r7 := by
      rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other .r12 (by decide), u₉.other .r3 (by decide), r12₈, shl4 hN,
        u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), k₃ _ (by decide) (by decide)
        (by decide) (by decide)]
    r8 := by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), r8₉]
    r10 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        r10₇]
    r12 := by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), r12₈]
    lr := by
      rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), r10₇]
    sp := by rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂]
    mem := by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, mem₅]
    rd := by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂]
    wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂] }

/-! ## A call of the whole-block function -/

/-- The 16 bytes below the stack pointer `sp`, which a call uses: its frame
and the one the whole-block function pushes. -/
abbrev stk16 (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 16, 16⟩

theorem below_stk (sp : BitVec 32) : Region.Sub (below sp) (stk16 sp) :=
  Offset.sub_below _ (by decide) (by decide)

theorem below16_stk {sp : BitVec 32} (hsp : 16 ≤ sp.toNat) :
    Region.Sub ⟨State.addr (sp - 8) - BitVec.ofNat 64 8, 8⟩ (stk16 sp) := by
  rw [hA (s := { finalSat with sp := sp }) (show 8 ≤ sp.toNat by omega),
    show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.sub_sub, BitVec.ofNat_add_ofNat]
  exact Region.sub_prefix (by decide)

theorem belowA16_stk {sp : BitVec 32} (hsp : 16 ≤ sp.toNat) : Region.Sub (belowA (sp - 8) 8) (stk16 sp) := by
  show Region.Sub ⟨State.addr (sp - 8 - BitVec.ofNat 32 8), 8⟩ _
  rw [BitVec.sub_sub, show (8 : BitVec 32) + BitVec.ofNat 32 8 = BitVec.ofNat 32 16 from rfl,
    FrameStack.addr_sub' (by omega)]
  exact Region.sub_prefix (by decide)

/-- What a call of `vg_aes_ctr` needs: the key schedule at `W` for `R`
rounds, the counter block at `C`, `n` blocks at `D` and the scratch buffer at
`S`, with `n` in `r12` and `S` in `lr`, to push. -/
structure WCall (s : State) (W R C D S : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 n
  lr : s.gpr .lr = S
  rounds : R.toNat = 10 ∨ R.toNat = 12 ∨ R.toNat = 14
  hsp : 16 ≤ s.sp.toNat
  fitW : W.toNat + 240 ≤ 2 ^ 32
  fitC : C.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  fitS : S.toNat + 2176 ≤ 2 ^ 32
  wc : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  wd : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  cd : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  cs : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  bw : (stk16 s.sp).Disjoint ⟨State.addr W, 240⟩
  bc : (stk16 s.sp).Disjoint ⟨State.addr C, 16⟩
  bd : (stk16 s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  bs : (stk16 s.sp).Disjoint ⟨State.addr S, 2176⟩
  reads : Covers [⟨State.addr W, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2176⟩] s.wr

/-- AES with `R` rounds and the key schedule at `W`. -/
abbrev wCiph (m : Mem) (W R : BitVec 32) : Spec.Cbc.Cipher :=
  Spec.Cbc.aesWith R.toNat (bytesAt m (State.addr W) (16 * (R.toNat + 1)))

/-- What a call of `vg_aes_ctr` leaves. -/
structure WPost (s : State) (W R C D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2176⟩, stk16 s.sp] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem (State.addr D) n =
    Spec.Ctr.crypt (wCiph s.mem W R) (bytesAt s.mem (State.addr C) 16) (Spec.Cbc.blocksAt s.mem (State.addr D) n)
  ctr : bytesAt s'.mem (State.addr C) 16 = Spec.Ctr.next (bytesAt s.mem (State.addr C) 16) n

abbrev wRd (sp W : BitVec 32) : List Region := [⟨State.addr W, 240⟩, below sp]
abbrev wWr (C D S : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr S, 2176⟩]

theorem crypt_stack : armStack Impl.AesCtr.Arm.crypt = 8 := by
  simp only [Impl.AesCtr.Arm.crypt, Impl.AesCbc.Arm.whole, Impl.AesCtr.Arm.body, Impl.AesCbc.Arm.encFrame,
    armStack, encBlocks_stack]
  decide

theorem crypt_correct : ∀ s, (modeArm AesCtr.ctrMode).pre s →
    ∃ t s', Exec isa Impl.AesCtr.Arm.crypt s t s' ∧ abiPreserved s s' ∧ (modeArm AesCtr.ctrMode).post s s' :=
  fun _ hs => AesCbc.Arm.whole_wp body_ok hs

namespace WCall
variable {s : State} {W R C D S : BitVec 32} {n : Nat} (h : WCall s W R C D S n)
include h

theorem hsp8 : 8 ≤ s.sp.toNat := by have := h.hsp; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem pre : (modeArm AesCtr.ctrMode).pre
    ((pushed [.r12, .lr] s).callEntry.withRegions (wRd s.sp W) (wWr C D S n)) := by
  have hn := toNat_ofNat32 h.n_lt
  have hs8 := h.hsp8
  simp only [modeArm, view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide),
    view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1, h.r2, h.r3,
    State.withRegions_rd, State.withRegions_wr, view_sp, stackArgAddr_withRegions, stackArg_withRegions,
    stackArg_callEntry, stackArgAddr_callEntry, arg0 hs8, arg1 hs8, argAddr0 hs8, h.r12, h.lr, hn, hspA hs8]
  have b8 := below_stk s.sp
  have b16 := below16_stk h.hsp
  refine ⟨trivial, trivial, h.wc, h.wd, h.ws, h.cd, h.cs, h.ds, (h.bc.sub_left b8).symm,
    (h.bd.sub_left b8).symm, (h.bs.sub_left b8).symm, h.bw.sub_left b16, h.bc.sub_left b16,
    h.bd.sub_left b16, h.bs.sub_left b16, h.fitW, h.fitC, h.fitD, h.fitS, by have := h.hsp; omega,
    by have := s.sp.isLt; omega, h.rounds⟩

theorem cov : Covers (wRd s.sp W ++ wWr C D S n) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  refine covers_append' (covers_append' (cover_pushed' h.reads) (cover_frame h.hsp8 (by decide)))
    (cover_pushed' (fun x n' hi => ?_))
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (wWr C D S n) (pushed [.r12, .lr] s).wr := cover_pushed h.writes

end WCall

theorem w_call {s : State} {W R C D S : BitVec 32} {n : Nat} (h : WCall s W R C D S n) :
    WP isa (wholeFrame "vg_aes_ctr" Impl.AesCtr.Arm.crypt) s (WPost s W R C D S n) := by
  have hs8 := h.hsp8
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using hs8) (by simp) ?_
  refine FrameStack.WP.callF (k := modeArm AesCtr.ctrMode) crypt_correct (rd := wRd s.sp W)
    (wr := wWr C D S n) h.pre h.cov h.covW (by rw [crypt_stack, pushed_sp8, hspA hs8]; have := h.hsp; omega) ?_
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs hpost
  have hn := toNat_ofNat32 h.n_lt
  have hR' : 16 * (R.toNat + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega
  have fA' := fA (s := s) hs8
  have b8 := below_stk s.sp
  have bytesW : bytesAt (pushed [.r12, .lr] s).mem (State.addr W) (16 * (R.toNat + 1)) =
      bytesAt s.mem (State.addr W) (16 * (R.toNat + 1)) :=
    Proof.Cmac.bytesAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((h.bw.sub_left b8).symm.sub_left (Region.sub_prefix hR'))) (by omega)
  have bytesC : bytesAt (pushed [.r12, .lr] s).mem (State.addr C) 16 = bytesAt s.mem (State.addr C) 16 :=
    Proof.Cmac.bytesAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.bc.sub_left b8).symm) (by decide)
  have blocksD : Spec.Cbc.blocksAt (pushed [.r12, .lr] s).mem (State.addr D) n =
      Spec.Cbc.blocksAt s.mem (State.addr D) n :=
    blocksAt_frame' fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.bd.sub_left b8).symm)
  obtain ⟨hdata, hctr⟩ := hpost
  simp only [State.withRegions_mem, State.callEntry_mem, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, stackArg_withRegions, stackArg_callEntry, arg0 hs8, h.r12, hn, bytesW, bytesC,
    blocksD, AesCtr.ctrMode_out, AesCtr.ctrMode_chain, AesCbc.length_blocksAt] at hdata hctr
  have fB : Frame (wWr C D S n ++ [belowA (pushed [.r12, .lr] s).sp (armStack Impl.AesCtr.Arm.crypt)])
      (pushed [.r12, .lr] s).mem s₂.mem := hf
  rw [crypt_stack, pushed_sp8] at fB
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp8]; exact BitVec.sub_add_cancel _ _
  · rw [popped_gpr (by rintro rfl; simp [preserved] at hr), hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (fA'.sub fun r hr => ?_).trans (fB.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stk16 s.sp, by simp, b8⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨stk16 s.sp, by simp, belowA16_stk h.hsp⟩
  · rw [popped_mem]; exact hdata
  · rw [popped_mem]; exact hctr

/-- Calls of `vg_aes_ctr` with the same arguments and stack pointer in both
runs are constant time. -/
theorem w_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W R C D S : BitVec 32, ∃ n : Nat,
      WCall s₁ W R C D S n ∧ WCall s₂ W R C D S n ∧ s₁.sp = s₂.sp) :
    RelCT isa P (wholeFrame "vg_aes_ctr" Impl.AesCtr.Arm.crypt) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, _, _, _, _, _, _, e⟩ := h _ _ hp; exact e) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, pa, pb⟩ e₁ e₂
  obtain ⟨W, R, C, D, S, n, h₁, h₂, hsp⟩ := h _ _ hp
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₁.hsp8), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₂.hsp8), Option.some.injEq] at pb
  subst pa pb
  refine RelCT.call (k := modeArm AesCtr.ctrMode) crypt_correct (AesCbc.Arm.whole_ct body_ok body_ct)
    (wRd s₁.sp W) (wWr C D S n) (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₂ := h₂.pre
  rw [← hsp] at p₂
  refine ⟨h₁.pre, p₂, ?_, h₁.cov, h₁.covW, hsp ▸ h₂.cov, h₂.covW⟩
  simp only [modeArm, stackArg_withRegions, stackArg_callEntry, arg0 h₁.hsp8, arg1 h₁.hsp8, arg0 h₂.hsp8,
    arg1 h₂.hsp8, view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide),
    view_gpr _ _ _ .r3 (by decide), view_sp, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₂.r0, h₂.r1, h₂.r2,
    h₂.r3, h₂.r12, h₂.lr, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The whole blocks -/

/-- The memory of the regions apart from what the function writes. -/
theorem CPre.sched_big {s₀ : State} (hp : CPre s₀) :
    ∀ r ∈ [fIvR s₀, fData s₀, fScr s₀, cSv s₀, fStk s₀],
      (⟨State.addr (fW s₀), 16 * (fR s₀ + 1)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left hp.sched_sub
  · exact hp.sch_data.sub_left hp.sched_sub
  · exact hp.sch_scr.sub_left hp.sched_sub
  · exact hp.sch_sv.sub_left hp.sched_sub
  · exact hp.stk_sch.symm.sub_left hp.sched_sub

/-- The key schedule, from any memory the function leaves. -/
theorem CPre.wk {s₀ : State} (hp : CPre s₀) {m : Mem}
    (hf : Frame [fIvR s₀, fData s₀, fScr s₀, cSv s₀, fStk s₀] s₀.mem m) :
    wCiph m (fW s₀) (s₀.gpr .r1) = cCiph s₀ := by
  show Spec.Cbc.aesWith (fR s₀) (bytesAt m (State.addr (fW s₀)) (16 * (fR s₀ + 1))) = _
  rw [Proof.Cmac.bytesAt_frame hf hp.sched_big hp.sched_len]

theorem CPre.svFrame {s₀ : State} (_ : CPre s₀) :
    Frame [fIvR s₀, fData s₀, fScr s₀, cSv s₀, fStk s₀] s₀.mem (svMem s₀) :=
  (svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]

theorem setup_call {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    WCall s (fW s₀) (s₀.gpr .r1) (fIv s₀) (fD s₀) (fS s₀) (fN s₀) := by
  have hst : stk16 s.sp = fStk s₀ := by rw [h.sp]
  refine ⟨h.r0, h.r1, h.r2, h.r3, h.r12, h.lr, hp.rounds, by rw [h.sp]; exact hp.sp_lo, hp.sch_fit, hp.iv_fit,
    hp.blk_fit, hp.scr_fit, hp.sch_iv, hp.sch_data.sub_right (blk_sub s₀), hp.sch_scr,
    hp.iv_data.sub_right (blk_sub s₀), hp.iv_scr, hp.data_scr.sub_left (blk_sub s₀), by rw [hst]; exact hp.stk_sch,
    by rw [hst]; exact hp.stk_iv, by rw [hst]; exact hp.stk_data.sub_right (blk_sub s₀),
    by rw [hst]; exact hp.stk_scr, ?_, ?_⟩
  · rw [h.rd, h.wr, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩

theorem whole_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    WP isa (wholeFrame "vg_aes_ctr" Impl.AesCtr.Arm.crypt) s (Whole AesCtr.ctrMode s₀) := by
  refine WP.mono (w_call (setup_call hp h)) fun s' w => ?_
  have keep : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r := w.saved
  have sv := hp.svFrame
  have eW : wCiph s.mem (fW s₀) (s₀.gpr .r1) = cCiph s₀ := by rw [h.mem]; exact hp.wk sv
  have eIv : bytesAt s.mem (State.addr (fIv s₀)) 16 = fIv0 s₀ := by
    rw [h.mem]; exact Proof.Cmac.bytesAt_frame (svMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv) (by decide)
  have eB : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = fBlks s₀ := by
    rw [h.mem]; exact blocksAt_frame' (svMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (blk_sub s₀))
  have hst : stk16 s.sp = fStk s₀ := by rw [h.sp]
  refine ⟨by rw [keep .r4 (by simp [preserved]) (by decide), h.r4],
    by rw [keep .r5 (by simp [preserved]) (by decide), h.r5],
    by rw [keep .r6 (by simp [preserved]) (by decide), h.r6],
    by rw [keep .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [keep .r8 (by simp [preserved]) (by decide), h.r8],
    by rw [keep .r10 (by simp [preserved]) (by decide), h.r10],
    by rw [w.sp, h.sp], by rw [w.rd, h.rd], by rw [w.wr, h.wr], ?_, ?_, ?_⟩
  · rw [← h.mem]; have f := w.frame; rw [hst] at f; exact f
  · rw [w.out, eW, eIv, eB, AesCtr.ctrMode_out]
  · rw [w.ctr, eIv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]

/-! ## The partial last block -/

section
variable (s₀ : State)

/-- What the function writes before the XOR. -/
abbrev cW1 : List Region := [fIvR s₀, fBlk s₀, fScr s₀, cBlk s₀, fStk s₀]

end

theorem cW1_cW {s₀ : State} {m : Mem} (hf : Frame (cW1 s₀) (svMem s₀) m) : Frame (cW s₀) (svMem s₀) m :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem whole_cW1 {s₀ s : State} (h : Whole AesCtr.ctrMode s₀ s) : Frame (cW1 s₀) (svMem s₀) s.mem :=
  h.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-- The partial block is apart from what the function writes before the XOR. -/
theorem CPre.tail_cW1 {s₀ : State} (hp : CPre s₀) : ∀ r ∈ cW1 s₀, (fTail s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
  · exact hp.blk_tail.symm
  · exact hp.data_scr.sub_left (tail_sub s₀)
  · exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)
  · exact (hp.stk_data.sub_right (tail_sub s₀)).symm

/-- The whole blocks are apart from what the function writes after them. -/
theorem CPre.blk_tailW {s₀ : State} (hp : CPre s₀) :
    ∀ r ∈ [fIvR s₀, cBlk s₀, fScr s₀, fStk s₀], (fBlk s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.iv_data.sub_right (blk_sub s₀)).symm
  · exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  · exact hp.data_scr.sub_left (blk_sub s₀)
  · exact (hp.stk_data.sub_right (blk_sub s₀)).symm

/-- The counter block is apart from the block and the tail. -/
theorem CPre.iv_blk {s₀ : State} (hp : CPre s₀) : (fIvR s₀).Disjoint (cBlk s₀) :=
  hp.iv_sv.sub_right (blk_sv_sub s₀)

/-- What the arguments of the call on the block leave. -/
structure TArgs (s₀ s : State) : Prop where
  call : WCall s (fW s₀) (s₀.gpr .r1) (fIv s₀) (cBk32 s₀) (fS s₀) 1
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) =
    Spec.Ctr.crypt (cCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (State.addr (fIv s₀)) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)
  zero : bytesAt s.mem (cBk s₀) 16 = List.replicate 16 0
  tailb : ∀ q < fU s₀, s.mem (fTa s₀ + BitVec.ofNat 64 q) = s₀.mem (fTa s₀ + BitVec.ofNat 64 q)

theorem zeroArgs_eq (is : List Instr) :
    zeroArgs ++ is = .mov .r0 (.imm 0) :: (Proof.CmacAes.Arm.zeroBlk .r0 .r12 40 ++ is) := rfl

theorem oneArgs_eq : oneArgs = [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r6),
    .dp .add .r3 .r12 (.imm 40), .mov .r12 (.imm 1), .mov .lr (.reg .r10)] := rfl

theorem tail_args_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.block tailArgs) s (TArgs s₀) := by
  show WP isa (.block (.ldrSp .r12 8 :: (zeroArgs ++ oneArgs))) s _
  have f1 := whole_cW1 h
  have big := big_frame (cW1_cW f1)
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) (by rw [h.sp]; rfl)
    (by rw [h.rd, h.wr]; exact hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have r12₁ : s₁.gpr .r12 = fV s₀ := by rw [u₁.gpr]; exact hp.argMem big (by decide)
  rw [zeroArgs_eq]
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have sv := hp.sv_fit
  have r12₂ : s₂.gpr .r12 = fV s₀ := by rw [u₂.other _ (by decide), r12₁]
  have bA : State.addr (s₂.gpr .r12) + BitVec.ofNat 64 40 = cBk s₀ := by rw [r12₂]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₂.gpr (by decide) (by rw [r12₂]; omega) ?_
    fun s₃ g₃ m₃ rd₃ wr₃ sp₃ => ?_
  · rw [bA, u₂.wr, u₁.wr, h.wr, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨cSv s₀, by simp, 40, rfl, by simp⟩
  rw [bA] at m₃
  rw [oneArgs_eq]
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ =>
    wp_add (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_imm (by decide)) fun s₈ u₈ =>
    wp_mov (op2_reg _ _) fun s₉ u₉ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h0 h12 => by
    rw [g₃, u₂.other _ h0, u₁.other _ h12]
  have mem₉ : s₉.mem = Proof.Cmac.zero4 s.mem (cBk s₀) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
  have sp₉ : s₉.sp = s₀.sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, h.sp]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, h.wr]
  have zf : Frame [cBlk s₀] s.mem (Proof.Cmac.zero4 s.mem (cBk s₀)) := AesCbc.zero4_frame _ _
  have zd : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint (cBlk s₀) → n ≤ 2 ^ 64 →
      bytesAt (Proof.Cmac.zero4 s.mem (cBk s₀)) p n = bytesAt s.mem p n := fun hd hn =>
    Proof.Cmac.bytesAt_frame zf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hn
  have hst : stk16 s₉.sp = fStk s₀ := by rw [sp₉]
  have bkA := hp.bkA
  have hbk := hp.bk_toNat
  refine ⟨⟨?_, ?_, ?_, ?_, by rw [u₉.other _ (by decide), u₈.gpr]; rfl, ?_, hp.rounds, by rw [sp₉]; exact hp.sp_lo,
    hp.sch_fit, hp.iv_fit, by rw [hbk]; omega, hp.scr_fit, hp.sch_iv, ?_, hp.sch_scr, ?_, hp.iv_scr, ?_,
    by rw [hst]; exact hp.stk_sch, by rw [hst]; exact hp.stk_iv, ?_, by rw [hst]; exact hp.stk_scr, ?_, ?_⟩,
    ?_, ?_, sp₉, rd₉, wr₉, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr, g₂ _ (by decide) (by decide), h.r4]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, u₄.other _ (by decide), g₂ _ (by decide) (by decide), h.r5]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      u₅.other _ (by decide), u₄.other _ (by decide), g₂ _ (by decide) (by decide), h.r6]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), g₃, u₂.other _ (by decide), r12₁]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), g₂ _ (by decide) (by decide), h.r10]
  · rw [bkA, Nat.mul_one]; exact hp.sch_sv.sub_right (blk_sv_sub s₀)
  · rw [bkA, Nat.mul_one]; exact hp.iv_blk
  · rw [bkA, Nat.mul_one]; exact (hp.scr_sv.sub_right (blk_sv_sub s₀)).symm
  · rw [hst, bkA, Nat.mul_one]; exact hp.stk_sv.sub_right (blk_sv_sub s₀)
  · rw [rd₉, wr₉, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₉, hp.wr, bkA, Nat.mul_one]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 40, rfl, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), g₂ _ (by decide) (by decide), h.r7]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), g₂ _ (by decide) (by decide), h.r8]
  · rw [mem₉]
    exact f1.trans (zf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [mem₉, blocksAt_frame' zf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)), h.blocks, AesCtr.ctrMode_out]
  · rw [mem₉, zd hp.iv_blk (by decide), h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]
  · rw [mem₉, Proof.Cmac.zero4_bytes]; rfl
  · rw [mem₉]
    have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; have := fU_lt s₀; omega
    rw [zf.bytes (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)) hlen hq,
      f1.bytes hp.tail_cW1 hlen hq,
      (svMem_frame s₀).bytes (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (tail_sub s₀)) hlen hq]

/-- What the call on the block leaves. -/
structure TCall (s₀ s : State) : Prop where
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) =
    Spec.Ctr.crypt (cCiph s₀) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (State.addr (fIv s₀)) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀ + 1)
  key : bytesAt s.mem (cBk s₀) 16 = cCiph s₀ (Spec.Ctr.next (fIv0 s₀) (fN s₀))
  tailb : ∀ q < fU s₀, s.mem (fTa s₀ + BitVec.ofNat 64 q) = s₀.mem (fTa s₀ + BitVec.ofNat 64 q)

theorem tail_call {s₀ : State} (hp : CPre s₀) {s s' : State} (h : TArgs s₀ s)
    (w : WPost s (fW s₀) (s₀.gpr .r1) (fIv s₀) (cBk32 s₀) (fS s₀) 1 s') : TCall s₀ s' := by
  have keep : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r := w.saved
  have hst : stk16 s.sp = fStk s₀ := by rw [h.sp]
  have fw : Frame [fIvR s₀, cBlk s₀, fScr s₀, fStk s₀] s.mem s'.mem := by
    have f := w.frame; rw [hst, hp.bkA, Nat.mul_one] at f; exact f
  have big := big_frame (cW1_cW h.frame)
  have eW : wCiph s.mem (fW s₀) (s₀.gpr .r1) = cCiph s₀ := hp.wk big
  have e1 : ∀ m : Mem, Spec.Cbc.blocksAt m (cBk s₀) 1 = [bytesAt m (cBk s₀) 16] := fun m => by
    simp [Spec.Cbc.blocksAt]
  have hout := w.out
  rw [hp.bkA, eW, h.ctr] at hout
  have hkey := Proof.Modes.CtrFinal.bytesAt_of_blocksAt_one (aesWith_length _ _) h.zero hout
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; have := fU_lt s₀; omega
  refine ⟨by rw [keep .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [keep .r8 (by simp [preserved]) (by decide), h.r8], by rw [w.sp, h.sp], by rw [w.rd, h.rd],
    by rw [w.wr, h.wr], h.frame.trans (fw.sub fun r hr => ?_), ?_, ?_, hkey, fun q hq => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [blocksAt_frame' fw hp.blk_tailW]; exact h.blocks
  · rw [w.ctr, h.ctr]; rfl
  · rw [fw.bytes (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
      · exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact hp.data_scr.sub_left (tail_sub s₀)
      · exact (hp.stk_data.sub_right (tail_sub s₀)).symm) hlen hq]
    exact h.tailb q hq

/-- What the function leaves before restoring the registers. -/
structure Done (s₀ s : State) : Prop where
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) =
    Spec.Ctr.crypt (cCiph s₀) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fTa s₀ + BitVec.ofNat 64 q) = s₀.mem (fTa s₀ + BitVec.ofNat 64 q) ^^^
    (cCiph s₀ (Spec.Ctr.next (fIv0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem (State.addr (fIv s₀)) 16 =
    Spec.Ctr.next (fIv0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : Whole AesCtr.ctrMode s₀ s) (hu : fU s₀ = 0) : Done s₀ s :=
  ⟨h.sp, h.rd, h.wr, cW1_cW (whole_cW1 h), by rw [h.blocks, AesCtr.ctrMode_out],
    fun q hq => absurd hq (by omega),
    by rw [ite_eq_left_of_eq_true _ _ (eq_true hu), h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]⟩

theorem xorArgs_eq : xorArgs = [.ldrSp .r12 8, .dp .add .r0 .r12 (.imm 40), .mov .r6 (.reg .r7),
    .mov .r7 (.reg .r8)] := rfl

theorem tail_xor_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block xorArgs) (.loop (.block Impl.Modes.Arm.xorByte) .ne)) s (Done s₀) := by
  have big := big_frame (cW1_cW h.frame)
  rw [xorArgs_eq]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) (by rw [h.sp]; rfl)
    (by rw [h.rd, h.wr]; exact hp.arg_in (by decide)) fun s₁ u₁ => ?_)
  have r12₁ : s₁.gpr .r12 = fV s₀ := by rw [u₁.gpr]; exact hp.argMem big (by decide)
  refine wp_add (op2_imm (by decide)) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have hU := fU_lt s₀
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_fit
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have hT := hp.tail_toNat hu
  have aT := hp.tailA hu
  have bkA := hp.bkA
  have hbk := hp.bk_toNat
  have sv := hp.sv_fit
  have r0₄ : s₄.gpr .r0 = cBk32 s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, r12₁]
  have r6₄ : s₄.gpr .r6 = fT s₀ := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r7]
  have r7₄ : s₄.gpr .r7 = BitVec.ofNat 32 (fU s₀) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r8]
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s₀.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₄ : s₄.wr = s₀.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have sp₄ : s₄.sp = s₀.sp := by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp]
  have blkT : (cBlk s₀).Disjoint (fTail s₀) := ((hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)).symm
  have xp : XPre s₄ (cBk32 s₀) (fT s₀) (fU s₀) := {
    fK := by rw [hbk]; omega
    fR := by rw [hT]; omega
    disj := by rw [aT, bkA]; exact blkT.sub_left (Region.sub_prefix (by omega))
    rdK := by
      rw [rd₄, wr₄, hp.rd, hp.wr, bkA]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨cSv s₀, by simp, 40, rfl, by simp only; omega⟩
    wrR := by
      rw [wr₄, hp.wr, aT]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨fData s₀, by simp, 16 * fN s₀, rfl, by simp only; omega⟩ }
  have x0 : XInv s₄ (cBk32 s₀) (fT s₀) (fU s₀) 0 s₄ :=
    ⟨by rw [add0_32, r0₄], by rw [add0_32, r6₄], by rw [Nat.sub_zero, r7₄], by omega,
      (Proof.Modes.over_zero _ _ _).symm, rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩
  refine WP.mono (xorLoop_wp xp x0) fun s' d => ?_
  have fo : Frame [fTail s₀] s₄.mem s'.mem := by rw [d.mem, aT]; exact Proof.Modes.over_frame _ _ _ _
  refine ⟨by rw [d.sp, sp₄], by rw [d.rd, rd₄], by rw [d.wr, wr₄], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact (cW1_cW h.frame).trans (by
      rw [← mem₄]
      exact fo.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' fo fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail, mem₄]
    exact h.blocks
  · rw [d.mem, ← aT, Proof.Modes.over_at hq (by omega), aT, mem₄, bkA]
    show s.mem (fTa s₀ + BitVec.ofNat 64 q) ^^^ s.mem (cBk s₀ + BitVec.ofNat 64 q) = _
    rw [h.tailb q hq, MdStream.Arm.bytesAt_getD h.key (show q < 16 by omega)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hu), Proof.Cmac.bytesAt_frame fo (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.sub_right (tail_sub s₀)) (by decide),
      mem₄, h.ctr]

theorem final_mid_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s)
    (hz : s.z = decide (fU s₀ = 0)) :
    WP isa (.ite .eq (.block []) (finalTail "vg_aes_ctr" Impl.AesCtr.Arm.crypt)) s (Done s₀) := by
  have ev : isa.eval .eq s = some (decide (fU s₀ = 0)) := by show VG.Arm.eval .eq s = _; rw [eval_eq, hz]
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [ev, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [ev, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (tail_args_wp hp h) fun _ a =>
      WP.seq (WP.mono (w_call a.call) fun _ c => tail_xor_wp hp (tail_call hp a c) hu))

/-! ## Restoring the registers -/

theorem final_end_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Done s₀ s) :
    WP isa (.block finalEnd) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  show WP isa (.block (.ldrSp .r12 8 :: finalRestore)) s _
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) (by rw [h.sp]; rfl)
    (by rw [h.rd, h.wr]; exact hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have big := big_frame h.frame
  have r12 : s₁.gpr .r12 = fV s₀ := by rw [u₁.gpr]; exact hp.argMem big (by decide)
  have sv := hp.sv_fit
  have hs : Spill.Saved s₁.mem (State.addr (s₁.gpr .r12)) s₀.gpr finalSaved := by
    rw [u₁.mem, r12]
    refine (Spill.saveMem_saved (lo := 0) (hi := 36) _ _ _ _ (by decide)).frame (lo := 0) (hi := 36) (by decide)
      h.frame fun r hr => ?_
    have hsub : Region.Sub ⟨State.addr (fV s₀) + BitVec.ofNat 64 0, 36 - 0⟩ (cSv s₀) :=
      Offset.sub_base _ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.iv_sv.symm.sub_left hsub
    · exact hp.data_sv.symm.sub_left hsub
    · exact hp.scr_sv.symm.sub_left hsub
    · exact Offset.disjoint _ (d := 0) (n := 36) (e := 40) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · exact hp.stk_sv.symm.sub_left hsub
  refine WP.mono (Spill.restore_block_ok (b := .r12) (lo := 0) (hi := 36) (by decide) (by decide)
    (by rw [r12]; omega) (fun d _ hd => ?_) hs) fun s' ⟨g, _, m, _, _, sp⟩ => ?_
  · rw [u₁.rd, u₁.wr, h.rd, h.wr, r12]
    exact ⟨cSv s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨⟨fun r hr => Spill.restored_reg g (preserved_saved r hr), by rw [sp, u₁.sp, h.sp]⟩, by rw [m, u₁.mem]⟩

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : CPre s₀) :
    WP isa cryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ ∃ s₁, Done s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_test_wp h₂) fun s₃ ⟨h₃, z₃⟩ => ?_)
  refine WP.seq (WP.mono (final_mid_wp hp h₃ z₃) fun s₄ h₄ => ?_)
  exact WP.mono (final_end_wp hp h₄) fun _ ⟨g, m⟩ => ⟨g, s₄, h₄, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalArm.post s₀ s' := by
  show Spec.Ctr.CryptFinal (ciphAt s₀.mem (State.addr (fW s₀)) (fR s₀)) s₀.mem s'.mem
    (State.addr (fIv s₀)) (State.addr (fD s₀)) (fL s₀)
  exact Proof.Modes.CtrFinal.cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem final_correct (s : State) (hs : ctrFinalArm.pre s) :
    ∃ t s', Exec isa cryptFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalArm.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp (CPre.of hs)
  exact ⟨t, s', he, hg, final_post h₁ hm⟩

/-! ## Constant time -/

section
variable {s₀ s₀' : State} (hq : ctrFinalArm.pub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_W : fW s₀ = fW s₀' := hq.2.1
theorem pub_r1 : s₀.gpr .r1 = s₀'.gpr .r1 := hq.2.2.1
theorem pub_Iv : fIv s₀ = fIv s₀' := hq.2.2.2.1
theorem pub_D : fD s₀ = fD s₀' := hq.2.2.2.2.1
theorem pub_L : stackArg s₀ 0 = stackArg s₀' 0 := hq.2.2.2.2.2.1
theorem pub_S : fS s₀ = fS s₀' := hq.2.2.2.2.2.2.1
theorem pub_V : fV s₀ = fV s₀' := hq.2.2.2.2.2.2.2
theorem pub_N : fN s₀ = fN s₀' := by rw [fN, fN, fL, fL, pub_L hq]
theorem pub_U : fU s₀ = fU s₀' := by rw [fU, fU, fL, fL, pub_L hq]
theorem pub_T : fT s₀ = fT s₀' := by rw [fT, fT, pub_D hq, pub_N hq]

end

/-- The arguments' area, apart from what may be written. -/
theorem CPre.argsWf {s₀ : State} (hp : CPre s₀) :
    s₀.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 12⟩ r := by
  have e : (⟨State.addr s₀.sp, 12⟩ : Region) = fArg s₀ := by simp [stackArgAddr]
  refine ⟨hp.sp_hi, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hp.iv_arg.symm
  · exact hp.data_arg.symm
  · exact hp.scr_arg.symm
  · exact hp.sv_arg.symm

/-- Two states of the runs agree on the taint that makes the registers `rs`
and the stack arguments public. -/
theorem agreeAt {s₀ s₀' : State} (hp : CPre s₀) (hp' : CPre s₀') (hq : ctrFinalArm.pub s₀ s₀') {a b : State}
    (sa : a.sp = s₀.sp) (sb : b.sp = s₀'.sp) (wa : a.wr = s₀.wr) (wb : b.wr = s₀'.wr)
    (ma : Frame [fIvR s₀, fData s₀, fScr s₀, cSv s₀, fStk s₀] s₀.mem a.mem)
    (mb : Frame [fIvR s₀', fData s₀', fScr s₀', cSv s₀', fStk s₀'] s₀'.mem b.mem) {rs : List Reg}
    (hr : ∀ r ∈ rs, a.gpr r = b.gpr r) : VG.Arm.Taint.Agree (argTaint rs 12) a b := by
  have arg : ∀ {σ s : State}, CPre σ → s.sp = σ.sp →
      Frame [fIvR σ, fData σ, fScr σ, cSv σ, fStk σ] σ.mem s.mem → ∀ k < 3, stackArg s k = stackArg σ k :=
    fun {σ s} hσ hs hm k hk => by
      rw [stackArg, show stackArgAddr s k = stackArgAddr σ k by simp only [stackArgAddr, hs]]
      exact hσ.argMem hm hk
  refine agree_argTaint hr (by rw [sa, sb, pub_sp hq]) (by rw [sa, wa]; exact hp.argsWf)
    (by rw [sb, wb]; exact hp'.argsWf)
    (argMem_of (j := 3) (by rw [sa, sb, pub_sp hq]) (by rw [sa]; exact hp.sp_hi) fun i hi => ?_)
  rw [arg hp sa ma i hi, arg hp' sb mb i hi]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact pub_L hq
  · exact pub_S hq
  · exact pub_V hq

theorem tailArgs_taint :
    ∃ h, (taint.check (argTaint [.r4, .r5, .r6, .r10] 12) (.block tailArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (argTaint [.r7, .r8] 12)
    (.seq (.block xorArgs) (.loop (.block Impl.Modes.Arm.xorByte) .ne)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalArm.pre s₀) (h0' : ctrFinalArm.pre s₀')
    (hq : ctrFinalArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') cryptFinal fun _ _ => True := by
  have hp := CPre.of h0
  have hp' := CPre.of h0'
  let M := AesCtr.ctrMode
  -- The registers saved and the arguments set up.
  have r₁ := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := Setup s₀) (G' := Setup s₀')
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      refine agreeAt hp hp' hq rfl rfl rfl rfl (Frame.refl _ _) (Frame.refl _ _) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact pub_W hq
      · exact pub_r1 hq
      · exact pub_Iv hq
      · exact pub_D hq) setup_taint
    (fun s e => by rw [e]; exact final_setup_wp hp) (fun s e => by rw [e]; exact final_setup_wp hp')
  -- The whole blocks.
  have r₂ := rel_wp (F := Setup s₀) (F' := Setup s₀') (G := Whole M s₀) (G' := Whole M s₀')
    (w_rel fun a b ⟨ha, hb⟩ => ⟨_, _, _, _, _, _, setup_call hp ha, by
      rw [pub_W hq, pub_r1 hq, pub_Iv hq, pub_D hq, pub_S hq, pub_N hq]; exact setup_call hp' hb,
      by rw [ha.sp, hb.sp, pub_sp hq]⟩)
    (fun _ h => whole_wp hp h) (fun _ h => whole_wp hp' h)
  -- The test.
  have r₃ := rel_agree (F := Whole M s₀) (F' := Whole M s₀')
    (G := fun s => Whole M s₀ s ∧ s.z = decide (fU s₀ = 0)) (G' := fun s => Whole M s₀' s ∧ s.z = decide (fU s₀' = 0))
    (Taint.ofRegs [.r8]) (fun a b ha hb => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.r8, hb.r8, pub_U hq]) test_taint
    (fun _ h => final_test_wp h) (fun _ h => final_test_wp h)
  -- The partial last block.
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole M s₀ a ∧ Whole M s₀' b)
      (finalTail "vg_aes_ctr" Impl.AesCtr.Arm.crypt) fun a b => Done s₀ a ∧ Done s₀' b := by
    have hu' : fU s₀' ≠ 0 := pub_U hq ▸ hu
    have a₁ := rel_agree (F := Whole M s₀) (F' := Whole M s₀') (G := TArgs s₀) (G' := TArgs s₀')
      (argTaint [.r4, .r5, .r6, .r10] 12) (fun a b ha hb => by
        refine agreeAt hp hp' hq ha.sp hb.sp ha.wr hb.wr (big_frame (cW1_cW (whole_cW1 ha)))
          (big_frame (cW1_cW (whole_cW1 hb))) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [ha.r4, hb.r4, pub_W hq]
        · rw [ha.r5, hb.r5, pub_r1 hq]
        · rw [ha.r6, hb.r6, pub_Iv hq]
        · rw [ha.r10, hb.r10, pub_S hq]) tailArgs_taint
      (fun _ h => tail_args_wp hp h) (fun _ h => tail_args_wp hp' h)
    have a₂ := rel_wp (F := TArgs s₀) (F' := TArgs s₀') (G := TCall s₀) (G' := TCall s₀')
      (w_rel fun a b ⟨ha, hb⟩ => ⟨_, _, _, _, _, _, ha.call, by
        rw [pub_W hq, pub_r1 hq, pub_Iv hq, cBk32, pub_V hq, pub_S hq]; exact hb.call,
        by rw [ha.sp, hb.sp, pub_sp hq]⟩)
      (fun _ h => WP.mono (w_call h.call) fun _ c => tail_call hp h c)
      (fun _ h => WP.mono (w_call h.call) fun _ c => tail_call hp' h c)
    have a₃ := rel_agree (F := TCall s₀) (F' := TCall s₀') (G := Done s₀) (G' := Done s₀')
      (argTaint [.r7, .r8] 12) (fun a b ha hb => by
        refine agreeAt hp hp' hq ha.sp hb.sp ha.wr hb.wr (big_frame (cW1_cW ha.frame))
          (big_frame (cW1_cW hb.frame)) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.r7, hb.r7, pub_T hq]
        · rw [ha.r8, hb.r8, pub_U hq]) xor_taint
      (fun _ h => tail_xor_wp hp h hu) (fun _ h => tail_xor_wp hp' h hu')
    exact a₁.seq (a₂.seq a₃)
  have ev {s : State} {u : Nat} (h : s.z = decide (u = 0)) : isa.eval .eq s = some (decide (u = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have r₄ : RelCT isa (fun a b => (Whole M s₀ a ∧ a.z = decide (fU s₀ = 0)) ∧
      (Whole M s₀' b ∧ b.z = decide (fU s₀' = 0)))
      (.ite .eq (.block []) (finalTail "vg_aes_ctr" Impl.AesCtr.Arm.crypt))
      (fun a b => Done s₀ a ∧ Done s₀' b) := by
    obtain ⟨_, hnil⟩ := nil_taint
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev h.2.2, pub_U hq]) ?_ ?_
    · refine ((RelCT.taint (A := taint) (Taint.ofRegs [])
        (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil).wp
        (F₁ := Done s₀) (F₂ := Done s₀') fun a b h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
      have h0 : fU s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (done_of_zero h.1.1.1 h0), WP.block_nil (done_of_zero h.1.2.1 (pub_U hq ▸ h0))⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1.2] at this; simpa using this
  -- `save` reloaded, and the registers restored.
  have r₅ := rel_agree (F := Done s₀) (F' := Done s₀') (G := fun _ => True) (G' := fun _ => True)
    (argTaint [] 12)
    (fun a b ha hb => agreeAt hp hp' hq ha.sp hb.sp ha.wr hb.wr (big_frame ha.frame) (big_frame hb.frame)
      fun r hr => by simp at hr) end_taint
    (fun _ h => WP.mono (final_end_wp hp h) fun _ _ => trivial)
    (fun _ h => WP.mono (final_end_wp hp' h) fun _ _ => trivial)
  exact (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem final_ct : ConstantTime isa ctrFinalArm.pre ctrFinalArm.pub cryptFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem cryptFinal_verified : Verified Arm.target cryptFinal finalScratchContract :=
  Verified.of_correct final_correct final_ct final_implies

/-! ## With `save` on the stack

The final function has two stack arguments, so `save` is its third: it runs
its code in a frame of 72 bytes (`withStackScratchWiped`): the copies of the
two stack arguments, `save`'s address, the word holding `lr`, and `save`'s
56 bytes, the block included, which it zeroes before returning. The code's
calls use 16 bytes below it, so 88 in all. -/

/-- A state satisfying the precondition, without `save`. -/
def ctrFrameSat : State :=
  { finalSat with rd := [⟨0x1000, 240⟩, ⟨0x8000, 8⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩] }

theorem frameSat_pre : ∃ s, (finalRoundsContract Arm.abi 88).pre s := by
  implies_sat [finalRoundsContract, Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [ctrFrameSat, finalSat] using ctrFrameSat

/-- `cryptFinal`, with `save` on the stack (zeroed on return). -/
theorem cryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 72 2 14 cryptFinal)
      (finalRoundsContract Arm.abi 88) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Ctr.aesFinalSig) (nm := "save") (e := .u64) (n := 7)
    (pre := finalPre Arm.abi.ptrBits) (post := finalPost Arm.abi.ptrBits) (wa := false) (stack := 16)
    (m := 2) (bytes := 72) cryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (finalPre_local _) (finalPost_local _) (finalPost_localOut _) frameSat_pre (hleak := (finalLeak_local _).toL)

end VG.Proof.AesCtr.Arm
