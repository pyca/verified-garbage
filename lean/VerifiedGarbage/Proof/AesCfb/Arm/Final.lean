module

public import VerifiedGarbage.Impl.AesCfb.Arm.Final
public import VerifiedGarbage.Proof.AesCfb.Final
public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Proof.AesCfb.Arm.Verified
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Proof.AesCbc.Arm.Loop
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.AesGcm.Arm.Callee
public import VerifiedGarbage.Proof.AesOcb.Arm.Callee
public import VerifiedGarbage.Proof.Modes.Arm.SeqFinal
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.AesOfb.Arm.Body
import VerifiedGarbage.Proof.AesCfb.Arm.Body
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Impl.AesCfb.Arm.Final
meta import VerifiedGarbage.Proof.AesCfb.Final
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Proof.AesCfb.Arm.Verified
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Impl.StackScratch.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Spill
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.AesCbc.Arm.Loop
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.AesGcm.Arm.Callee
meta import VerifiedGarbage.Proof.AesOcb.Arm.Callee
meta import VerifiedGarbage.Proof.Modes.Arm.SeqFinal
meta import VerifiedGarbage.Proof.Modes.Words
meta import VerifiedGarbage.Proof.AesOfb.Arm.Body
meta import VerifiedGarbage.Proof.AesCfb.Arm.Body
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.Exec

/-!
# AES-CFB128 of a message's last piece on ARMv7

`encryptFinal_framed` and `decryptFinal_framed`: `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final` (`Impl/AesCfb/Arm/Final.lean`) meet
`Proof.AesCfb.encryptFinalRoundsContract` (and `decrypt…`), from which the
shared contracts follow (`Proof.AesCfb.encryptFinal_keyed`).

The code is proven against `finalArm`, with a third stack argument `save`
for its caller's registers (`final_implies`: the shared contract with it,
`finalScratchContract`), as a caller of two verified functions, through their
contracts:

* `final_setup_wp`: `save`'s address loaded, the registers saved there, and
  the arguments set up (`Setup`);
* `whole_wp`: the whole-block function of the same direction
  (`Impl/AesCfb/Arm.lean`) on the `n = len / 16` whole blocks, in a frame
  that pushes its stack arguments, from its contract (`modeArm (cfbMode enc)`,
  `FrameStack.WP.callF`), with the regions it is given (`whole_pre`): the
  blocks and the chaining value the mode's (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, `vg_aes_encrypt_blocks`
  on the chaining value in place (`final_ivArgs_wp`, `AesOcb.Arm.blk_call`,
  `final_ciph`), and its first `u` bytes XORed into them by the modes' loop
  (`Modes.Arm.xorLoop_wp`, `final_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers restored from `save`, whose address on the
  stack and slots nothing else wrote;
* `final_post`: `Done` gives `Spec.Cfb.EncryptFinal` (or `DecryptFinal`), by
  `Proof.AesCfb.encryptFinal_of`.

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
their contracts' constant time (`RelCT.call` in `whole_rel`,
`AesOcb.Arm.blk_rel`), every address and branch from the pointers and `len`,
which agree in both runs. `encryptFinal_framed` runs the code with `save` in
a frame of 56 bytes on the stack (`Arm.Verified.stackScratchWiped`), zeroed
on return.
-/

@[expose] public section

namespace VG.Proof.AesCfb.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)

/-- The code's contract, with the arguments `(schedule = r0, rounds = r1,
iv = r2, data = r3, len = [sp], scratch = [sp + 4], save = [sp + 8])`: in
direction `enc`, the data and the block at `iv` as `Spec.Cfb.EncryptFinal`
(or `DecryptFinal`) says, by AES with the key schedule it is given. -/
def finalArm (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let iv : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let sv : Region := ⟨State.addr (stackArg s 2), 40⟩
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
      (stackArg s 2).toNat + 40 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let ciph := ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    if enc then
      Spec.Cfb.EncryptFinal ciph 16 s.mem s'.mem (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3))
        (stackArg s 0).toNat
    else
      Spec.Cfb.DecryptFinal ciph 16 s.mem s'.mem (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3))
        (stackArg s 0).toNat
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2

/-- The postcondition in direction `enc`. -/
abbrev finalPost (enc : Bool) : Spec.Cfb.aesFinalSig.Post Arm.abi.ptrBits :=
  if enc then encryptFinalPost Arm.abi.ptrBits else decryptFinalPost Arm.abi.ptrBits

/-- The contract the frame needs: the shared one, with `save`, 40 bytes, as
a seventh argument, and 16 bytes of stack (the whole-block function's frame
and the one it pushes around its calls). -/
abbrev finalScratchContract (enc : Bool) : Contract isa :=
  Sig.scratchContract Arm.abi Spec.Cfb.aesFinalSig "save" .u64 5 (finalPre Arm.abi.ptrBits)
    (finalPost enc) false 16

/-- A state satisfying the precondition: the schedule at `0x1000`, 10
rounds, the block at `0x2000`, no data at `0x3000`, the scratch buffer at
`0x4000` and `save` at `0x6000` (the stack arguments at `0x8000`). -/
def finalSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8005 then 0x40 else if a = 0x8009 then 0x60 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x8000, 12⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 40⟩]

theorem final_implies (enc : Bool) : (finalArm enc).Implies (finalScratchContract enc) := by
  cases enc <;>
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Cfb.aesFinalSig, finalPre, finalPost, encryptFinalPost, decryptFinalPost, finalArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finalSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finalSat


/-! ## The arguments, by name -/

section
variable (s₀ : State)

abbrev fW : BitVec 32 := s₀.gpr .r0
abbrev fR : Nat := (s₀.gpr .r1).toNat
abbrev fIv : BitVec 32 := s₀.gpr .r2
abbrev fD : BitVec 32 := s₀.gpr .r3
abbrev fL : Nat := (stackArg s₀ 0).toNat
abbrev fS : BitVec 32 := stackArg s₀ 1
abbrev fV : BitVec 32 := stackArg s₀ 2
/-- The number of whole blocks, and of the bytes after them. -/
abbrev fN : Nat := fL s₀ / 16
abbrev fU : Nat := fL s₀ % 16
/-- The data after the whole blocks, as a register holds it and as an
address. -/
abbrev fT : BitVec 32 := fD s₀ + BitVec.ofNat 32 (16 * fN s₀)
abbrev fTa : Addr := State.addr (fD s₀) + BitVec.ofNat 64 (16 * fN s₀)

abbrev fSch : Region := ⟨State.addr (fW s₀), 240⟩
abbrev fIvR : Region := ⟨State.addr (fIv s₀), 16⟩
abbrev fData : Region := ⟨State.addr (fD s₀), fL s₀⟩
abbrev fBlk : Region := ⟨State.addr (fD s₀), 16 * fN s₀⟩
abbrev fTail : Region := ⟨fTa s₀, fU s₀⟩
abbrev fScr : Region := ⟨State.addr (fS s₀), 2176⟩
abbrev fSv : Region := ⟨State.addr (fV s₀), 40⟩
abbrev fArg : Region := ⟨stackArgAddr s₀ 0, 12⟩
abbrev fStk : Region := ⟨State.addr s₀.sp - BitVec.ofNat 64 16, 16⟩

/-- The key schedule, the chaining value and the whole blocks on entry. -/
abbrev fWk : List Byte := bytesAt s₀.mem (State.addr (fW s₀)) (16 * (fR s₀ + 1))
abbrev fIv0 : List Byte := bytesAt s₀.mem (State.addr (fIv s₀)) 16
abbrev fBlks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (State.addr (fD s₀)) (fN s₀)

/-- The memory once the registers are saved. -/
abbrev svMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (State.addr (fV s₀)) s₀.gpr Impl.AesCfb.Arm.finalSaved

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  sp_lo : 16 ≤ s₀.sp.toNat
  sp_hi : s₀.sp.toNat + 12 ≤ 2 ^ 32
  rd : s₀.rd = [fSch s₀, fArg s₀]
  wr : s₀.wr = [fIvR s₀, fData s₀, fScr s₀, fSv s₀]
  sch_iv : (fSch s₀).Disjoint (fIvR s₀)
  sch_data : (fSch s₀).Disjoint (fData s₀)
  sch_scr : (fSch s₀).Disjoint (fScr s₀)
  sch_sv : (fSch s₀).Disjoint (fSv s₀)
  iv_data : (fIvR s₀).Disjoint (fData s₀)
  iv_scr : (fIvR s₀).Disjoint (fScr s₀)
  iv_sv : (fIvR s₀).Disjoint (fSv s₀)
  iv_arg : (fIvR s₀).Disjoint (fArg s₀)
  data_scr : (fData s₀).Disjoint (fScr s₀)
  data_sv : (fData s₀).Disjoint (fSv s₀)
  data_arg : (fData s₀).Disjoint (fArg s₀)
  scr_sv : (fScr s₀).Disjoint (fSv s₀)
  scr_arg : (fScr s₀).Disjoint (fArg s₀)
  sv_arg : (fSv s₀).Disjoint (fArg s₀)
  stk_sch : (fStk s₀).Disjoint (fSch s₀)
  stk_iv : (fStk s₀).Disjoint (fIvR s₀)
  stk_data : (fStk s₀).Disjoint (fData s₀)
  stk_scr : (fStk s₀).Disjoint (fScr s₀)
  stk_sv : (fStk s₀).Disjoint (fSv s₀)
  stk_arg : (fStk s₀).Disjoint (fArg s₀)
  sch_fit : (fW s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (fIv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (fD s₀).toNat + fL s₀ ≤ 2 ^ 32
  scr_fit : (fS s₀).toNat + 2176 ≤ 2 ^ 32
  sv_fit : (fV s₀).toNat + 40 ≤ 2 ^ 32
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem FPre.of {enc : Bool} {s₀ : State} (h : (finalArm enc).pre s₀) : FPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30⟩

/-! ## Regions -/

open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_and wp_cmp wp_ldrSp eval_eq eval_ne
  ofNat_beq_zero)
open VG.Impl.AesCfb.Arm

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)

theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])

theorem fL_lt (s₀ : State) : fL s₀ < 2 ^ 32 := (stackArg s₀ 0).isLt

theorem fU_lt (s₀ : State) : fU s₀ < 16 := Nat.mod_lt _ (by decide)

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [fN_eq, fU_eq]; omega)

theorem FPre.blk_fit : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 32 := by
  have := hp.data_fit; have := Nat.mul_div_le (fL s₀) 16; rw [fN_eq]; omega

theorem FPre.sched_sub : Region.Sub ⟨State.addr (fW s₀), 16 * (fR s₀ + 1)⟩ (fSch s₀) :=
  Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)

theorem FPre.sched_len : 16 * (fR s₀ + 1) ≤ 2 ^ 64 := by
  rcases hp.rounds with h | h | h <;> omega

/-- The stack arguments' addresses. -/
theorem FPre.argAddr {k : Nat} (hk : k < 3) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_hi
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem FPre.arg_in {k : Nat} (hk : k < 3) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨fArg s₀, by simp [hp.rd], ?_⟩
  rw [hp.argAddr hk]
  exact Offset.contains_base _ (by omega) (by omega)

/-- The tail, as `r7` holds it. -/
theorem FPre.tail_lt (hu : fU s₀ ≠ 0) : (fD s₀).toNat + 16 * fN s₀ < 2 ^ 32 := by
  have := hp.data_fit; have := Nat.div_add_mod (fL s₀) 16; rw [fN_eq]; rw [fU_eq] at hu; omega

theorem FPre.tailA (hu : fU s₀ ≠ 0) : State.addr (fT s₀) = fTa s₀ := addr_add (hp.tail_lt hu)

theorem FPre.tail_toNat (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.tail_lt hu
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

end

/-- The save changes only `save`. -/
theorem svMem_frame (s₀ : State) : Frame [fSv s₀] s₀.mem (svMem s₀) :=
  Spill.saveMem_frame _ _ _ (L := 40) (by decide) finalSaved (by decide)

/-- The stack arguments survive the save. -/
theorem FPre.svArg {s₀ : State} (hp : FPre s₀) {k : Nat} (hk : k < 3) :
    (svMem s₀).readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := by
  refine (svMem_frame s₀).readW (r := fArg s₀) ?_ (fun r hr => ?_) (by decide)
  · rw [hp.argAddr hk]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr; exact hp.sv_arg.symm

/-! ## Saving the registers -/

theorem shr4 (x : BitVec 32) : x >>> 4 = BitVec.ofNat 32 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem and15 (x : BitVec 32) : x &&& 15#32 = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : Nat) % 2 ^ 32 = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shl4 {n : Nat} (h : 16 * n < 2 ^ 32) : BitVec.ofNat 32 n <<< 4 = BitVec.ofNat 32 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (a := n) (by omega)]
  omega

/-- What saving the registers and setting up the arguments leaves. -/
structure Setup (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = fW s₀
  r1 : s.gpr .r1 = s₀.gpr .r1
  r2 : s.gpr .r2 = fIv s₀
  r3 : s.gpr .r3 = fD s₀
  r4 : s.gpr .r4 = fW s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = fIv s₀
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  r10 : s.gpr .r10 = fS s₀
  r12 : s.gpr .r12 = BitVec.ofNat 32 (fN s₀)
  lr : s.gpr .lr = fS s₀
  sp : s.sp = s₀.sp
  mem : s.mem = svMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finalMoves_eq : finalMoves =
    [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2), .ldrSp .r8 0, .ldrSp .r10 4,
     .mov .r12 (.shifted .r8 .lsr 4), .dp .and .r8 .r8 (.imm 15), .dp .add .r7 .r3 (.shifted .r12 .lsl 4),
     .mov .lr (.reg .r10)] := rfl

theorem final_setup_wp {s₀ : State} (hp : FPre s₀) : WP isa (.block finalSetup) s₀ (Setup s₀) := by
  show WP isa (.block (.ldrSp .r12 8 :: (finalSave ++ finalMoves))) s₀ _
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have r12₁ : s₁.gpr .r12 = fV s₀ := u₁.gpr
  have sv := hp.sv_fit
  refine Spill.save_slots_ok (lo := 0) (hi := 36) (by decide) (by rw [r12₁]; omega) (fun d _ hd => ?_) ?_
  · rw [u₁.wr, hp.wr, r12₁]
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
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
  exact {
    r0 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), keep₂ _ (by decide)]
    r1 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), keep₂ _ (by decide)]
    r2 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), keep₂ _ (by decide)]
    r3 := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), keep₂ _ (by decide)]
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
        u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), keep₂ _ (by decide)]
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


/-! ## The call of the whole-block function -/

open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.Arm (modeArm)
open VG.Proof.AesGcm.Arm (below toNat_ofNat32 pushed_sp8 hspA hA fA view_gpr view_sp arg0 arg1 argAddr0
  cover_pushed cover_pushed' cover_frame covers_append' stackArg_callEntry stackArgAddr_callEntry)
open VG.Arm.FrameStack (armStack belowA)

/-- The `n` blocks at `D` are unchanged outside a frame that misses them. -/
theorem blocksAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨D, 16 * n⟩ : Region).Disjoint r) :
    Spec.Cbc.blocksAt m' D n = Spec.Cbc.blocksAt m D n :=
  List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame hf
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; omega))) (by decide)

/-- The 8 bytes below the stack pointer, and the 8 below those, are in the
16 the contract reserves. -/
theorem below8_sub (s₀ : State) : Region.Sub (below s₀.sp) (fStk s₀) :=
  Offset.sub_below _ (by decide) (by decide)

theorem below16_sub {s₀ : State} (hp : FPre s₀) :
    Region.Sub (belowA (s₀.sp - BitVec.ofNat 32 8) 8) (fStk s₀) := by
  have := hp.sp_lo
  show Region.Sub ⟨State.addr (s₀.sp - BitVec.ofNat 32 8 - BitVec.ofNat 32 8), 8⟩ _
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat, FrameStack.addr_sub' (by omega)]
  exact Region.sub_prefix (by decide)

theorem below16_sub' {s₀ : State} (hp : FPre s₀) :
    Region.Sub ⟨State.addr (s₀.sp - 8) - BitVec.ofNat 64 8, 8⟩ (fStk s₀) := by
  have := hp.sp_lo
  rw [hA (s := s₀) (by omega), show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.sub_sub,
    BitVec.ofNat_add_ofNat]
  exact Region.sub_prefix (by decide)

/-- The regions the whole-block function is given. -/
abbrev wRd (s₀ : State) : List Region := [fSch s₀, ⟨State.addr s₀.sp - 8, 8⟩]
abbrev wWr (s₀ : State) : List Region := [fIvR s₀, fBlk s₀, fScr s₀]

theorem toNat_N (s₀ : State) : (BitVec.ofNat 32 (fN s₀)).toNat = fN s₀ :=
  toNat_ofNat32 (by have := fL_lt s₀; rw [fN_eq]; omega)

theorem whole_pre {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Setup s₀ s) :
    (modeArm M).pre ((pushed [.r12, .lr] s).callEntry.withRegions (wRd s₀) (wWr s₀)) := by
  have hsp : 8 ≤ s.sp.toNat := by rw [h.sp]; have := hp.sp_lo; omega
  have hR := toNat_ofNat32 (n := fR s₀) (by rcases hp.rounds with h' | h' | h' <;> omega)
  simp only [modeArm, view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide),
    view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1, h.r2, h.r3,
    State.withRegions_rd, State.withRegions_wr, view_sp, stackArgAddr_withRegions, stackArg_withRegions,
    stackArg_callEntry, stackArgAddr_callEntry, arg0 hsp, arg1 hsp, argAddr0 hsp, h.r12, h.lr, toNat_N, h.sp,
    hspA (s := s₀) (by have := hp.sp_lo; omega)]
  have b8 := below8_sub s₀
  have b16 := below16_sub' hp
  refine ⟨trivial, trivial, hp.sch_iv, hp.sch_data.sub_right (blk_sub s₀), hp.sch_scr,
    hp.iv_data.sub_right (blk_sub s₀), hp.iv_scr, hp.data_scr.sub_left (blk_sub s₀),
    (hp.stk_iv.sub_left b8).symm, ((hp.stk_data.sub_left b8).sub_right (blk_sub s₀)).symm,
    (hp.stk_scr.sub_left b8).symm, hp.stk_sch.sub_left b16, hp.stk_iv.sub_left b16,
    (hp.stk_data.sub_left b16).sub_right (blk_sub s₀), hp.stk_scr.sub_left b16, hp.sch_fit, hp.iv_fit,
    hp.blk_fit, hp.scr_fit, by have := hp.sp_lo; omega, by have := s₀.sp.isLt; omega, hp.rounds⟩

theorem whole_cov {s₀ : State} (hp : FPre s₀) {s : State} (h : Setup s₀ s) :
    Covers (wRd s₀ ++ wWr s₀) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) ∧
      Covers (wWr s₀) (pushed [.r12, .lr] s).wr := by
  have hsp : 8 ≤ s.sp.toNat := by rw [h.sp]; have := hp.sp_lo; omega
  have cw : Covers (wWr s₀) s.wr := by
    rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩
  have cs : Covers [fSch s₀] (s.rd ++ s.wr) := by
    rw [h.rd, h.wr, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
  have e : wRd s₀ = [fSch s₀] ++ [⟨State.addr s.sp - 8, 8⟩] := by rw [h.sp]; rfl
  refine ⟨?_, cover_pushed cw⟩
  rw [e]
  exact covers_append' (covers_append' (cover_pushed' cs) (cover_frame hsp (by decide)))
    (cover_pushed' (Covers.right cw))

/-- The save and the push change only `save` and the stack. -/
theorem entry_frame {s₀ : State} (hp : FPre s₀) {s : State} (h : Setup s₀ s) :
    Frame [fSv s₀, fStk s₀] s₀.mem (pushed [.r12, .lr] s).mem := by
  have hsp : 8 ≤ s.sp.toNat := by rw [h.sp]; have := hp.sp_lo; omega
  have f₁ : Frame [fSv s₀, fStk s₀] s₀.mem s.mem := by
    rw [h.mem]; exact (svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
  have f₂ : Frame [fSv s₀, fStk s₀] s.mem (pushed [.r12, .lr] s).mem :=
    (fA hsp).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fStk s₀, by simp, by rw [h.sp]; exact below8_sub s₀⟩
  exact f₁.trans f₂

/-- What the call of the whole-block function leaves, for the mode `M`. -/
structure Whole (M : Mode) (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = fW s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = fIv s₀
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  r10 : s.gpr .r10 = fS s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fBlk s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  iv : bytesAt s.mem (State.addr (fIv s₀)) 16 = M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)

theorem whole_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeArm M).pre s → ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeArm M).post s s')
    (hd : armStack whole = 8) {s₀ : State} (hp : FPre s₀) {s : State} (h : Setup s₀ s) :
    WP isa (wholeFrame name whole) s (Whole M s₀) := by
  have hsp : 8 ≤ s.sp.toNat := by rw [h.sp]; have := hp.sp_lo; omega
  obtain ⟨hc, hw⟩ := whole_cov hp h
  have ef := entry_frame hp h
  have eW : bytesAt (pushed [.r12, .lr] s).mem (State.addr (fW s₀)) (16 * (fR s₀ + 1)) = fWk s₀ :=
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.sch_sv.sub_left hp.sched_sub
      · exact hp.stk_sch.symm.sub_left hp.sched_sub) hp.sched_len
  have eIv : bytesAt (pushed [.r12, .lr] s).mem (State.addr (fIv s₀)) 16 = fIv0 s₀ :=
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.iv_sv
      · exact hp.stk_iv.symm) (by decide)
  have eB : Spec.Cbc.blocksAt (pushed [.r12, .lr] s).mem (State.addr (fD s₀)) (fN s₀) = fBlks s₀ :=
    blocksAt_frame' ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_sv.sub_left (blk_sub s₀)
      · exact hp.stk_data.symm.sub_left (blk_sub s₀))
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using hsp) (by simp) ?_
  refine FrameStack.WP.callF (k := modeArm M) hv (rd := wRd s₀) (wr := wWr s₀) (whole_pre hp h) hc hw
    (by rw [hd, pushed_sp8, hspA hsp, h.sp]; have := hp.sp_lo; omega) ?_
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs hpost
  have hR := toNat_ofNat32 (n := fR s₀) (by rcases hp.rounds with h' | h' | h' <;> omega)
  simp only [modeArm, State.withRegions_mem, State.callEntry_mem, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0,
    h.r1, h.r2, h.r3, stackArg_withRegions, stackArg_callEntry, arg0 hsp, h.r12, toNat_N, eW, eIv, eB] at hpost
  have fr : Frame [fIvR s₀, fBlk s₀, fScr s₀, fStk s₀] (svMem s₀) s₂.mem := by
    rw [← h.mem]
    refine ((fA hsp).sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fStk s₀, by simp, by rw [h.sp]; exact below8_sub s₀⟩
    · rw [hd, pushed_sp8, h.sp] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨fStk s₀, by simp, below16_sub hp⟩
  have keep : ∀ r ∈ preserved, r ≠ .lr → (popped .r12 (4 * [Reg.r12, Reg.lr].length) s₂).gpr r = s.gpr r :=
    fun r hr hlr => by
    rw [popped_gpr (by rintro rfl; simp [preserved] at hr), hcs r hr hlr, pushed_gpr]
  exact ⟨by rw [keep .r4 (by simp [preserved]) (by decide), h.r4],
    by rw [keep .r5 (by simp [preserved]) (by decide), h.r5],
    by rw [keep .r6 (by simp [preserved]) (by decide), h.r6],
    by rw [keep .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [keep .r8 (by simp [preserved]) (by decide), h.r8],
    by rw [keep .r10 (by simp [preserved]) (by decide), h.r10],
    by rw [popped_sp, hsp₂, pushed_sp8, ← h.sp]; exact BitVec.sub_add_cancel _ _,
    by rw [popped_rd, hrd₂, pushed_rd, h.rd],
    by rw [popped_wr, hwr₂, pushed_wr]; exact h.wr,
    by rw [popped_mem]; exact fr, by rw [popped_mem]; exact hpost.1, by rw [popped_mem]; exact hpost.2⟩


/-! ## The partial last segment -/

open VG.Proof.AesOcb.Arm (BlkCall BlkPost blk_call encF)
open VG.Proof.Modes.Arm (XPre XInv XDone xorLoop_wp xf add0_32)

theorem Whole.of_fupd {M : Mode} {s₀ s s' : State} (h : Whole M s₀ s) (g : s'.gpr = s.gpr) (m : s'.mem = s.mem)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Whole M s₀ s' :=
  ⟨by rw [g, h.r4], by rw [g, h.r5], by rw [g, h.r6], by rw [g, h.r7], by rw [g, h.r8], by rw [g, h.r10],
    by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr], by rw [m]; exact h.frame, by rw [m]; exact h.blocks,
    by rw [m]; exact h.iv⟩

/-- The test sets Z if no bytes are left after the whole blocks. -/
theorem final_test_wp {M : Mode} {s₀ s : State} (h : Whole M s₀ s) :
    WP isa (.block [.cmp .r8 (.imm 0)]) s fun s' => Whole M s₀ s' ∧ s'.z = decide (fU s₀ = 0) :=
  wp_cmp (op2_imm (by decide)) fun s' f z => WP.block_nil ⟨h.of_fupd f.gpr f.mem f.rd f.wr f.sp, by
    rw [z, h.r8]; exact MdStream.Arm.cmp0 (by have := fU_lt s₀; omega)⟩

/-- What the function leaves before restoring the registers. -/
structure Done (M : Mode) (s₀ s : State) : Prop where
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fTa s₀ + BitVec.ofNat 64 q) = s₀.mem (fTa s₀ + BitVec.ofNat 64 q) ^^^
    (Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))).getD q 0
  iv : bytesAt s.mem (State.addr (fIv s₀)) 16 = if fU s₀ = 0 then M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
    else Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))

theorem Whole.frame' {M : Mode} {s₀ s : State} (h : Whole M s₀ s) :
    Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem :=
  h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem done_of_zero {M : Mode} {s₀ s : State} (h : Whole M s₀ s) (hu : fU s₀ = 0) : Done M s₀ s :=
  ⟨h.sp, h.rd, h.wr, h.frame', h.blocks, fun q hq => absurd hq (by omega), by rw [ite_eq_left hu]; exact h.iv⟩

/-- Everything the function writes, from entry. -/
theorem big_frame {s₀ : State} {m : Mem} (hf : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) m) :
    Frame [fIvR s₀, fData s₀, fScr s₀, fSv s₀, fStk s₀] s₀.mem m :=
  ((svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h])

theorem FPre.sched_big {s₀ : State} (hp : FPre s₀) :
    ∀ r ∈ [fIvR s₀, fData s₀, fScr s₀, fSv s₀, fStk s₀],
      (⟨State.addr (fW s₀), 16 * (fR s₀ + 1)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left hp.sched_sub
  · exact hp.sch_data.sub_left hp.sched_sub
  · exact hp.sch_scr.sub_left hp.sched_sub
  · exact hp.sch_sv.sub_left hp.sched_sub
  · exact hp.stk_sch.symm.sub_left hp.sched_sub

/-- What the code before the call of the block function leaves. -/
structure IvA (s₀ s s₁ : State) : Prop where
  pre : BlkCall s₁ (fW s₀) (fIv s₀) (fS s₀) (fR s₀) 1
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = s.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem final_ivArgs_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.block Impl.AesOfb.Arm.ivArgs) s (IvA s₀ s) := by
  rw [AesOfb.Arm.ivArgs_eq]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₅.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h12 => by
      rw [u₅.other _ h12, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  have sp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hb : below s₅.sp = below s₀.sp := by rw [sp₅, h.sp]
  have b8 := below8_sub s₀
  refine ⟨⟨?_, ?_, ?_, by rw [u₅.other _ (by decide), u₄.gpr]; rfl, ?_, hp.rounds,
    by rw [sp₅, h.sp]; have := hp.sp_lo; omega, hp.sch_fit, by have := hp.iv_fit; omega,
    by have := hp.scr_fit; omega, hp.sch_iv, hp.sch_scr.sub_right (Region.sub_prefix (by decide)),
    hp.iv_scr.sub_right (Region.sub_prefix (by decide)), by rw [hb]; exact hp.stk_sch.sub_left b8,
    by rw [hb]; exact hp.stk_iv.sub_left b8,
    by rw [hb]; exact (hp.stk_scr.sub_left b8).sub_right (Region.sub_prefix (by decide)), ?_, ?_⟩, keep, sp₅,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      h.r4]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      h.r5]; simp [fR]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      h.r6]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.r10]
  · rw [rd₅, wr₅, h.rd, h.wr, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₅, h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩

/-- What the call of the block function on the chaining value leaves. -/
structure Ciph (M : Mode) (s₀ s : State) : Prop where
  r6 : s.gpr .r6 = fIv s₀
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tailb : ∀ q < fU s₀, s.mem (fTa s₀ + BitVec.ofNat 64 q) = s₀.mem (fTa s₀ + BitVec.ofNat 64 q)
  iv : bytesAt s.mem (State.addr (fIv s₀)) 16 =
    Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))

theorem final_ciph {M : Mode} {s₀ : State} (hp : FPre s₀) {s s₁ s₂ : State} (h : Whole M s₀ s)
    (a : IvA s₀ s s₁) (c : BlkPost encF s₁ (fW s₀) (fIv s₀) (fS s₀) (fR s₀) 1 s₂) : Ciph M s₀ s₂ := by
  have kept : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = s.gpr r := fun r hr hlr => by
    rw [c.saved r hr hlr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact (hlr rfl).elim | exact a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have stk : Region.Sub (below s₁.sp) (fStk s₀) := by rw [a.sp, h.sp]; exact below8_sub s₀
  have fc : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] s₁.mem s₂.mem :=
    c.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨fScr s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨fStk s₀, by simp, stk⟩
  have f₁ : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) s₁.mem := by rw [a.mem]; exact h.frame'
  have big := big_frame f₁
  have tailD : ∀ r ∈ [(⟨State.addr (fIv s₀), 16 * 1⟩ : Region), ⟨State.addr (fS s₀), 2048⟩, below s₁.sp],
      (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
    · exact (hp.data_scr.sub_left (tail_sub s₀)).sub_right (Region.sub_prefix (by decide))
    · exact (hp.stk_data.sub_right (tail_sub s₀)).symm.sub_right stk
  have tailW : ∀ r ∈ [fIvR s₀, fBlk s₀, fScr s₀, fStk s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
    · exact hp.blk_tail.symm
    · exact hp.data_scr.sub_left (tail_sub s₀)
    · exact (hp.stk_data.sub_right (tail_sub s₀)).symm
  have tailS : ∀ r ∈ [fSv s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.data_sv.sub_left (tail_sub s₀)
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; have := fU_lt s₀; omega
  refine ⟨by rw [kept .r6 (by simp [preserved]) (by decide), h.r6],
    by rw [kept .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [kept .r8 (by simp [preserved]) (by decide), h.r8], by rw [c.sp, a.sp, h.sp],
    by rw [c.rd, a.rd, h.rd], by rw [c.wr, a.wr, h.wr], f₁.trans fc, ?_, fun q hq => ?_, ?_⟩
  · rw [blocksAt_frame' c.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.iv_data.symm.sub_left (blk_sub s₀))
      · exact (hp.data_scr.sub_left (blk_sub s₀)).sub_right (Region.sub_prefix (by decide))
      · exact (hp.stk_data.sub_right (blk_sub s₀)).symm.sub_right stk, a.mem]
    exact h.blocks
  · rw [c.frame.bytes tailD hlen hq, a.mem, h.frame.bytes tailW hlen hq, (svMem_frame s₀).bytes tailS hlen hq]
  · rw [AesCbc.bytesAt_of_statesAt c.out, show encF.f = Spec.Aes.cipher from rfl, ← AesCbc.aesWith_state,
      Proof.Cmac.bytesAt_frame big hp.sched_big hp.sched_len, a.mem, h.iv]


theorem final_xor_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Ciph M s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block [Impl.CmacAes.Arm.mov .r0 .r6, Impl.CmacAes.Arm.mov .r6 .r7,
      Impl.CmacAes.Arm.mov .r7 .r8]) (.loop (.block Impl.Modes.Arm.xorByte) .ne)) s (Done M s₀) := by
  show WP isa (.seq (.block [.mov .r0 (.reg .r6), .mov .r6 (.reg .r7), .mov .r7 (.reg .r8)]) _) s _
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ?_)
  have hU := fU_lt s₀
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_fit
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have hT := hp.tail_toNat hu
  have aT := hp.tailA hu
  have r0₃ : s₃.gpr .r0 = fIv s₀ := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r6]
  have r6₃ : s₃.gpr .r6 = fT s₀ := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.r7]
  have r7₃ : s₃.gpr .r7 = BitVec.ofNat 32 (fU s₀) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r8]
  have mem₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  have sp₃ : s₃.sp = s₀.sp := by rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  have xp : XPre s₃ (fIv s₀) (fT s₀) (fU s₀) := {
    pos := by omega
    fK := by have := hp.iv_fit; omega
    fR := by rw [hT]; omega
    disj := by rw [aT]; exact (hp.iv_data.sub_left (Region.sub_prefix (by omega))).sub_right (tail_sub s₀)
    rdK := by
      rw [rd₃, wr₃, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨fIvR s₀, by simp, 0, by simp, by simp; omega⟩
    wrR := by
      rw [wr₃, hp.wr, aT]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨fData s₀, by simp, 16 * fN s₀, rfl, by simp only; omega⟩ }
  have x0 : XInv s₃ (fIv s₀) (fT s₀) (fU s₀) 0 s₃ :=
    ⟨by rw [add0_32, r0₃], by rw [add0_32, r6₃], by rw [Nat.sub_zero, r7₃], by omega,
      (Proof.Modes.over_zero _ _ _).symm, rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl⟩
  refine WP.mono (xorLoop_wp xp x0) fun s' d => ?_
  have fo : Frame [fTail s₀] s₃.mem s'.mem := by rw [d.mem, aT]; exact Proof.Modes.over_frame _ _ _ _
  have ivT : ∀ r ∈ [fTail s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.sub_right (tail_sub s₀)
  refine ⟨by rw [d.sp, sp₃], by rw [d.rd, rd₃], by rw [d.wr, wr₃], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact h.frame.trans (by
      rw [← mem₃]
      exact fo.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' fo fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail, mem₃]
    exact h.blocks
  · rw [d.mem, ← aT, Proof.Modes.over_at hq (by omega), aT, mem₃]
    show s.mem (fTa s₀ + BitVec.ofNat 64 q) ^^^ s.mem (State.addr (fIv s₀) + BitVec.ofNat 64 q) = _
    rw [h.tailb q hq, MdStream.Arm.bytesAt_getD h.iv (show q < 16 by omega)]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame fo ivT (by decide), mem₃, h.iv]

theorem final_mid_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s)
    (hz : s.z = decide (fU s₀ = 0)) :
    WP isa (.ite .eq (.block []) finalTail) s (Done M s₀) := by
  have ev : isa.eval .eq s = some (decide (fU s₀ = 0)) := by show VG.Arm.eval .eq s = _; rw [eval_eq, hz]
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [ev, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [ev, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (final_ivArgs_wp hp h) fun _ a =>
      WP.seq (WP.mono (blk_call encF a.pre) fun _ c => final_xor_wp hp (final_ciph hp h a c) hu))

/-! ## Restoring the registers -/

/-- The stack arguments are unchanged when the registers are restored. -/
theorem Done.arg {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Done M s₀ s) {k : Nat} (hk : k < 3) :
    s.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := by
  refine (big_frame h.frame).readW (r := fArg s₀) ?_ (fun r hr => ?_) (by decide)
  · rw [hp.argAddr hk]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.iv_arg.symm
    · exact hp.data_arg.symm
    · exact hp.scr_arg.symm
    · exact hp.sv_arg.symm
    · exact hp.stk_arg.symm

theorem preserved_saved : ∀ r ∈ preserved, r ∈ finalSaved.map Prod.fst := by decide

theorem final_end_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Done M s₀ s) :
    WP isa (.block finalEnd) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  show WP isa (.block (.ldrSp .r12 8 :: finalRestore)) s _
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) (by rw [h.sp]; rfl)
    (by rw [h.rd, h.wr]; exact hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have r12 : s₁.gpr .r12 = fV s₀ := by rw [u₁.gpr]; exact h.arg hp (by decide)
  have sv := hp.sv_fit
  have hs : Spill.Saved s₁.mem (State.addr (s₁.gpr .r12)) s₀.gpr finalSaved := by
    rw [u₁.mem, r12]
    refine (Spill.saveMem_saved (lo := 0) (hi := 36) _ _ _ _ (by decide)).frame (lo := 0) (hi := 36) (by decide) h.frame
      fun r hr => ?_
    have hsub : Region.Sub ⟨State.addr (fV s₀) + BitVec.ofNat 64 0, 36 - 0⟩ (fSv s₀) := Offset.sub_base _ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_sv.symm.sub_left hsub
    · exact hp.data_sv.symm.sub_left hsub
    · exact hp.scr_sv.symm.sub_left hsub
    · exact hp.stk_sv.symm.sub_left hsub
  refine WP.mono (Spill.restore_block_ok (b := .r12) (lo := 0) (hi := 36) (by decide) (by decide)
    (by rw [r12]; omega) (fun d _ hd => ?_) hs) fun s' ⟨g, _, m, _, _, sp⟩ => ?_
  · rw [u₁.rd, u₁.wr, h.rd, h.wr, r12]
    exact ⟨fSv s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨⟨fun r hr => Spill.restored_reg g (preserved_saved r hr), by rw [sp, u₁.sp, h.sp]⟩, by rw [m, u₁.mem]⟩

/-! ## The whole function -/

theorem final_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeArm M).pre s → ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeArm M).post s s')
    (hd : armStack whole = 8) {s₀ : State} (hp : FPre s₀) :
    WP isa (final name whole) s₀ fun s' => abiPreserved s₀ s' ∧ ∃ s₁, Done M s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hv hd hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_test_wp h₂) fun s₃ ⟨h₃, z₃⟩ => ?_)
  refine WP.seq (WP.mono (final_mid_wp hp h₃ z₃) fun s₄ h₄ => ?_)
  exact WP.mono (final_end_wp hp h₄) fun _ ⟨g, m⟩ => ⟨g, s₄, h₄, m⟩

/-- The specification's results, from what the function leaves. -/
theorem final_post {enc : Bool} {s₀ s₁ s' : State} (h : Done (cfbMode enc) s₀ s₁) (hm : s'.mem = s₁.mem) :
    (finalArm enc).post s₀ s' := by
  cases enc
  · show Spec.Cfb.DecryptFinal (ciphAt s₀.mem (State.addr (fW s₀)) (fR s₀)) 16 s₀.mem s'.mem
      (State.addr (fIv s₀)) (State.addr (fD s₀)) (fL s₀)
    exact decryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)
  · show Spec.Cfb.EncryptFinal (ciphAt s₀.mem (State.addr (fW s₀)) (fR s₀)) 16 s₀.mem s'.mem
      (State.addr (fIv s₀)) (State.addr (fD s₀)) (fL s₀)
    exact encryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)

theorem final_correct {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeArm (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeArm (cfbMode enc)).post s s')
    (hd : armStack whole = 8) (s : State) (hs : (finalArm enc).pre s) :
    ∃ t s', Exec isa (final name whole) s t s' ∧ abiPreserved s s' ∧ (finalArm enc).post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp (M := cfbMode enc) hv hd (FPre.of hs)
  exact ⟨t, s', he, hg, final_post h₁ hm⟩


/-! ## Constant time -/

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (finalArm enc).pub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_W : fW s₀ = fW s₀' := hq.2.1
theorem pub_r1 : s₀.gpr .r1 = s₀'.gpr .r1 := hq.2.2.1
theorem pub_Iv : fIv s₀ = fIv s₀' := hq.2.2.2.1
theorem pub_D : fD s₀ = fD s₀' := hq.2.2.2.2.1
theorem pub_L : stackArg s₀ 0 = stackArg s₀' 0 := hq.2.2.2.2.2.1
theorem pub_S : fS s₀ = fS s₀' := hq.2.2.2.2.2.2.1
theorem pub_V : fV s₀ = fV s₀' := hq.2.2.2.2.2.2.2
theorem pub_R : fR s₀ = fR s₀' := by rw [fR, fR, pub_r1 hq]
theorem pub_N : fN s₀ = fN s₀' := by rw [fN, fN, fL, fL, pub_L hq]
theorem pub_U : fU s₀ = fU s₀' := by rw [fU, fU, fL, fL, pub_L hq]
theorem pub_T : fT s₀ = fT s₀' := by rw [fT, fT, pub_D hq, pub_N hq]
theorem pub_wRd : wRd s₀ = wRd s₀' := by rw [wRd, wRd, fSch, fSch, pub_W hq, pub_sp hq]
theorem pub_wWr : wWr s₀ = wWr s₀' := by
  rw [wWr, wWr, fIvR, fIvR, fBlk, fBlk, fScr, fScr, pub_Iv hq, pub_D hq, pub_N hq, pub_S hq]

end

/-- The whole-block function's calls in two runs from agreeing arguments are
constant time, by its contract's. -/
theorem whole_rel {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeArm M).pre s → ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeArm M).post s s')
    (hct : ConstantTime isa (modeArm M).pre (modeArm M).pub whole) {enc : Bool} {s₀ s₀' : State}
    (hp : FPre s₀) (hp' : FPre s₀') (hq : (finalArm enc).pub s₀ s₀') :
    RelCT isa (fun a b => Setup s₀ a ∧ Setup s₀' b) (wholeFrame name whole) fun _ _ => True := by
  refine RelCT.frame (fun a b h => by rw [h.1.sp, h.2.sp, pub_sp hq]) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, ⟨h₁, h₂⟩, pa, pb⟩ e₁ e₂
  have hsp₁ : 8 ≤ s₁.sp.toNat := by rw [h₁.sp]; have := hp.sp_lo; omega
  have hsp₂ : 8 ≤ s₂.sp.toNat := by rw [h₂.sp]; have := hp'.sp_lo; omega
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using hsp₁), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using hsp₂), Option.some.injEq] at pb
  subst pa pb
  refine RelCT.call (k := modeArm M) hv hct (wRd s₀) (wWr s₀)
    (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₂ := whole_pre (M := M) hp' h₂
  have c₂ := whole_cov hp' h₂
  rw [← pub_wRd hq, ← pub_wWr hq] at p₂ c₂
  refine ⟨whole_pre hp h₁, p₂, ?_, (whole_cov hp h₁).1, (whole_cov hp h₁).2, c₂.1, c₂.2⟩
  simp only [modeArm, stackArg_withRegions, stackArg_callEntry, arg0 hsp₁, arg1 hsp₁, arg0 hsp₂, arg1 hsp₂,
    view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide),
    view_gpr _ _ _ .r3 (by decide), view_sp, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₁.lr, h₁.sp, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, h₂.r12, h₂.lr, h₂.sp, pub_sp hq, pub_W hq, pub_r1 hq, pub_Iv hq, pub_D hq, pub_N hq, pub_S hq]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

theorem setup_taint :
    ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 12) (.block finalSetup) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem test_taint : ∃ h, (taint.check (Taint.ofRegs [.r8]) (.block [.cmp .r8 (.imm 0)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem ivArgs_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block Impl.AesOfb.Arm.ivArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (Taint.ofRegs [.r6, .r7, .r8])
    (.seq (.block [Impl.CmacAes.Arm.mov .r0 .r6, Impl.CmacAes.Arm.mov .r6 .r7, Impl.CmacAes.Arm.mov .r7 .r8])
      (.loop (.block Impl.Modes.Arm.xorByte) .ne)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

theorem end_taint : ∃ h, (taint.check (argTaint [] 12) (.block finalEnd) h).isSome = true := ⟨_, by taint_decide⟩

/-- The arguments' area, apart from what may be written. -/
theorem FPre.argsWf {s₀ : State} (hp : FPre s₀) :
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

theorem final_rel {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeArm (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeArm (cfbMode enc)).post s s')
    (hct : ConstantTime isa (modeArm (cfbMode enc)).pre (modeArm (cfbMode enc)).pub whole)
    (hd : armStack whole = 8) {s₀ s₀' : State}
    (h0 : (finalArm enc).pre s₀) (h0' : (finalArm enc).pre s₀') (hq : (finalArm enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (final name whole) fun _ _ => True := by
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  let M := cfbMode enc
  -- The registers saved and the arguments set up.
  have r₁ := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := Setup s₀) (G' := Setup s₀')
    (argTaint [.r0, .r1, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) (pub_sp hq) hp.argsWf hp'.argsWf
        (argMem_of (j := 3) (pub_sp hq) hp.sp_hi fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact pub_W hq
        · exact pub_r1 hq
        · exact pub_Iv hq
        · exact pub_D hq
      · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact pub_L hq
        · exact pub_S hq
        · exact pub_V hq) setup_taint
    (fun s e => by rw [e]; exact final_setup_wp hp) (fun s e => by rw [e]; exact final_setup_wp hp')
  -- The whole blocks.
  have r₂ := rel_wp (F := Setup s₀) (F' := Setup s₀') (G := Whole M s₀) (G' := Whole M s₀')
    (whole_rel (name := name) hv hct hp hp' hq) (fun _ h => whole_wp hv hd hp h) (fun _ h => whole_wp hv hd hp' h)
  -- The test.
  have r₃ := rel_agree (F := Whole M s₀) (F' := Whole M s₀')
    (G := fun s => Whole M s₀ s ∧ s.z = decide (fU s₀ = 0)) (G' := fun s => Whole M s₀' s ∧ s.z = decide (fU s₀' = 0))
    (Taint.ofRegs [.r8]) (fun a b ha hb => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.r8, hb.r8, pub_U hq]) test_taint
    (fun _ h => final_test_wp h) (fun _ h => final_test_wp h)
  -- The partial last segment.
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole M s₀ a ∧ Whole M s₀' b) finalTail
      fun a b => Done M s₀ a ∧ Done M s₀' b := by
    have hu' : fU s₀' ≠ 0 := pub_U hq ▸ hu
    have a₁ := rel_agree (F := Whole M s₀) (F' := Whole M s₀')
      (G := fun s₁ => ∃ s, Whole M s₀ s ∧ IvA s₀ s s₁) (G' := fun s₁ => ∃ s, Whole M s₀' s ∧ IvA s₀' s s₁)
      (Taint.ofRegs []) (fun _ _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) ivArgs_taint
      (fun s h => WP.mono (final_ivArgs_wp hp h) fun _ a => ⟨s, h, a⟩)
      (fun s h => WP.mono (final_ivArgs_wp hp' h) fun _ a => ⟨s, h, a⟩)
    have a₂ := rel_wp (F := fun s₁ => ∃ s, Whole M s₀ s ∧ IvA s₀ s s₁)
      (F' := fun s₁ => ∃ s, Whole M s₀' s ∧ IvA s₀' s s₁) (G := Ciph M s₀) (G' := Ciph M s₀')
      (AesOcb.Arm.blk_rel encF fun a b ⟨⟨x, hx, ha⟩, ⟨y, hy, hb⟩⟩ =>
        ⟨fW s₀, fIv s₀, fS s₀, fR s₀, 1, ha.pre,
          by rw [pub_W hq, pub_Iv hq, pub_S hq, pub_R hq]; exact hb.pre,
          by rw [ha.sp, hb.sp, hx.sp, hy.sp, pub_sp hq]⟩)
      (fun _ ⟨_, hw, ha⟩ => WP.mono (blk_call encF ha.pre) fun _ c => final_ciph hp hw ha c)
      (fun _ ⟨_, hw, ha⟩ => WP.mono (blk_call encF ha.pre) fun _ c => final_ciph hp' hw ha c)
    have a₃ := rel_agree (F := Ciph M s₀) (F' := Ciph M s₀') (G := Done M s₀) (G' := Done M s₀')
      (Taint.ofRegs [.r6, .r7, .r8]) (fun a b ha hb => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [ha.r6, hb.r6, pub_Iv hq]
        · rw [ha.r7, hb.r7, pub_T hq]
        · rw [ha.r8, hb.r8, pub_U hq]) xor_taint
      (fun _ h => final_xor_wp hp h hu) (fun _ h => final_xor_wp hp' h hu')
    exact a₁.seq (a₂.seq a₃)
  have ev {s : State} {u : Nat} (h : s.z = decide (u = 0)) : isa.eval .eq s = some (decide (u = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have r₄ : RelCT isa (fun a b => (Whole M s₀ a ∧ a.z = decide (fU s₀ = 0)) ∧
      (Whole M s₀' b ∧ b.z = decide (fU s₀' = 0)))
      (.ite .eq (.block []) finalTail) (fun a b => Done M s₀ a ∧ Done M s₀' b) := by
    obtain ⟨_, hnil⟩ := nil_taint
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev h.2.2, pub_U hq]) ?_ ?_
    · refine ((RelCT.taint (A := taint) (Taint.ofRegs [])
        (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil).wp
        (F₁ := Done M s₀) (F₂ := Done M s₀') fun a b h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
      have h0 : fU s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (done_of_zero h.1.1.1 h0), WP.block_nil (done_of_zero h.1.2.1 (pub_U hq ▸ h0))⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1.2] at this; simpa using this
  -- `save` reloaded, and the registers restored.
  have r₅ := rel_agree (F := Done M s₀) (F' := Done M s₀') (G := fun _ => True) (G' := fun _ => True)
    (argTaint [] 12)
    (fun a b ha hb => by
      have wf : ∀ {σ s : State}, FPre σ → Done M σ s →
          s.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 12⟩ r := fun hσ hs => by
        rw [hs.sp, hs.wr]; exact hσ.argsWf
      have arg : ∀ {σ s : State}, FPre σ → Done M σ s → ∀ k < 3, stackArg s k = stackArg σ k :=
        fun {σ s} hσ hs k hk => by
          rw [stackArg, show stackArgAddr s k = stackArgAddr σ k by simp only [stackArgAddr, hs.sp]]
          exact hs.arg hσ hk
      refine agree_argTaint (fun r hr => by simp at hr) (by rw [ha.sp, hb.sp, pub_sp hq]) (wf hp ha) (wf hp' hb)
        (argMem_of (j := 3) (by rw [ha.sp, hb.sp, pub_sp hq]) (by rw [ha.sp]; exact hp.sp_hi) fun i hi => ?_)
      rw [arg hp ha i hi, arg hp' hb i hi]
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · exact pub_L hq
      · exact pub_S hq
      · exact pub_V hq) end_taint
    (fun _ h => WP.mono (final_end_wp hp h) fun _ _ => trivial)
    (fun _ h => WP.mono (final_end_wp hp' h) fun _ _ => trivial)
  exact (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem final_ct {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeArm (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeArm (cfbMode enc)).post s s')
    (hct : ConstantTime isa (modeArm (cfbMode enc)).pre (modeArm (cfbMode enc)).pub whole)
    (hd : armStack whole = 8) :
    ConstantTime isa (finalArm enc).pre (finalArm enc).pub (final name whole) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel hv hct hd h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1


/-! ## Verified -/

/-- Code without frames uses no stack below the stack pointer. -/
theorem armStack_noFrames : ∀ c : Prog isa, c.noFrames = true → armStack c = 0
  | .block _, _ => rfl
  | .seq a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [armStack, armStack_noFrames a h.1, armStack_noFrames b h.2, Nat.max_self]
  | .ite _ a b, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [armStack, armStack_noFrames a h.1, armStack_noFrames b h.2, Nat.max_self]
  | .loop b _, h => by
    simp only [Code.noFrames] at h
    simp only [armStack, armStack_noFrames b h]
  | .call _ b, h => by
    simp only [Code.noFrames] at h
    simp only [armStack, armStack_noFrames b h]
  | .frame .., h => by simp [Code.noFrames] at h
  | .icall _ _ b n, h => by
    simp only [Code.noFrames, Bool.and_eq_true] at h
    simp only [armStack, armStack_noFrames b h.1, armStack_noFrames n h.2, Nat.max_self]

theorem encBlocks_stack : armStack Impl.Aes.Arm.encryptBlocks = 0 :=
  armStack_noFrames _ (Code.noFrames_of_noCalls AesOcb.Arm.enc_noCalls)

/-- The whole-block functions' frames: 8 bytes around each call of the
block function. -/
theorem encrypt_stack : armStack encrypt = 8 := by
  simp only [encrypt, Impl.AesCbc.Arm.whole, body, Impl.AesCbc.Arm.encFrame, armStack, encBlocks_stack]
  decide

theorem decrypt_stack : armStack decrypt = 8 := by
  simp only [decrypt, Impl.AesCbc.Arm.whole, body, Impl.AesCbc.Arm.encFrame, armStack, encBlocks_stack]
  decide

theorem encryptFinal_verified : Verified Arm.target encryptFinal (finalScratchContract true) :=
  Verified.of_correct (final_correct (fun _ hs => AesCbc.Arm.whole_wp encBody_ok hs) encrypt_stack)
    (final_ct (fun _ hs => AesCbc.Arm.whole_wp encBody_ok hs) (AesCbc.Arm.whole_ct encBody_ok encBody_ct)
      encrypt_stack)
    (final_implies true)

theorem decryptFinal_verified : Verified Arm.target decryptFinal (finalScratchContract false) :=
  Verified.of_correct (final_correct (fun _ hs => AesCbc.Arm.whole_wp decBody_ok hs) decrypt_stack)
    (final_ct (fun _ hs => AesCbc.Arm.whole_wp decBody_ok hs) (AesCbc.Arm.whole_ct decBody_ok decBody_ct)
      decrypt_stack)
    (final_implies false)

/-! ## With `save` on the stack

The final functions have two stack arguments, so `save` is their third:
they run their code in a frame of 56 bytes (`withStackScratchWiped`): the
copies of the two stack arguments, `save`'s address, the word holding `lr`,
and `save`'s 40 bytes, which it zeroes before returning. The code's calls
use 16 bytes below it, so 72 in all. -/

/-- A state satisfying the precondition, without `save`. -/
def finalFrameSat : State :=
  { finalSat with rd := [⟨0x1000, 240⟩, ⟨0x8000, 8⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩] }

theorem encFrameSat_pre : ∃ s, (encryptFinalRoundsContract Arm.abi 72).pre s := by
  implies_sat [encryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, encryptFinalPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [finalFrameSat, finalSat] using finalFrameSat

theorem decFrameSat_pre : ∃ s, (decryptFinalRoundsContract Arm.abi 72).pre s := by
  implies_sat [decryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, decryptFinalPost, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [finalFrameSat, finalSat] using finalFrameSat

/-- `encryptFinal`, with `save` on the stack (zeroed on return). -/
theorem encryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 encryptFinal)
      (encryptFinalRoundsContract Arm.abi 72) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 5)
    (pre := finalPre Arm.abi.ptrBits) (post := encryptFinalPost Arm.abi.ptrBits) (wa := false) (stack := 16)
    (m := 2) (bytes := 56) encryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (finalPre_local _) (encryptFinalPost_local _) (encryptFinalPost_localOut _) encFrameSat_pre

/-- `decryptFinal`, with `save` on the stack (zeroed on return). -/
theorem decryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 56 2 10 decryptFinal)
      (decryptFinalRoundsContract Arm.abi 72) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 5)
    (pre := finalPre Arm.abi.ptrBits) (post := decryptFinalPost Arm.abi.ptrBits) (wa := false) (stack := 16)
    (m := 2) (bytes := 56) decryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (finalPre_local _) (decryptFinalPost_local _) (decryptFinalPost_localOut _) decFrameSat_pre

end VG.Proof.AesCfb.Arm
