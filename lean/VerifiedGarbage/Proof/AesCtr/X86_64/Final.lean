module

public import VerifiedGarbage.Impl.AesCtr.X86_64.Final
public import VerifiedGarbage.Proof.AesCtr.Final
public import VerifiedGarbage.Proof.AesCtr.X86_64.Verified
public import VerifiedGarbage.Proof.AesCfb.X86_64.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.AesCtr.X86_64.CT
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
meta import VerifiedGarbage.Impl.AesCtr.X86_64.Final
meta import VerifiedGarbage.Proof.AesCtr.Final
meta import VerifiedGarbage.Proof.AesCtr.X86_64.Verified
meta import VerifiedGarbage.Proof.AesCfb.X86_64.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.AesCtr.X86_64.CT
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe

/-!
# AES-CTR of a message's last piece on x86-64

`cryptFinal_framed`: `vg_aes_ctr_final` (`Impl/AesCtr/X86_64/Final.lean`), for
any implementation `v` of `vg_aes_ctr32` (`Ctr32Impl`), meets
`Proof.AesCtr.finalRoundsContract`, from which the shared contract follows
(`Proof.AesCtr.final_keyed`).

The code is proven against `ctrFinalX86_64`, with a seventh argument `save`
of 64 bytes on the stack, for its caller's registers and a block of its own
(`final_implies`: the shared contract with it, `finalScratchContract`), as a
caller of the whole-block function, through its contract
(`modeX86_64 ctrMode`, with `ctrPub`). It shares AES-CFB's final functions'
setup and restore (`Proof/AesCfb/X86_64/Final.lean`: `Setup`, `Whole`):

* `final_setup_wp`, `whole_wp`: the registers saved, and the whole-block
  function on the `n = len / 16` whole blocks (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, the block after the
  registers in `save` zeroed and the whole-block function on it
  (`tail_args_wp`, `tail_call_wp`), which leaves `CIPH_K(Tₙ₊₁)` there and
  `Tₙ₊₂` in `ctr`, and its first `u` bytes XORed into them
  (`Modes.X86_64.xorLoop_wp`, `tail_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers restored;
* `final_post`: `Done` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`).

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
the whole-block function's constant time, whose public data, the last 32
bits of the counter block, agree in both runs at both calls: they do on
entry (the contract's leak), and after `n` blocks they are those on entry
plus `n` modulo `2³²`.
-/

@[expose] public section

namespace VG.Proof.AesCtr.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.X86_64.RegUpd
open VG.Impl.AesCtr.X86_64 (tailArgs tailMoves tailKey zeroSlots finalTail final cryptFinal crypt)
open VG.Impl.AesCfb.X86_64 (loadSave finalSetup finalRestore finalSaved finalMoves)
open VG.Proof.AesCfb.X86_64 (fW fR fIv fD fL fS fV fSp fN fU fT fSch fIvR fData fBlk fTail fScr fSv fArg fStk
  fWk fIv0 fBlks fG svMem Setup Whole)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.X86_64 (modeX86_64 callEntry_frame bytesAt_frame)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- The code's contract, with the arguments `(schedule = rdi, rounds = rsi,
ctr = rdx, data = rcx, len = r8, scratch = r9, save = [rsp + 8])`, `save` of
64 bytes: the data and the counter block as `Spec.Ctr.CryptFinal` says, by
AES with the key schedule it is given; the counter block's last four bytes
are public. -/
def ctrFinalX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let iv : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let sv : Region := ⟨stackArg s 0, 64⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧
      s.rd = [sched, args] ∧ s.wr = [iv, data, scr, sv] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint sv ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint sv ∧ iv.Disjoint args ∧
      data.Disjoint scr ∧ data.Disjoint sv ∧ data.Disjoint args ∧
      scr.Disjoint sv ∧ scr.Disjoint args ∧ sv.Disjoint args ∧
      ret.Disjoint sched ∧ ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ ret.Disjoint sv ∧
      ret.Disjoint args ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      stack.Disjoint sv ∧ stack.Disjoint args ∧
      (s.gpr .rdi).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2176 ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + 64 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    Spec.Ctr.CryptFinal (ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) s.mem s'.mem (s.gpr .rdx) (s.gpr .rcx)
      (s.gpr .r8).toNat
  pub s₁ s₂ :=
    (s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp ∧ stackArg s₁ 0 = stackArg s₂ 0) ∧
      Spec.Ctr.ctrLeak s₁.mem (s₁.gpr .rdx) = Spec.Ctr.ctrLeak s₂.mem (s₂.gpr .rdx)

/-- The contract the frame needs: the shared one, with `save`, 64 bytes, as
a seventh argument, and 16 bytes of stack (the return addresses of the
whole-block function and of `vg_aes_ctr32`, which it calls). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract X86_64.abi Spec.Ctr.aesFinalSig "save" .u64 8 (finalPre X86_64.abi.ptrBits)
    (finalPost X86_64.abi.ptrBits) false 16 (some (finalLeak X86_64.abi.ptrBits))

def ctrSatState : State := { AesCfb.X86_64.finalSatState with
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 64⟩] }

theorem final_implies : ctrFinalX86_64.Implies finalScratchContract where
  pre := by
    intro s h
    sig_pre [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, abi, argRegs, ctrFinalX86_64,
      AesCfb.X86_64.args_getD, AesCfb.X86_64.stackArgs_one, List.append_eq] at h
    sig_pre [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, abi, argRegs, ctrFinalX86_64,
      AesCfb.X86_64.args_getD, AesCfb.X86_64.stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, abi, argRegs, ctrFinalX86_64,
      AesCfb.X86_64.args_getD, AesCfb.X86_64.stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
  post := by
    sig_implies_post [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, abi, argRegs, ctrFinalX86_64,
      AesCfb.X86_64.args_getD, AesCfb.X86_64.stackArgs_one, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, abi, argRegs, ctrFinalX86_64,
      AesCfb.X86_64.args_getD, AesCfb.X86_64.stackArgs_one, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨⟨h3, h4, h5, h6, h7, h8, h1, h⟩, h2⟩
  sat := by
    sig_implies_sat [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, abi, argRegs, ctrFinalX86_64,
      AesCfb.X86_64.args_getD, AesCfb.X86_64.stackArgs_one, List.append_eq]
      [ctrSatState, AesCfb.X86_64.finalSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using ctrSatState

/-! ## The arguments, by name -/

section
variable (s₀ : State)

/-- `save`, the registers then the block. -/
abbrev cSv : Region := ⟨fV s₀, 64⟩
/-- The block after the registers in `save`. -/
abbrev cBk : Addr := fV s₀ + BitVec.ofNat 64 48
abbrev cBlk : Region := ⟨cBk s₀, 16⟩
/-- The counter block on entry. -/
abbrev cT : List Byte := bytesAt s₀.mem (fIv s₀) 16

end

/-- The precondition, by name. -/
structure CPre (s₀ : State) : Prop where
  sp_lo : 16 ≤ (fSp s₀).toNat
  sp_hi : (fSp s₀).toNat + 16 ≤ 2 ^ 64
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
  ret_sch : (⟨fSp s₀, 8⟩ : Region).Disjoint (fSch s₀)
  ret_iv : (⟨fSp s₀, 8⟩ : Region).Disjoint (fIvR s₀)
  ret_data : (⟨fSp s₀, 8⟩ : Region).Disjoint (fData s₀)
  ret_scr : (⟨fSp s₀, 8⟩ : Region).Disjoint (fScr s₀)
  ret_sv : (⟨fSp s₀, 8⟩ : Region).Disjoint (cSv s₀)
  ret_arg : (⟨fSp s₀, 8⟩ : Region).Disjoint (fArg s₀)
  stk_sch : (fStk s₀).Disjoint (fSch s₀)
  stk_iv : (fStk s₀).Disjoint (fIvR s₀)
  stk_data : (fStk s₀).Disjoint (fData s₀)
  stk_scr : (fStk s₀).Disjoint (fScr s₀)
  stk_sv : (fStk s₀).Disjoint (cSv s₀)
  stk_arg : (fStk s₀).Disjoint (fArg s₀)
  sch_wrap : (fW s₀).toNat + 240 ≤ 2 ^ 64
  iv_wrap : (fIv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (fD s₀).toNat + fL s₀ ≤ 2 ^ 64
  scr_wrap : (fS s₀).toNat + 2176 ≤ 2 ^ 64
  sv_wrap : (fV s₀).toNat + 64 ≤ 2 ^ 64
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem CPre.of {s₀ : State} (h : ctrFinalX86_64.pre s₀) : CPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩

/-! ## Regions -/

theorem sv48_sub (s₀ : State) : Region.Sub (fSv s₀) (cSv s₀) := Region.sub_prefix (by decide)
theorem blk_sv_sub (s₀ : State) : Region.Sub (cBlk s₀) (cSv s₀) := Offset.sub_base _ (by decide)

section
variable {s₀ : State} (hp : CPre s₀)
include hp

theorem CPre.sched_sub : Region.Sub ⟨fW s₀, 16 * (fR s₀ + 1)⟩ (fSch s₀) :=
  Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)

theorem CPre.sched_len : 16 * (fR s₀ + 1) ≤ 2 ^ 64 := by
  rcases hp.rounds with h | h | h <;> omega

theorem CPre.blk_wrap : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := Nat.mul_div_le (fL s₀) 16; rw [AesCfb.X86_64.fN_eq]; omega

theorem CPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [AesCfb.X86_64.fN_eq, AesCfb.X86_64.fU_eq]; omega)

omit hp in
/-- The slots of the registers miss the block. -/
theorem slot_blk : ∀ p ∈ finalSaved, Region.Disjoint ⟨Spill.slot (fV s₀) p.2, 8⟩ (cBlk s₀) := by
  intro p hp'
  have := AesCfb.X86_64.saved_slots p hp'
  exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)

end

/-! ## Saving the registers, and the whole blocks -/

theorem final_load_wp {s₀ : State} (hp : CPre s₀) :
    WP isa (.block loadSave) s₀ (· = s₀.setReg .rax (fV s₀)) :=
  WP.of_runBlock ⟨_, AesCfb.X86_64.loadSave_ok s₀ (by rw [hp.rd, hp.wr]; exact ⟨fArg s₀, by simp,
    Region.contains_self _ _⟩), rfl⟩

theorem final_setup_wp {s₀ : State} (hp : CPre s₀) :
    WP isa (.block finalSetup) (s₀.setReg .rax (fV s₀)) (Setup s₀) := by
  have hw : ∀ p ∈ finalSaved, InRegions (s₀.setReg .rax (fV s₀)).wr
      (Spill.slot ((s₀.setReg .rax (fV s₀)).gpr .rax) p.2) 8 := by
    intro p hp'
    rw [wr_setReg, gpr_setReg_self, hp.wr]
    have := AesCfb.X86_64.saved_slots p hp'
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  show WP isa (.block (Spill.saveCode .rax finalSaved ++ finalMoves)) _ _
  refine Spill.save_then .rax finalSaved hw ?_
  refine WP.mono (WP.of_runBlock (AesCfb.X86_64.moves_ok _))
    fun s' ⟨rbx, rbp, r12, r15, r14, r13, r8, rdi, rsi, rdx, rcx, r9, rsp, _, mem, rd, wr⟩ => ?_
  simp only [gpr_setReg, reduceCtorEq, ↓reduceIte] at rbx rbp r12 r15 r14 r13 r8 rdi rsi rdx rcx r9 rsp
  exact ⟨rbx, rbp, r12, by rw [r13, AesCfb.X86_64.and15, AesCfb.X86_64.tail_addr],
    by rw [r14, AesCfb.X86_64.and15], r15, rdi, rsi, rdx, rcx,
    by rw [r8, AesCfb.X86_64.shr4], r9, rsp, by rw [mem, mem_setReg, gpr_setReg_self], by rw [rd, rd_setReg],
    by rw [wr, wr_setReg]⟩

theorem crypt_noSp (v : Ctr32Impl) : NoSp (crypt v.callee) :=
  AesCfb.X86_64.noSp_of_all (by
    simp only [crypt, Impl.AesCtr.X86_64.body, Code.allInstrs, AesCfb.X86_64.all_of_noSp v.nosp]
    decide +kernel)

theorem crypt_depth (v : Ctr32Impl) : (crypt v.callee).depth = 1 := by
  simp only [crypt, Impl.AesCtr.X86_64.body, Code.depth, v.depth]
  decide

/-- The whole-block function's contract: `modeX86_64 ctrMode`, with the last
32 bits of the counter block public. -/
abbrev wholeK : Contract isa := { modeX86_64 AesCtr.ctrMode with pub := ctrPub }

theorem whole_pre {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    wholeK.pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, fBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, fBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, fBlk s₀, fScr s₀] s.wr := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
      AesCfb.X86_64.toNat_n]
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_data.sub_right (AesCfb.X86_64.blk_sub s₀), hp.sch_scr,
      hp.iv_data.sub_right (AesCfb.X86_64.blk_sub s₀), hp.iv_scr, hp.data_scr.sub_left (AesCfb.X86_64.blk_sub s₀),
      hp.stk_iv.sub_left (AesCfb.X86_64.ret8_sub _),
      (hp.stk_data.sub_left (AesCfb.X86_64.ret8_sub _)).sub_right (AesCfb.X86_64.blk_sub s₀),
      hp.stk_scr.sub_left (AesCfb.X86_64.ret8_sub _), hp.stk_sch.sub_left (AesCfb.X86_64.callee8_sub _),
      hp.stk_iv.sub_left (AesCfb.X86_64.callee8_sub _),
      (hp.stk_data.sub_left (AesCfb.X86_64.callee8_sub _)).sub_right (AesCfb.X86_64.blk_sub s₀),
      hp.stk_scr.sub_left (AesCfb.X86_64.callee8_sub _), hp.iv_wrap, hp.blk_wrap, hp.scr_wrap, hp.rounds⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩

/-- The schedule, the counter block and the whole blocks at the call, as on
entry. -/
theorem entry_bytes {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    bytesAt s.callEntry.mem (fW s₀) (16 * (fR s₀ + 1)) = fWk s₀ ∧ bytesAt s.callEntry.mem (fIv s₀) 16 = fIv0 s₀ ∧
      Spec.Cbc.blocksAt s.callEntry.mem (fD s₀) (fN s₀) = fBlks s₀ := by
  have ef := AesCfb.X86_64.entry_frame h.mem h.rsp
  refine ⟨bytesAt_frame ef (fun r hr => ?_) hp.sched_len, bytesAt_frame ef (fun r hr => ?_) (by decide),
    AesCfb.X86_64.blocksAt_frame' ef fun r hr => ?_⟩ <;>
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> rcases hr with rfl | rfl
  · exact (hp.sch_sv.sub_left hp.sched_sub).sub_right (sv48_sub s₀)
  · exact hp.stk_sch.symm.sub_left hp.sched_sub
  · exact hp.iv_sv.sub_right (sv48_sub s₀)
  · exact hp.stk_iv.symm
  · exact (hp.data_sv.sub_left (AesCfb.X86_64.blk_sub s₀)).sub_right (sv48_sub s₀)
  · exact hp.stk_data.symm.sub_left (AesCfb.X86_64.blk_sub s₀)

theorem whole_wp (v : Ctr32Impl) {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    WP isa (.call ("vg_aes_ctr" ++ v.suffix) (crypt v.callee)) s (Whole AesCtr.ctrMode s₀) := by
  obtain ⟨eW, eIv, eB⟩ := entry_bytes hp h
  obtain ⟨hpre, hc, hw⟩ := whole_pre hp h
  refine WP.call (k := wholeK) (crypt_correct v) (crypt_noSp v) (by rw [crypt_depth v]; decide) (rd := [fSch s₀])
    (wr := [fIvR s₀, fBlk s₀, fScr s₀]) hpre hc hw ?_
  intro s' rd' wr' cs' fr' _ ⟨s₂, mem₂, _, post₂⟩
  rw [crypt_depth v, h.rsp, h.mem] at fr'
  simp only [modeX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8,
    AesCfb.X86_64.toNat_n, mem₂, eW, eIv, eB] at post₂
  exact ⟨by rw [cs' .rbx (by simp [calleeSaved]), h.rbx], by rw [cs' .rbp (by simp [calleeSaved]), h.rbp],
    by rw [cs' .r12 (by simp [calleeSaved]), h.r12], by rw [cs' .r13 (by simp [calleeSaved]), h.r13],
    by rw [cs' .r14 (by simp [calleeSaved]), h.r14], by rw [cs' .r15 (by simp [calleeSaved]), h.r15],
    by rw [cs' .rsp (by simp [calleeSaved]), h.rsp], by rw [rd', h.rd], by rw [wr', h.wr], fr', post₂.1,
    post₂.2⟩

/-! ## The partial last block: its arguments -/

/-- Two zeroed quadwords make 16 zero bytes. -/
theorem zero_bytes (m : Mem) (B : Addr) :
    bytesAt ((m.writeW B (0 : BitVec 64)).writeW (B + BitVec.ofNat 64 8) (0 : BitVec 64)) B 16 =
      List.replicate 16 0 := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  have hi : i < 16 := by simpa [bytesAt] using h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate, Mem.writeW, Mem.write,
    Mem.sub_ofNat_toNat B (show i < 2 ^ 64 by omega), Offset.sub_toNat' B (show 8 < 2 ^ 64 by decide)
      (show i < 2 ^ 64 by omega)]
  by_cases h8 : 8 ≤ i
  · rw [ite_eq_left h8, ite_eq_left (by omega)]; simp
  · rw [ite_eq_right h8, ite_eq_right (by omega), ite_eq_left (by omega)]; simp

theorem tailMoves_ok (s : State) :
    ∃ s', runBlock isa tailMoves s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rdx = s.gpr .r12 ∧
      s'.gpr .rcx = s.gpr .rax + BitVec.ofNat 64 48 ∧ s'.gpr .r8 = 1 ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.gpr .r13 = s.gpr .r13 ∧ s'.gpr .r14 = s.gpr .r14 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [tailMoves, runBlock_cons, runStep_some, reduceExec, execAlu, readSrc, Option.bind_some,
      Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    try simp [gpr_setReg, State.setReg32, mem_arithFlags, rd_arithFlags, wr_arithFlags, mem_setReg, rd_setReg,
      wr_setReg]
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem zero_ok (s : State) :
    ∃ s', runBlock isa [.mov32 .r10 (.imm 0)] s = some s' ∧ s'.gpr .r10 = 0 ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [runBlock_cons, reduceExec]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32, hr]

/-! ## Frames -/

section
variable (s₀ : State)

/-- What the function writes after saving the registers, with the whole
blocks rather than the data. -/
abbrev cW1 : List Region := [fIvR s₀, fBlk s₀, fScr s₀, cBlk s₀, fStk s₀]
/-- What the function writes after saving the registers. -/
abbrev cW : List Region := [fIvR s₀, fData s₀, fScr s₀, cBlk s₀, fStk s₀]
/-- What the function writes. -/
abbrev cBig : List Region := [fIvR s₀, fData s₀, fScr s₀, cSv s₀, fStk s₀]

end

theorem cW1_cW {s₀ : State} {m : Mem} (hf : Frame (cW1 s₀) (svMem s₀) m) : Frame (cW s₀) (svMem s₀) m :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, AesCfb.X86_64.blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem whole_cW1 {M : Mode} {s₀ s : State} (h : Whole M s₀ s) : Frame (cW1 s₀) (svMem s₀) s.mem :=
  h.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

theorem big_of {s₀ : State} {m : Mem} (hf : Frame (cW s₀) (svMem s₀) m) : Frame (cBig s₀) s₀.mem m :=
  ((AesCfb.X86_64.svMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨cSv s₀, by simp, sv48_sub s₀⟩).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨cSv s₀, by simp, blk_sv_sub s₀⟩
      · exact ⟨_, by simp, fun _ h => h⟩)

/-- `save`'s address, on the stack, is unchanged. -/
theorem arg_keep {s₀ : State} (hp : CPre s₀) {s : State} (hsp : s.gpr .rsp = fSp s₀)
    (hf : Frame (cBig s₀) s₀.mem s.mem) : stackArgAddr s 0 = stackArgAddr s₀ 0 ∧ stackArg s 0 = fV s₀ := by
  have hA : stackArgAddr s 0 = stackArgAddr s₀ 0 := by simp only [stackArgAddr, hsp]
  refine ⟨hA, ?_⟩
  show s.mem.readW (stackArgAddr s 0) 64 = s₀.mem.readW (stackArgAddr s₀ 0) 64
  rw [hA]
  refine hf.readW (r := fArg s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.iv_arg.symm
  · exact hp.data_arg.symm
  · exact hp.scr_arg.symm
  · exact hp.sv_arg.symm
  · exact hp.stk_arg.symm

/-- `save` to `rax`, from a state whose stack pointer and argument slot are
as on entry. -/
theorem load_ok {s₀ : State} (hp : CPre s₀) {s : State} (hsp : s.gpr .rsp = fSp s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hf : Frame (cBig s₀) s₀.mem s.mem) :
    runBlock isa loadSave s = some (s.setReg .rax (fV s₀)) := by
  obtain ⟨hA, hV⟩ := arg_keep hp hsp hf
  rw [← hV]
  exact AesCfb.X86_64.loadSave_ok s (by rw [hrd, hwr, hp.rd, hp.wr, hA]; exact ⟨fArg s₀, by simp,
    Region.contains_self _ _⟩)

/-! ## The partial last block -/

/-- What zeroing the block and setting up the arguments leaves. -/
structure TArgs (s₀ s : State) : Prop where
  rdi : s.gpr .rdi = fW s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  rdx : s.gpr .rdx = fIv s₀
  rcx : s.gpr .rcx = cBk s₀
  r8 : s.gpr .r8 = 1
  r9 : s.gpr .r9 = fS s₀
  r13 : s.gpr .r13 = fT s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (fU s₀)
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)
  zero : bytesAt s.mem (cBk s₀) 16 = List.replicate 16 0

theorem zero_frame (s₀ : State) (m : Mem) (g : Reg → BitVec 64) :
    Frame [cBlk s₀] m (Spill.saveMem m (fV s₀) g zeroSlots) :=
  Spill.saveMem_frame m _ g zeroSlots fun p hp' => by
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact Offset.contains _ (by decide) (by decide) (by decide)
    · exact Offset.contains _ (by decide) (by decide) (by decide)

/-- `save` to `rax`, from a state `F` describes. -/
abbrev Loaded (F : State → Prop) (s₀ s : State) : Prop := ∃ w, F w ∧ s = w.setReg .rax (fV s₀)

theorem tail_load_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.block loadSave) s (Loaded (Whole AesCtr.ctrMode s₀) s₀) :=
  WP.of_runBlock ⟨_, load_ok hp h.rsp h.rd h.wr (big_of (cW1_cW (whole_cW1 h))), s, h, rfl⟩

theorem tail_args_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.block tailArgs) (s.setReg .rax (fV s₀)) (TArgs s₀) := by
  have f₁ := whole_cW1 h
  obtain ⟨s₂, r₂, z₂, k₂, m₂, rd₂, wr₂⟩ := zero_ok (s.setReg .rax (fV s₀))
  show WP isa (.block ([.mov32 .r10 (.imm 0)] ++ (Spill.saveCode .rax zeroSlots ++ tailMoves))) _ _
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₂, r₂, ?_⟩)
  have k₂' : ∀ r, r ≠ .r10 → r ≠ .rax → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [k₂ r h₁, gpr_setReg_of_ne _ _ h₂]
  have hrax : s₂.gpr .rax = fV s₀ := by rw [k₂ _ (by decide), gpr_setReg_self]
  have hw : ∀ p ∈ zeroSlots, InRegions s₂.wr (Spill.slot (s₂.gpr .rax) p.2) 8 := by
    intro p hp'
    rw [wr₂, wr_setReg, h.wr, hp.wr, hrax]
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨cSv s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
    · exact ⟨cSv s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  refine Spill.save_then .rax zeroSlots hw ?_
  refine WP.mono (WP.of_runBlock (tailMoves_ok _))
    fun s' ⟨rdi, rsi, rdx, rcx, r8, r9, cs, r13, r14, mem, rd, wr⟩ => ?_
  have e : ∀ r, ({ s₂ with mem := Spill.saveMem s₂.mem (s₂.gpr .rax) s₂.gpr zeroSlots } : State).gpr r =
    s₂.gpr r := fun _ => rfl
  rw [e] at rdi rsi rdx rcx r9 r13 r14
  have hm : s'.mem = Spill.saveMem s.mem (fV s₀) s₂.gpr zeroSlots := by
    rw [mem]; show Spill.saveMem s₂.mem _ _ _ = _; rw [m₂, mem_setReg, hrax]
  have fz : Frame [cBlk s₀] s.mem s'.mem := by rw [hm]; exact zero_frame s₀ _ _
  have ivZ : ∀ r ∈ [cBlk s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  have blkZ : ∀ r ∈ [cBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (AesCfb.X86_64.blk_sub s₀)).sub_right (blk_sv_sub s₀)
  refine ⟨by rw [rdi, k₂' _ (by decide) (by decide), h.rbx], by rw [rsi, k₂' _ (by decide) (by decide), h.rbp],
    by rw [rdx, k₂' _ (by decide) (by decide), h.r12], by rw [rcx, hrax], r8,
    by rw [r9, k₂' _ (by decide) (by decide), h.r15], by rw [r13, k₂' _ (by decide) (by decide), h.r13],
    by rw [r14, k₂' _ (by decide) (by decide), h.r14], ?_, by rw [rd, rd₂, rd_setReg, h.rd],
    by rw [wr, wr₂, wr_setReg, h.wr], ?_, ?_, ?_, ?_⟩
  · rw [cs .rsp (by simp [calleeSaved]), e, k₂' _ (by decide) (by decide), h.rsp]
  · exact f₁.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [AesCfb.X86_64.blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [bytesAt_frame fz ivZ (by decide), h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]
  · rw [hm, show Spill.saveMem s.mem (fV s₀) s₂.gpr zeroSlots =
        ((s.mem.writeW (cBk s₀) (s₂.gpr .r10)).writeW (cBk s₀ + BitVec.ofNat 64 8) (s₂.gpr .r10)) by
      simp only [Spill.saveMem, zeroSlots, Spill.slot, Offset.add_add], z₂]
    exact zero_bytes _ _

theorem one_toNat : (1 : BitVec 64).toNat = 1 := rfl

theorem cBk_toNat {s₀ : State} (hp : CPre s₀) : (cBk s₀).toNat = (fV s₀).toNat + 48 := by
  have := hp.sv_wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 48) (by decide), Nat.mod_eq_of_lt (by omega)]

theorem tail_pre {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    wholeK.pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, cBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, cBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, cBlk s₀, fScr s₀] s.wr := by
  have bs := blk_sv_sub s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
      one_toNat, Nat.mul_one]
    have := hp.sv_wrap
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_sv.sub_right bs, hp.sch_scr,
      hp.iv_sv.sub_right bs, hp.iv_scr, (hp.scr_sv.sub_right bs).symm,
      hp.stk_iv.sub_left (AesCfb.X86_64.ret8_sub _),
      (hp.stk_sv.sub_left (AesCfb.X86_64.ret8_sub _)).sub_right bs,
      hp.stk_scr.sub_left (AesCfb.X86_64.ret8_sub _), hp.stk_sch.sub_left (AesCfb.X86_64.callee8_sub _),
      hp.stk_iv.sub_left (AesCfb.X86_64.callee8_sub _),
      (hp.stk_sv.sub_left (AesCfb.X86_64.callee8_sub _)).sub_right bs,
      hp.stk_scr.sub_left (AesCfb.X86_64.callee8_sub _), hp.iv_wrap, by rw [cBk_toNat hp]; omega,
      hp.scr_wrap, hp.rounds⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 48, by simp, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 48, by simp, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩

/-- What the call on the block leaves. -/
structure TCall (s₀ s : State) : Prop where
  r13 : s.gpr .r13 = fT s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (fU s₀)
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (Spec.Ctr.next (fIv0 s₀) (fN s₀)) 1
  out : bytesAt s.mem (cBk s₀) 16 = Spec.Cbc.aesWith (fR s₀) (fWk s₀) (Spec.Ctr.next (fIv0 s₀) (fN s₀))

theorem CPre.sched_big {s₀ : State} (hp : CPre s₀) :
    ∀ r ∈ cBig s₀, (⟨fW s₀, 16 * (fR s₀ + 1)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left hp.sched_sub
  · exact hp.sch_data.sub_left hp.sched_sub
  · exact hp.sch_scr.sub_left hp.sched_sub
  · exact hp.sch_sv.sub_left hp.sched_sub
  · exact hp.stk_sch.symm.sub_left hp.sched_sub

theorem tail_call_wp (v : Ctr32Impl) {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    WP isa (.call ("vg_aes_ctr" ++ v.suffix) (crypt v.callee)) s (TCall s₀) := by
  obtain ⟨hpre, hc, hw⟩ := tail_pre hp h
  have ef := callEntry_frame s
  have stk : Region.Sub (below (s.gpr .rsp) 8) (fStk s₀) := by rw [h.rsp]; exact AesCfb.X86_64.below8_sub _
  have big := big_of (cW1_cW h.frame)
  have eW : bytesAt s.callEntry.mem (fW s₀) (16 * (fR s₀ + 1)) = fWk s₀ := by
    rw [bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.stk_sch.symm.sub_left hp.sched_sub).sub_right stk) hp.sched_len]
    exact bytesAt_frame big hp.sched_big hp.sched_len
  have eT : bytesAt s.callEntry.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀) := by
    rw [bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.stk_iv.symm.sub_right stk) (by decide)]
    exact h.ctr
  have eZ : bytesAt s.callEntry.mem (cBk s₀) 16 = List.replicate 16 0 := by
    rw [bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.stk_sv.symm.sub_left (blk_sv_sub s₀)).sub_right stk) (by decide)]
    exact h.zero
  refine WP.call (k := wholeK) (crypt_correct v) (crypt_noSp v) (by rw [crypt_depth v]; decide) (rd := [fSch s₀])
    (wr := [fIvR s₀, cBlk s₀, fScr s₀]) hpre hc hw ?_
  intro s' rd' wr' cs' fr' _ ⟨s₂, mem₂, _, post₂⟩
  rw [crypt_depth v, h.rsp] at fr'
  simp only [modeX86_64, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
    State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, one_toNat, mem₂, eW,
    eT, AesCtr.ctrMode_out, AesCtr.ctrMode_chain, AesCbc.length_blocksAt] at post₂
  have hrounds : (s₀.gpr .rsi).toNat = fR s₀ := rfl
  rw [hrounds] at post₂
  have fc : Frame (cW1 s₀) s.mem s'.mem := fr'.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨by rw [cs' .r13 (by simp [calleeSaved]), h.r13], by rw [cs' .r14 (by simp [calleeSaved]), h.r14],
    by rw [cs' .rsp (by simp [calleeSaved]), h.rsp], by rw [rd', h.rd], by rw [wr', h.wr], h.frame.trans fc, ?_,
    post₂.2, ?_⟩
  · rw [AesCfb.X86_64.blocksAt_frame' fr' fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (AesCfb.X86_64.blk_sub s₀)
      · exact (hp.data_sv.sub_left (AesCfb.X86_64.blk_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact hp.data_scr.sub_left (AesCfb.X86_64.blk_sub s₀)
      · exact hp.stk_data.symm.sub_left (AesCfb.X86_64.blk_sub s₀)]
    exact h.blocks
  · exact Modes.CtrFinal.bytesAt_of_blocksAt_one (aesWith_length _ _) eZ post₂.1

theorem key_ok (s : State) :
    ∃ s', runBlock isa tailKey s = some s' ∧ s'.gpr .rax = s.gpr .rax + BitVec.ofNat 64 48 ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [tailKey, runBlock_cons, runStep_some, reduceExec, execAlu, readSrc, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg, hr]
  · simp [mem_arithFlags, mem_setReg]
  · simp [rd_arithFlags, rd_setReg]
  · simp [wr_arithFlags, wr_setReg]

/-- What the function leaves before restoring the registers. -/
structure Done (s₀ s : State) : Prop where
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q) ^^^
    (Spec.Cbc.aesWith (fR s₀) (fWk s₀) (Spec.Ctr.next (fIv0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : Whole AesCtr.ctrMode s₀ s) (hu : fU s₀ = 0) : Done s₀ s :=
  ⟨h.rsp, h.rd, h.wr, cW1_cW (whole_cW1 h), h.blocks, fun q hq => absurd hq (by omega), by
    rw [ite_eq_left hu, h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]⟩

theorem key_load_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TCall s₀ s) :
    WP isa (.block loadSave) s (Loaded (TCall s₀) s₀) :=
  WP.of_runBlock ⟨_, load_ok hp h.rsp h.rd h.wr (big_of (cW1_cW h.frame)), s, h, rfl⟩

theorem tail_xor_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block tailKey) (.loop (.block (Impl.Modes.X86_64.xorByte .r13 .r14)) .ne))
      (s.setReg .rax (fV s₀)) (Done s₀) := by
  obtain ⟨s₁, r₁, rax₁, k₁, m₁, rd₁, wr₁⟩ := key_ok (s.setReg .rax (fV s₀))
  rw [gpr_setReg_self] at rax₁
  have k₁' : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r hr => by rw [k₁ r hr, gpr_setReg_of_ne _ _ hr]
  rw [mem_setReg] at m₁
  rw [rd_setReg] at rd₁
  rw [wr_setReg] at wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, r₁, ?_⟩)
  have hU : fU s₀ < 16 := Nat.mod_lt _ (by decide)
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hVw := hp.sv_wrap
  have eN := AesCfb.X86_64.fN_eq s₀
  have eU := AesCfb.X86_64.fU_eq s₀
  have hT : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hB := cBk_toNat hp
  have xp : Modes.X86_64.XPre s₁ (cBk s₀) (fT s₀) (fU s₀) .r13 .r14 := {
    pos := by omega
    small := by omega
    fitK := by omega
    fitR := by rw [hT]; omega
    disj := (((hp.data_sv.sub_left (AesCfb.X86_64.tail_sub s₀)).sub_right (blk_sv_sub s₀)).sub_right
      (Region.sub_prefix (by omega))).symm
    rdK := fun q hq => by
      rw [rd₁, wr₁, h.rd, h.wr, hp.rd, hp.wr]
      refine ⟨cSv s₀, by simp, ?_⟩
      rw [Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)
    wrR := fun q hq => by
      rw [wr₁, h.wr, hp.wr]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show fT s₀ + BitVec.ofNat 64 q = fD s₀ + BitVec.ofNat 64 (16 * fN s₀ + q) from Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega)
    dl := by decide
    dRax := by decide
    dR10 := by decide
    dRcx := by decide }
  have x0 : Modes.X86_64.XInv s₁ (cBk s₀) (fT s₀) (fU s₀) .r13 .r14 0 s₁ := {
    rax := by rw [rax₁]; exact (BitVec.add_zero _).symm
    dat := by rw [k₁' _ (by decide), h.r13]; exact (BitVec.add_zero _).symm
    left := by rw [k₁' _ (by decide), h.r14, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Modes.X86_64.xorLoop_wp xp x0) fun s' d => ?_
  have tailD : ∀ r ∈ cW1 s₀, (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.iv_data.sub_right (AesCfb.X86_64.tail_sub s₀)).symm
    · exact hp.blk_tail.symm
    · exact hp.data_scr.sub_left (AesCfb.X86_64.tail_sub s₀)
    · exact (hp.data_sv.sub_left (AesCfb.X86_64.tail_sub s₀)).sub_right (blk_sv_sub s₀)
    · exact (hp.stk_data.sub_right (AesCfb.X86_64.tail_sub s₀)).symm
  have tailS : ∀ r ∈ [fSv s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (AesCfb.X86_64.tail_sub s₀)).sub_right (sv48_sub s₀)
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; omega
  have ivT : ∀ r ∈ [fTail s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.iv_data.sub_right (AesCfb.X86_64.tail_sub s₀)
  refine ⟨by rw [d.gpr .rsp (by decide) (by decide) (by decide) (by decide) (by decide), k₁' _ (by decide), h.rsp],
    by rw [d.rd, rd₁, h.rd], by rw [d.wr, wr₁, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · refine cW1_cW h.frame |>.trans ?_
    rw [← m₁]
    exact d.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, AesCfb.X86_64.tail_sub s₀⟩
  · rw [AesCfb.X86_64.blocksAt_frame' d.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail, m₁]
    exact h.blocks
  · rw [d.data q hq, m₁, h.frame.bytes tailD hlen hq, (AesCfb.X86_64.svMem_frame s₀).bytes tailS hlen hq,
      ← AesCfb.X86_64.bytesAt_getD s.mem (cBk s₀) (show q < 16 by omega), h.out]
  · rw [ite_eq_right hu, bytesAt_frame d.frame ivT (by decide), m₁, h.ctr, ← AesCtr.next_add]

theorem final_mid_wp (v : Ctr32Impl) {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s)
    (hz : s.zf = some (decide (fU s₀ = 0))) :
    WP isa (.ite .e (.block []) (finalTail ("vg_aes_ctr" ++ v.suffix) (crypt v.callee))) s (Done s₀) := by
  have ev : isa.eval .e s = some (decide (fU s₀ = 0)) := hz
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [ev, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [ev, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (tail_load_wp hp h) fun _ ⟨w, hw, e⟩ => ?_)
    subst e
    exact WP.seq (WP.mono (tail_args_wp hp hw) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp v hp h₁) fun _ h₂ =>
        WP.seq (WP.mono (key_load_wp hp h₂) fun _ ⟨w', hw', e'⟩ => by subst e'; exact tail_xor_wp hp hw' hu)))

/-! ## Restoring the registers -/

theorem final_end_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Done s₀ s) :
    WP isa (.seq (.block loadSave) (.block finalRestore)) s fun s' => gprPreserved s₀ s' ∧ s'.mem = s.mem := by
  have big := big_of h.frame
  refine WP.seq (WP.of_runBlock ⟨_, load_ok hp h.rsp h.rd h.wr big, ?_⟩)
  have hs : Spill.Saved (s.setReg .rax (fV s₀)).mem ((s.setReg .rax (fV s₀)).gpr .rax) (fG s₀) finalSaved := by
    rw [mem_setReg, gpr_setReg_self]
    refine (Spill.saveMem_saved _ _ _ _ (by decide)).frame h.frame fun p hp' r hr => ?_
    have hsub : Region.Sub ⟨Spill.slot (fV s₀) p.2, 8⟩ (cSv s₀) :=
      Offset.sub_base _ (by have := AesCfb.X86_64.saved_slots p hp'; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.iv_sv.symm.sub_left hsub
    · exact hp.data_sv.symm.sub_left hsub
    · exact hp.scr_sv.symm.sub_left hsub
    · exact slot_blk p hp'
    · exact hp.stk_sv.symm.sub_left hsub
  show WP isa (.block (Spill.restoreCode .rax finalSaved)) _ _
  refine WP.mono (Spill.restore_ok .rax finalSaved (fG s₀) _ (by decide) (fun p hp' => ?_) hs)
    fun s' ⟨g₁, g₂, mem', _, _⟩ => ?_
  · rw [rd_setReg, wr_setReg, gpr_setReg_self, h.rd, h.wr, hp.rd, hp.wr]
    have := AesCfb.X86_64.saved_slots p hp'
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  · have cs := Spill.calleeSaved_ok g₁ g₂ (by decide)
      (show _ = (s₀.setReg .rax (fV s₀)).gpr .rsp by
        rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), h.rsp])
    refine ⟨⟨fun r hr => by rw [cs r hr]; exact gpr_setReg_of_ne _ _ (AesCfb.X86_64.calleeSaved_ne_rax' hr), ?_⟩,
      by rw [mem', mem_setReg]⟩
    rw [mem', mem_setReg]
    refine big.readW (r := ⟨fSp s₀, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact hp.ret_sv
    · exact Offset.base_disjoint_below _ (by decide)

/-! ## The whole function -/

theorem final_wp (v : Ctr32Impl) {s₀ : State} (hp : CPre s₀) :
    WP isa (cryptFinal v.callee v.suffix) s₀ fun s' => gprPreserved s₀ s' ∧ ∃ s₁, Done s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_load_wp hp) fun s₁ e₁ => ?_)
  subst e₁
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (whole_wp v hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (AesCfb.X86_64.final_test_wp h₃) fun s₄ ⟨h₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (final_mid_wp v hp h₄ z₄) fun s₅ h₅ => ?_)
  exact WP.mono (final_end_wp hp h₅) fun _ ⟨g, m⟩ => ⟨g, s₅, h₅, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalX86_64.post s₀ s' := by
  show Spec.Ctr.CryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem cryptFinal_mx (v : Ctr32Impl) :
    (cryptFinal v.callee v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [cryptFinal, final, finalTail, Code.allInstrs, crypt_mx v]
  decide +kernel

theorem final_correct (v : Ctr32Impl) (s : State) (hs : ctrFinalX86_64.pre s) :
    ∃ t s', Exec isa (cryptFinal v.callee v.suffix) s t s' ∧ abiPreserved s s' ∧ ctrFinalX86_64.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp v (CPre.of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (cryptFinal_mx v) he hg, final_post h₁ hm⟩

/-! ## Constant time -/

/-- Counter blocks whose last 32 bits agree still do after `k` increments. -/
theorem lo32_next_of {t t' : List Byte} (ht : t.length = 16) (ht' : t'.length = 16)
    (h : AesCtr.lo32 t = AesCtr.lo32 t') (k : Nat) :
    AesCtr.lo32 (Spec.Ctr.next t k) = AesCtr.lo32 (Spec.Ctr.next t' k) := by
  rw [AesCtr.lo32_next ht, AesCtr.lo32_next ht']
  unfold AesCtr.lo32 at h
  omega

theorem TArgs.entry_ctr {s₀ s : State} (hp : CPre s₀) (h : TArgs s₀ s) :
    bytesAt s.callEntry.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀) := by
  rw [bytesAt_frame (callEntry_frame s) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.stk_iv.symm.sub_right (by rw [h.rsp]; exact AesCfb.X86_64.below8_sub _)) (by decide)]
  exact h.ctr

theorem loadSave_taint : ∃ h, (taint.check (Taint.ofRegs [.rsp]) (.block loadSave) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem setup_taint : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp, .rax])
    (.block finalSetup) h).isSome = true := ⟨_, by taint_decide⟩

theorem ftest_taint : ∃ h, (taint.check (Taint.ofRegs [.r14]) (.block [.alu .test .r14 (.reg .r14)]) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.rax, .rbx, .rbp, .r12, .r15, .rsp])
    (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (Taint.ofRegs [.rax, .r13, .r14])
    (.seq (.block tailKey) (.loop (.block (Impl.Modes.X86_64.xorByte .r13 .r14)) .ne)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.rax]) (.block finalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : ctrFinalX86_64.pre s₀) (h0' : ctrFinalX86_64.pre s₀')
    (hq : ctrFinalX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (cryptFinal v.callee v.suffix) fun _ _ => True := by
  have hp := CPre.of h0
  have hp' := CPre.of h0'
  obtain ⟨⟨qW, qR, qIv, qD, qL, qS, qSp, qV⟩, qLk⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, qD, qN]
  have qLo : AesCtr.lo32 (fIv0 s₀) = AesCtr.lo32 (fIv0 s₀') :=
    AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _) qLk
  -- `save` to `rax`.
  have r₁ := taint_rel (P := fun a b => a = s₀ ∧ b = s₀') (F₁ := (· = s₀.setReg .rax (fV s₀)))
    (F₂ := (· = s₀'.setReg .rax (fV s₀'))) [.rsp] loadSave_taint
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h; simp only [List.mem_singleton] at hr; subst hr; exact qSp)
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨final_load_wp hp, final_load_wp hp'⟩
  -- The registers saved and the arguments set up.
  have r₂ := taint_rel (P := fun a b => a = s₀.setReg .rax (fV s₀) ∧ b = s₀'.setReg .rax (fV s₀'))
    (F₁ := Setup s₀) (F₂ := Setup s₀') [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp, .rax] setup_taint
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, qW, qR, qIv, qD, qL, qS, qSp, fV, qV])
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨final_setup_wp hp, final_setup_wp hp'⟩
  -- The whole blocks.
  have r₃ := (RelCT.callEx (k := wholeK) (n := "vg_aes_ctr" ++ v.suffix) (crypt_correct v) (crypt_ct v)
    (P := fun a b => Setup s₀ a ∧ Setup s₀' b) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre hp ha
      obtain ⟨pb, cb, wb⟩ := whole_pre hp' hb
      refine ⟨_, _, _, _, pa, pb, ⟨?_, ?_⟩, ca, wa, cb, wb, by rw [ha.rsp, hb.rsp, fSp, fSp, qSp]⟩
      · simp only [modeX86_64, State.withRegions_gpr, State.callEntry_rsp,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
          ha.rdi, ha.rsi, ha.rdx, ha.rcx, ha.r8, ha.r9, ha.rsp, hb.rdi, hb.rsi, hb.rdx, hb.rcx, hb.r8, hb.r9,
          hb.rsp]
        rw [fW, fW, fIv, fIv, fD, fD, fS, fS, fSp, fSp, qW, qR, qIv, qD, qS, qSp, qN]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [AesCbc.X86_64.iv0, AesCbc.X86_64.Iv, State.withRegions_gpr, State.withRegions_mem,
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), ha.rdx, hb.rdx]
        rw [(entry_bytes hp ha).2.1, (entry_bytes hp' hb).2.1]
        exact qLo).wp
    (F₁ := Whole AesCtr.ctrMode s₀) (F₂ := Whole AesCtr.ctrMode s₀')
    fun a b h => ⟨whole_wp v hp h.1, whole_wp v hp' h.2⟩
  -- The test.
  have r₄ := taint_rel (P := fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b)
    (F₁ := fun (s : State) => Whole AesCtr.ctrMode s₀ s ∧ s.zf = some (decide (fU s₀ = 0)))
    (F₂ := fun (s : State) => Whole AesCtr.ctrMode s₀' s ∧ s.zf = some (decide (fU s₀' = 0))) [.r14] ftest_taint
    (fun a b h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.r14, h.2.r14, qU])
    fun a b h => ⟨AesCfb.X86_64.final_test_wp h.1, AesCfb.X86_64.final_test_wp h.2⟩
  -- The partial last block.
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b)
      (finalTail ("vg_aes_ctr" ++ v.suffix) (crypt v.callee)) fun a b => Done s₀ a ∧ Done s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₁ := taint_rel (P := fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b)
      (F₁ := Loaded (Whole AesCtr.ctrMode s₀) s₀) (F₂ := Loaded (Whole AesCtr.ctrMode s₀') s₀') [.rsp]
      loadSave_taint
      (fun a b h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, fSp, fSp, qSp])
      fun a b h => ⟨tail_load_wp hp h.1, tail_load_wp hp' h.2⟩
    have a₂ := taint_rel (P := fun a b => Loaded (Whole AesCtr.ctrMode s₀) s₀ a ∧
        Loaded (Whole AesCtr.ctrMode s₀') s₀' b)
      (F₁ := TArgs s₀) (F₂ := TArgs s₀') [.rax, .rbx, .rbp, .r12, .r15, .rsp] tailArgs_taint
      (fun a b h r hr => by
        obtain ⟨⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [gpr_setReg_self, gpr_setReg_self, fV, fV, qV]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.rbx, hw'.rbx, fW, fW, qW]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.rbp, hw'.rbp, qR]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.r12, hw'.r12, fIv, fIv, qIv]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.r15, hw'.r15, fS, fS, qS]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.rsp, hw'.rsp, fSp, fSp,
            qSp])
      fun a b h => by
        obtain ⟨⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ := h
        exact ⟨tail_args_wp hp hw, tail_args_wp hp' hw'⟩
    have a₃ := (RelCT.callEx (k := wholeK) (n := "vg_aes_ctr" ++ v.suffix) (crypt_correct v) (crypt_ct v)
      (P := fun a b => TArgs s₀ a ∧ TArgs s₀' b) fun a b ⟨ha, hb⟩ => by
        obtain ⟨pa, ca, wa⟩ := tail_pre hp ha
        obtain ⟨pb, cb, wb⟩ := tail_pre hp' hb
        refine ⟨_, _, _, _, pa, pb, ⟨?_, ?_⟩, ca, wa, cb, wb, by rw [ha.rsp, hb.rsp, fSp, fSp, qSp]⟩
        · simp only [modeX86_64, State.withRegions_gpr, State.callEntry_rsp,
            State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
            State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
            State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
            ha.rdi, ha.rsi, ha.rdx, ha.rcx, ha.r8, ha.r9, ha.rsp, hb.rdi, hb.rsi, hb.rdx, hb.rcx, hb.r8, hb.r9,
            hb.rsp]
          rw [fW, fW, fIv, fIv, cBk, cBk, fV, fV, fS, fS, fSp, fSp, qW, qR, qIv, qV, qS, qSp]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
        · simp only [AesCbc.X86_64.iv0, AesCbc.X86_64.Iv, State.withRegions_gpr, State.withRegions_mem,
            State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), ha.rdx, hb.rdx]
          rw [ha.entry_ctr hp, hb.entry_ctr hp', qN]
          exact lo32_next_of (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _) qLo _).wp
      (F₁ := TCall s₀) (F₂ := TCall s₀') fun a b h => ⟨tail_call_wp v hp h.1, tail_call_wp v hp' h.2⟩
    have a₄ := taint_rel (P := fun a b => TCall s₀ a ∧ TCall s₀' b)
      (F₁ := Loaded (TCall s₀) s₀) (F₂ := Loaded (TCall s₀') s₀') [.rsp] loadSave_taint
      (fun a b h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, fSp, fSp, qSp])
      fun a b h => ⟨key_load_wp hp h.1, key_load_wp hp' h.2⟩
    have a₅ := taint_rel (P := fun a b => Loaded (TCall s₀) s₀ a ∧ Loaded (TCall s₀') s₀' b)
      (F₁ := Done s₀) (F₂ := Done s₀') [.rax, .r13, .r14] xor_taint
      (fun a b h r hr => by
        obtain ⟨⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [gpr_setReg_self, gpr_setReg_self, fV, fV, qV]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.r13, hw'.r13, qT]
        · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), hw.r14, hw'.r14, qU])
      fun a b h => by
        obtain ⟨⟨w, hw, rfl⟩, ⟨w', hw', rfl⟩⟩ := h
        exact ⟨tail_xor_wp hp hw hu, tail_xor_wp hp' hw' hu'⟩
    exact a₁.seq (a₂.seq ((a₃.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₄.seq a₅)))
  have r₅ : RelCT isa (fun a b => (Whole AesCtr.ctrMode s₀ a ∧ a.zf = some (decide (fU s₀ = 0))) ∧
      (Whole AesCtr.ctrMode s₀' b ∧ b.zf = some (decide (fU s₀' = 0))))
      (.ite .e (.block []) (finalTail ("vg_aes_ctr" ++ v.suffix) (crypt v.callee)))
      (fun a b => Done s₀ a ∧ Done s₀' b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, qU]
    · refine RelCT.block_nil fun a b h => ?_
      have h0 : fU s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨done_of_zero h.1.1.1 h0, done_of_zero h.1.2.1 (qU ▸ h0)⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
  -- `save` to `rax`, and the registers restored.
  have r₆ := taint_rel (P := fun a b => Done s₀ a ∧ Done s₀' b)
    (F₁ := fun (s : State) => s.gpr .rax = fV s₀) (F₂ := fun (s : State) => s.gpr .rax = fV s₀') [.rsp]
    loadSave_taint
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, fSp, fSp, qSp])
    fun a b h => ⟨WP.of_runBlock ⟨_, load_ok hp h.1.rsp h.1.rd h.1.wr (big_of h.1.frame), gpr_setReg_self _ _ _⟩,
      WP.of_runBlock ⟨_, load_ok hp' h.2.rsp h.2.rd h.2.wr (big_of h.2.frame), gpr_setReg_self _ _ _⟩⟩
  obtain ⟨_, t₇⟩ := restore_taint
  have r₇ := RelCT.taint (A := taint) (P := fun a b => a.gpr .rax = fV s₀ ∧ b.gpr .rax = fV s₀') _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1, h.2, fV, fV, qV]) t₇
  exact r₁.seq (r₂.seq ((r₃.mono (fun _ _ h => h) fun _ _ h => h.2).seq (r₄.seq (r₅.seq (r₆.seq r₇)))))

theorem final_ct (v : Ctr32Impl) :
    ConstantTime isa ctrFinalX86_64.pre ctrFinalX86_64.pub (cryptFinal v.callee v.suffix) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem cryptFinal_spSafe (v : Ctr32Impl) :
    (cryptFinal v.callee v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [cryptFinal, final, finalTail, Code.all, crypt_spSafe v]
  decide +kernel

theorem cryptFinal_xdepth (v : Ctr32Impl) : (cryptFinal v.callee v.suffix).x86_64Depth ≤ 16 := by
  simp only [cryptFinal, final, finalTail, crypt, Impl.AesCtr.X86_64.body, Code.x86_64Depth, v.noStack]
  decide

theorem cryptFinal_verified (v : Ctr32Impl) :
    Verified X86_64.target (cryptFinal v.callee v.suffix) finalScratchContract :=
  Verified.of_correct (final_correct v) (final_ct v) final_implies

/-! ## With `save` on the stack

The final function has six argument words, so `save` is its first stack
argument: it runs its code in a frame of 80 bytes (`withStackArgScratchWiped`):
the quadword standing for the return address, `save`'s address, and `save`'s
64 bytes (the registers, then the block that held the last output block),
which it zeroes before returning. The code's calls use 16 bytes below it, so
96 in all. -/

theorem frameSat_pre : ∃ s, (finalRoundsContract X86_64.abi 96).pre s := by
  implies_sat [finalRoundsContract, Spec.Ctr.aesFinalSig, finalPre, finalPost, X86_64.abi,
    X86_64.argRegs] [AesCfb.X86_64.finalFrameSat, AesCfb.X86_64.finalSatState] using AesCfb.X86_64.finalFrameSat

theorem cryptFinal_framed (v : Ctr32Impl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 80 0 8 (cryptFinal v.callee v.suffix))
      (finalRoundsContract X86_64.abi 96) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Ctr.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre X86_64.abi.ptrBits) (post := finalPost X86_64.abi.ptrBits) (wa := false)
    (leak := some (finalLeak X86_64.abi.ptrBits))
    (stack := 16) (bytes := 80) (words := 8) (cryptFinal_verified v) (by decide) (by decide) (by decide)
    (cryptFinal_spSafe v) (cryptFinal_xdepth v) (by decide) (finalPre_local _) (finalPost_local _)
    (finalPost_localOut _) frameSat_pre (finalLeak_local _)

theorem cryptFinal_framed_spSafe (v : Ctr32Impl) :
    (Impl.StackScratch.X86_64.withStackArgScratchWiped 80 0 8 (cryptFinal v.callee v.suffix)).all
      (fun i => !X86_64.isa.writesSp i) = true :=
  X86_64.withStackArgScratch_spSafe (by
    simp only [Code.all, cryptFinal_spSafe v, X86_64.wipeAt_spSafe, Bool.and_self])

end VG.Proof.AesCtr.X86_64
