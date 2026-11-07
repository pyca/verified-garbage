module

public import VerifiedGarbage.Impl.AesCfb.X86_64.Final
public import VerifiedGarbage.Proof.AesCfb.Final
public import VerifiedGarbage.Proof.AesCfb.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesOfb.X86_64.Body
import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
import VerifiedGarbage.Proof.AesCfb.X86_64.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.CT
import VerifiedGarbage.Proof.AesCbc.X86_64.Group
import VerifiedGarbage.Proof.AesCfb.X86_64.Group
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe
meta import VerifiedGarbage.Impl.AesCfb.X86_64.Final
meta import VerifiedGarbage.Proof.AesCfb.Final
meta import VerifiedGarbage.Proof.AesCfb.X86_64.Verified
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesOfb.X86_64.Body
meta import VerifiedGarbage.Proof.Modes.X86_64.FbFinal
meta import VerifiedGarbage.Proof.AesCfb.X86_64.Body
meta import VerifiedGarbage.Proof.AesCbc.X86_64.CT
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Group
meta import VerifiedGarbage.Proof.AesCfb.X86_64.Group
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe

/-!
# AES-CFB128 of a message's last piece on x86-64

`encryptFinal_framed` and `decryptFinal_framed`: `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final` (`Impl/AesCfb/X86_64/Final.lean`), for any
implementation `v` of the block functions (`BlocksImpl`), meet
`Proof.AesCfb.encryptFinalRoundsContract` (and `decrypt…`), from which the
shared contracts follow (`Proof.AesCfb.encryptFinal_keyed`).

The code is proven against `finalX86_64`, with a seventh argument `save` on
the stack for its caller's registers (`final_implies`: the shared contract
with it, `finalScratchContract`), as a caller of two verified functions,
through their contracts (`WP.call`, `blk_call`):

* `final_setup_wp`: `save`'s address loaded, the registers saved there, and
  the arguments set up (`Setup`);
* `whole_wp`: the whole-block function of the same direction and variant on
  the `n = len / 16` whole blocks, from its contract
  (`modeX86_64 (cfbMode enc)`), with the regions it is given
  (`whole_pre`): the blocks and the chaining value the mode's (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, the block function on
  the chaining value in place (`final_ivArgs_wp`, `final_ciph_wp`), and its
  first `u` bytes XORed into them by the modes' loop
  (`Modes.X86_64.xorLoop_wp`, `final_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers restored from `save`, whose address on the
  stack and slots nothing else wrote;
* `final_post`: `Done` gives `Spec.Cfb.EncryptFinal` (or `DecryptFinal`),
  by `Proof.AesCfb.encryptFinal_of`.

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
their contracts' constant time (`RelCT.callEx`, `blk_rel`), every address
and branch from the pointers and `len`, which agree in both runs.
`encryptFinal_framed` runs the code with `save` in a frame of 64 bytes on
the stack (`Verified.stackArgScratchWiped`), zeroed on return.
-/

@[expose] public section

namespace VG.Proof.AesCfb.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)

/-- The code's contract, with the arguments `(schedule = rdi, rounds = rsi,
iv = rdx, data = rcx, len = r8, scratch = r9, save = [rsp + 8])`: in direction
`enc`, the data and the block at `iv` as `Spec.Cfb.EncryptFinal` (or
`DecryptFinal`) says, by AES with the key schedule it is given. -/
def finalX86_64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let iv : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let sv : Region := ⟨stackArg s 0, 48⟩
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
      (stackArg s 0).toNat + 48 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    if enc then Spec.Cfb.EncryptFinal ciph 16 s.mem s'.mem (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8).toNat
    else Spec.Cfb.DecryptFinal ciph 16 s.mem s'.mem (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- The postcondition in direction `enc`. -/
abbrev finalPost (enc : Bool) : Spec.Cfb.aesFinalSig.Post X86_64.abi.ptrBits :=
  if enc then encryptFinalPost X86_64.abi.ptrBits else decryptFinalPost X86_64.abi.ptrBits

/-- The contract the frame needs: the shared one, with `save`, 48 bytes, as
a seventh argument, and 16 bytes of stack (the return addresses of the
whole-block function and of the block function it calls). -/
abbrev finalScratchContract (enc : Bool) : Contract isa :=
  Sig.scratchContract X86_64.abi Spec.Cfb.aesFinalSig "save" .u64 6 (finalPre X86_64.abi.ptrBits)
    (finalPost enc) false 16

def finalSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8009 then 0x60 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 48⟩]

theorem stackArgs_one (s : State) : List.map (stackArg s) (List.range 1) = [stackArg s 0] := rfl

theorem args_getD (s : State) : (s.gpr .rdi :: s.gpr .rsi :: s.gpr .rdx :: s.gpr .rcx :: s.gpr .r8 :: s.gpr .r9 ::
    List.map (stackArg s) (List.range 1)).getD 6 0 = stackArg s 0 := rfl

theorem final_implies (enc : Bool) : (finalX86_64 enc).Implies (finalScratchContract enc) where
  pre := by
    intro s h
    sig_pre [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Cfb.aesFinalSig, finalPre, finalPost, abi, argRegs, finalX86_64, args_getD, stackArgs_one,
      List.append_eq] at h
    sig_pre [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Cfb.aesFinalSig, finalPre, finalPost, abi, argRegs, finalX86_64, args_getD, stackArgs_one,
      List.append_eq] at h
    sig_split h
    sig_reduce [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Cfb.aesFinalSig, finalPre, finalPost, abi, argRegs, finalX86_64, args_getD, stackArgs_one,
      List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
  post := by
    cases enc <;> sig_implies_post [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Cfb.aesFinalSig, finalPre, finalPost, abi, argRegs, finalX86_64, args_getD, stackArgs_one,
      List.append_eq, encryptFinalPost, decryptFinalPost]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Cfb.aesFinalSig, finalPre, finalPost, abi, argRegs, finalX86_64, args_getD, stackArgs_one,
      List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7
    exact ⟨h2, h3, h4, h5, h6, h7, h1, h⟩
  sat := by
    sig_implies_sat [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Cfb.aesFinalSig, finalPre, finalPost, abi, argRegs, finalX86_64, args_getD, stackArgs_one,
      List.append_eq] [finalSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using finalSatState

/-! ## Runs of the blocks -/

open VG.X86_64.RegUpd VG.Impl.AesCfb.X86_64

theorem offset_nat (i : Nat) : BitVec.ofInt 64 (i : Int) = BitVec.ofNat 64 i := rfl

theorem loadSave_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) :
    runBlock isa loadSave s = some (s.setReg .rax (stackArg s 0)) := by
  have e : s.gpr .rsp + BitVec.ofNat 64 8 = stackArgAddr s 0 := rfl
  simp only [loadSave, runBlock_cons, runStep_some, runBlock_nil, Impl.AesCbc.X86_64.at_, exec, readSrc,
    State.load64, State.ea, offset_nat, e, hr, ↓reduceIte, Option.map_some]
  rfl

theorem signExtend_15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide

theorem moves_ok (s : State) :
    ∃ s', runBlock isa finalMoves s = some s' ∧
      s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rsi ∧ s'.gpr .r12 = s.gpr .rdx ∧
      s'.gpr .r15 = s.gpr .r9 ∧ s'.gpr .r14 = s.gpr .r8 &&& 15#64 ∧
      s'.gpr .r13 = s.gpr .r8 - (s.gpr .r8 &&& 15#64) + s.gpr .rcx ∧ s'.gpr .r8 = s.gpr .r8 >>> 4 ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdx = s.gpr .rdx ∧
      s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rax = s.gpr .rax ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, finalMoves, runBlock_cons,
      runStep_some, runBlock_nil, reduceExec, execAlu, execShift, readSrc, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, Nat.reduceLeDiff, and_self, signExtend_15]
    rfl, ?_⟩
  simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg,
    rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags, reduceCtorEq, ↓reduceIte, and_self]

/-! ## The arguments, by name -/

section
variable (s₀ : State)

abbrev fW : Addr := s₀.gpr .rdi
abbrev fR : Nat := (s₀.gpr .rsi).toNat
abbrev fIv : Addr := s₀.gpr .rdx
abbrev fD : Addr := s₀.gpr .rcx
abbrev fL : Nat := (s₀.gpr .r8).toNat
abbrev fS : Addr := s₀.gpr .r9
abbrev fV : Addr := stackArg s₀ 0
abbrev fSp : Addr := s₀.gpr .rsp
/-- The number of whole blocks, and of the bytes after them. -/
abbrev fN : Nat := fL s₀ / 16
abbrev fU : Nat := fL s₀ % 16
/-- The data after the whole blocks. -/
abbrev fT : Addr := fD s₀ + BitVec.ofNat 64 (16 * fN s₀)

abbrev fSch : Region := ⟨fW s₀, 240⟩
abbrev fIvR : Region := ⟨fIv s₀, 16⟩
abbrev fData : Region := ⟨fD s₀, fL s₀⟩
abbrev fBlk : Region := ⟨fD s₀, 16 * fN s₀⟩
abbrev fTail : Region := ⟨fT s₀, fU s₀⟩
abbrev fScr : Region := ⟨fS s₀, 2176⟩
abbrev fSv : Region := ⟨fV s₀, 48⟩
abbrev fArg : Region := ⟨stackArgAddr s₀ 0, 8⟩
abbrev fStk : Region := below (fSp s₀) 16

/-- The key schedule, the chaining value and the whole blocks on entry. -/
abbrev fWk : List Byte := bytesAt s₀.mem (fW s₀) (16 * (fR s₀ + 1))
abbrev fIv0 : List Byte := bytesAt s₀.mem (fIv s₀) 16
abbrev fBlks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (fD s₀) (fN s₀)

/-- The registers' values once `save` is in `rax`. -/
abbrev fG : Reg → BitVec 64 := (s₀.setReg .rax (fV s₀)).gpr

/-- The memory once the registers are saved. -/
abbrev svMem : Mem := Spill.saveMem s₀.mem (fV s₀) (fG s₀) finalSaved

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  sp_lo : 16 ≤ (fSp s₀).toNat
  sp_hi : (fSp s₀).toNat + 16 ≤ 2 ^ 64
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
  ret_sch : (⟨fSp s₀, 8⟩ : Region).Disjoint (fSch s₀)
  ret_iv : (⟨fSp s₀, 8⟩ : Region).Disjoint (fIvR s₀)
  ret_data : (⟨fSp s₀, 8⟩ : Region).Disjoint (fData s₀)
  ret_scr : (⟨fSp s₀, 8⟩ : Region).Disjoint (fScr s₀)
  ret_sv : (⟨fSp s₀, 8⟩ : Region).Disjoint (fSv s₀)
  ret_arg : (⟨fSp s₀, 8⟩ : Region).Disjoint (fArg s₀)
  stk_sch : (fStk s₀).Disjoint (fSch s₀)
  stk_iv : (fStk s₀).Disjoint (fIvR s₀)
  stk_data : (fStk s₀).Disjoint (fData s₀)
  stk_scr : (fStk s₀).Disjoint (fScr s₀)
  stk_sv : (fStk s₀).Disjoint (fSv s₀)
  stk_arg : (fStk s₀).Disjoint (fArg s₀)
  sch_wrap : (fW s₀).toNat + 240 ≤ 2 ^ 64
  iv_wrap : (fIv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (fD s₀).toNat + fL s₀ ≤ 2 ^ 64
  scr_wrap : (fS s₀).toNat + 2176 ≤ 2 ^ 64
  sv_wrap : (fV s₀).toNat + 48 ≤ 2 ^ 64
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem FPre.of {enc : Bool} {s₀ : State} (h : (finalX86_64 enc).pre s₀) : FPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩

/-! ## Regions -/

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)

theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [fN_eq, fU_eq]; omega)

theorem FPre.blk_wrap : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := Nat.mul_div_le (fL s₀) 16; rw [fN_eq]; omega

omit hp in
theorem n_lt (s₀ : State) : fN s₀ < 2 ^ 64 := by
  have := (s₀.gpr .r8).isLt; have : fL s₀ = (s₀.gpr .r8).toNat := rfl; rw [fN_eq]; omega

theorem FPre.sched_sub : Region.Sub ⟨fW s₀, 16 * (fR s₀ + 1)⟩ (fSch s₀) :=
  Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)

end

/-- The return address of a call from `sp`, and the stack its callee uses,
are in the 16 bytes below it. -/
theorem ret8_sub (sp : Addr) : Region.Sub ⟨sp - 8, 8⟩ (below sp 16) := Offset.sub_below sp (by decide) (by decide)
theorem below8_sub (sp : Addr) : Region.Sub (below sp 8) (below sp 16) := Offset.sub_below sp (by decide) (by decide)
theorem callee8_sub (sp : Addr) : Region.Sub (below (sp - 8) 8) (below sp 16) := below_callee sp 8

/-- The `n` blocks at `D` are unchanged outside a frame that misses them. -/
theorem blocksAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨D, 16 * n⟩ : Region).Disjoint r) :
    Spec.Cbc.blocksAt m' D n = Spec.Cbc.blocksAt m D n :=
  List.map_congr_left fun j hj => AesCbc.X86_64.bytesAt_frame hf
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; omega))) (by decide)

/-- The save changes only `save`. -/
theorem svMem_frame (s₀ : State) : Frame [fSv s₀] s₀.mem (svMem s₀) :=
  Spill.saveMem_frame_base _ _ _ finalSaved (by decide) (by decide)

/-! ## Saving the registers -/

theorem and15 (x : BitVec 64) : x &&& 15#64 = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : Nat) % 2 ^ 64 = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 (x : BitVec 64) : x >>> 4 = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem tail_addr (x c : BitVec 64) :
    x - BitVec.ofNat 64 (x.toNat % 16) + c = c + BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem final_load_wp {s₀ : State} (hp : FPre s₀) :
    WP isa (.block loadSave) s₀ (· = s₀.setReg .rax (fV s₀)) :=
  WP.of_runBlock ⟨_, loadSave_ok s₀ (by rw [hp.rd, hp.wr]; exact ⟨fArg s₀, by simp, Region.contains_self _ _⟩), rfl⟩

/-- What saving the registers and setting up the arguments leaves. -/
structure Setup (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = fW s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = fIv s₀
  r13 : s.gpr .r13 = fT s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (fU s₀)
  r15 : s.gpr .r15 = fS s₀
  rdi : s.gpr .rdi = fW s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  rdx : s.gpr .rdx = fIv s₀
  rcx : s.gpr .rcx = fD s₀
  r8 : s.gpr .r8 = BitVec.ofNat 64 (fN s₀)
  r9 : s.gpr .r9 = fS s₀
  rsp : s.gpr .rsp = fSp s₀
  mem : s.mem = svMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem saved_slots : ∀ p ∈ finalSaved, p.2 + 8 ≤ 48 := by decide

theorem final_setup_wp {s₀ : State} (hp : FPre s₀) :
    WP isa (.block finalSetup) (s₀.setReg .rax (fV s₀)) (Setup s₀) := by
  have hw : ∀ p ∈ finalSaved, InRegions (s₀.setReg .rax (fV s₀)).wr
      (Spill.slot ((s₀.setReg .rax (fV s₀)).gpr .rax) p.2) 8 := by
    intro p hp'
    rw [wr_setReg, gpr_setReg_self, hp.wr]
    have := saved_slots p hp'
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  show WP isa (.block (Spill.saveCode .rax finalSaved ++ finalMoves)) _ _
  refine Spill.save_then .rax finalSaved hw ?_
  refine WP.mono (WP.of_runBlock (moves_ok _))
    fun s' ⟨rbx, rbp, r12, r15, r14, r13, r8, rdi, rsi, rdx, rcx, r9, rsp, _, mem, rd, wr⟩ => ?_
  simp only [gpr_setReg, reduceCtorEq, ↓reduceIte] at rbx rbp r12 r15 r14 r13 r8 rdi rsi rdx rcx r9 rsp
  exact ⟨rbx, rbp, r12, by rw [r13, and15, tail_addr], by rw [r14, and15], r15, rdi, rsi, rdx, rcx,
    by rw [r8, shr4], r9, rsp, by rw [mem, mem_setReg, gpr_setReg_self], by rw [rd, rd_setReg],
    by rw [wr, wr_setReg]⟩

/-! ## The call of the whole-block function -/

open VG.Proof.AesCbc (Mode cts aesWith_state)
open VG.Proof.AesCbc.X86_64 (modeX86_64 CallPre CallPost blk_call callEntry_frame bytesAt_frame)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-- The save and a call's return address change only `save` and the stack. -/
theorem entry_frame {s₀ : State} {s : State} (hm : s.mem = svMem s₀) (hsp : s.gpr .rsp = fSp s₀) :
    Frame [fSv s₀, fStk s₀] s₀.mem s.callEntry.mem := by
  have f₁ : Frame [fSv s₀, fStk s₀] s₀.mem s.mem := by
    rw [hm]; exact (svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
  have f₂ : Frame [fSv s₀, fStk s₀] s.mem s.callEntry.mem :=
    (callEntry_frame s).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fStk s₀, by simp, by rw [hsp]; exact below8_sub _⟩
  exact f₁.trans f₂

/-- What the call of the whole-block function leaves, for the mode `M`. -/
structure Whole (M : Mode) (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = fW s₀
  rbp : s.gpr .rbp = s₀.gpr .rsi
  r12 : s.gpr .r12 = fIv s₀
  r13 : s.gpr .r13 = fT s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (fU s₀)
  r15 : s.gpr .r15 = fS s₀
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fBlk s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  iv : bytesAt s.mem (fIv s₀) 16 = M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)

theorem toNat_n (s₀ : State) : (BitVec.ofNat 64 (fN s₀)).toNat = fN s₀ := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (n_lt s₀)]

/-- The whole-block function's precondition at the call, with the regions it
is given, which ours cover. -/
theorem whole_pre {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Setup s₀ s) :
    (modeX86_64 M).pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, fBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, fBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, fBlk s₀, fScr s₀] s.wr := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp, toNat_n]
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_data.sub_right (blk_sub s₀), hp.sch_scr,
      hp.iv_data.sub_right (blk_sub s₀), hp.iv_scr, hp.data_scr.sub_left (blk_sub s₀),
      hp.stk_iv.sub_left (ret8_sub _), (hp.stk_data.sub_left (ret8_sub _)).sub_right (blk_sub s₀),
      hp.stk_scr.sub_left (ret8_sub _), hp.stk_sch.sub_left (callee8_sub _), hp.stk_iv.sub_left (callee8_sub _),
      (hp.stk_data.sub_left (callee8_sub _)).sub_right (blk_sub s₀), hp.stk_scr.sub_left (callee8_sub _),
      hp.iv_wrap, hp.blk_wrap, hp.scr_wrap, hp.rounds⟩
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
theorem whole_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86_64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86_64 M).post s s')
    (hsp : NoSp whole) (hd : whole.depth = 1) {s₀ : State} (hp : FPre s₀) {s : State} (h : Setup s₀ s) :
    WP isa (.call name whole) s (Whole M s₀) := by
  have ef := entry_frame h.mem h.rsp
  have eW : bytesAt s.callEntry.mem (fW s₀) (16 * (fR s₀ + 1)) = fWk s₀ :=
    bytesAt_frame ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.sch_sv.sub_left hp.sched_sub
      · exact hp.stk_sch.symm.sub_left hp.sched_sub) (by rcases hp.rounds with h | h | h <;> omega)
  have eIv : bytesAt s.callEntry.mem (fIv s₀) 16 = fIv0 s₀ :=
    bytesAt_frame ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.iv_sv
      · exact hp.stk_iv.symm) (by decide)
  have eB : Spec.Cbc.blocksAt s.callEntry.mem (fD s₀) (fN s₀) = fBlks s₀ :=
    blocksAt_frame' ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_sv.sub_left (blk_sub s₀)
      · exact hp.stk_data.symm.sub_left (blk_sub s₀))
  obtain ⟨hpre, hc, hw⟩ := whole_pre (M := M) hp h
  refine WP.call (k := modeX86_64 M) hv hsp (by rw [hd]; decide) (rd := [fSch s₀])
    (wr := [fIvR s₀, fBlk s₀, fScr s₀]) hpre hc hw ?_
  · intro s' rd' wr' cs' fr' _ ⟨s₂, mem₂, _, post₂⟩
    rw [hd, h.rsp, h.mem] at fr'
    simp only [modeX86_64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_gpr s (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rsi ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr s (by decide : Reg.rcx ≠ .rsp),
      State.callEntry_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, toNat_n, mem₂, eW, eIv,
      eB] at post₂
    exact ⟨by rw [cs' .rbx (by simp [calleeSaved]), h.rbx], by rw [cs' .rbp (by simp [calleeSaved]), h.rbp],
      by rw [cs' .r12 (by simp [calleeSaved]), h.r12], by rw [cs' .r13 (by simp [calleeSaved]), h.r13],
      by rw [cs' .r14 (by simp [calleeSaved]), h.r14], by rw [cs' .r15 (by simp [calleeSaved]), h.r15],
      by rw [cs' .rsp (by simp [calleeSaved]), h.rsp], by rw [rd', h.rd], by rw [wr', h.wr], fr', post₂.1,
      post₂.2⟩

/-! ## The partial last segment -/

theorem test_ok (s : State) :
    runBlock isa [.alu .test .r14 (.reg .r14)] s = some (arithFlags s (s.gpr .r14 &&& s.gpr .r14) false false) := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu, readSrc, Option.bind_some]

theorem beq_zero' {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

/-- The test sets ZF if no bytes are left after the whole blocks. -/
theorem final_test_wp {M : Mode} {s₀ s : State} (h : Whole M s₀ s) :
    WP isa (.block [.alu .test .r14 (.reg .r14)]) s fun s' => Whole M s₀ s' ∧ s'.zf = some (decide (fU s₀ = 0)) :=
  WP.of_runBlock ⟨_, test_ok s, ⟨h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15, h.rsp, h.rd, h.wr, h.frame, h.blocks, h.iv⟩, by
    have eU := fU_eq s₀
    rw [zf_arithFlags, BitVec.and_self, h.r14, beq_zero' (by have := Nat.mod_lt (fL s₀) (by decide : 16 > 0); omega)]⟩

theorem bytesAt_getD (m : Mem) (p : Addr) {n q : Nat} (hq : q < n) :
    (bytesAt m p n).getD q 0 = m (p + BitVec.ofNat 64 q) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hq]

/-- What the function leaves before restoring the registers. -/
structure Done (M : Mode) (s₀ s : State) : Prop where
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q) ^^^
    (Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))).getD q 0
  iv : bytesAt s.mem (fIv s₀) 16 = if fU s₀ = 0 then M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
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
  ⟨h.rsp, h.rd, h.wr, h.frame', h.blocks, fun q hq => absurd hq (by omega), by rw [ite_eq_left hu]; exact h.iv⟩

/-- Everything the function writes, from entry. -/
theorem big_frame {s₀ : State} {m : Mem} (hf : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) m) :
    Frame [fIvR s₀, fData s₀, fScr s₀, fSv s₀, fStk s₀] s₀.mem m :=
  ((svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h])

theorem FPre.sched_big {s₀ : State} (hp : FPre s₀) :
    ∀ r ∈ [fIvR s₀, fData s₀, fScr s₀, fSv s₀, fStk s₀], (⟨fW s₀, 16 * (fR s₀ + 1)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left hp.sched_sub
  · exact hp.sch_data.sub_left hp.sched_sub
  · exact hp.sch_scr.sub_left hp.sched_sub
  · exact hp.sch_sv.sub_left hp.sched_sub
  · exact hp.stk_sch.symm.sub_left hp.sched_sub

theorem FPre.sched_len {s₀ : State} (hp : FPre s₀) : 16 * (fR s₀ + 1) ≤ 2 ^ 64 := by
  rcases hp.rounds with h | h | h <;> omega

theorem final_ivArgs_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.block Impl.AesOfb.X86_64.ivArgs) s fun s' =>
      Whole M s₀ s' ∧ CallPre s' (fW s₀) (fIv s₀) (fS s₀) (fR s₀) := by
  obtain ⟨s', run, rdi, rsi, rdx, rcx, r8, cs, mem, rd, wr⟩ := AesOfb.X86_64.ivArgs_ok s
  have rsp' : s'.gpr .rsp = fSp s₀ := by rw [cs .rsp (by simp [calleeSaved]), h.rsp]
  refine WP.of_runBlock ⟨s', run, ⟨by rw [cs .rbx (by simp [calleeSaved]), h.rbx],
    by rw [cs .rbp (by simp [calleeSaved]), h.rbp], by rw [cs .r12 (by simp [calleeSaved]), h.r12],
    by rw [cs .r13 (by simp [calleeSaved]), h.r13], by rw [cs .r14 (by simp [calleeSaved]), h.r14],
    by rw [cs .r15 (by simp [calleeSaved]), h.r15], rsp', by rw [rd, h.rd], by rw [wr, h.wr],
    by rw [mem]; exact h.frame, by rw [mem]; exact h.blocks, by rw [mem]; exact h.iv⟩, ?_⟩
  exact {
    rdi := by rw [rdi, h.rbx]
    rsi := by rw [rsi, h.rbp]; apply BitVec.eq_of_toNat_eq; simp
    rdx := by rw [rdx, h.r12]
    rcx := rcx
    r8 := by rw [r8, h.r15]
    rounds := hp.rounds
    wd := hp.sch_iv
    ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
    ds := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    stkW := by rw [rsp']; exact hp.stk_sch.sub_left (below8_sub _)
    stkD := by rw [rsp']; exact hp.stk_iv.sub_left (below8_sub _)
    stkS := by rw [rsp']; exact (hp.stk_scr.sub_left (below8_sub _)).sub_right (Region.sub_prefix (by decide))
    wrap := hp.iv_wrap
    reads := by
      rw [rd, wr, h.rd, h.wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr, h.wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩ }

/-- What the call of the block function on the chaining value leaves. -/
structure Ciph (M : Mode) (s₀ s : State) : Prop where
  r12 : s.gpr .r12 = fIv s₀
  r13 : s.gpr .r13 = fT s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (fU s₀)
  rsp : s.gpr .rsp = fSp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tailb : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q)
  iv : bytesAt s.mem (fIv s₀) 16 =
    Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))

theorem final_ciph_wp (v : BlocksImpl) {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State}
    (h : Whole M s₀ s ∧ CallPre s (fW s₀) (fIv s₀) (fS s₀) (fR s₀)) :
    WP isa (.call v.enc.name v.enc.code) s (Ciph M s₀) := by
  obtain ⟨hw, hc⟩ := h
  refine WP.mono (blk_call v.encOk v.encNosp v.encDepth hc) fun s' c => ?_
  have stk : Region.Sub (below (s.gpr .rsp) 8) (fStk s₀) := by rw [hw.rsp]; exact below8_sub _
  have fc : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] s.mem s'.mem :=
    c.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨fScr s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨fStk s₀, by simp, stk⟩
  have big := big_frame hw.frame'
  have tailD : ∀ r ∈ [fIvR s₀, ⟨fS s₀, 2048⟩, below (s.gpr .rsp) 8], (fTail s₀).Disjoint r := by
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
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by
    show fU s₀ ≤ 2 ^ 64; have := Nat.mod_lt (fL s₀) (by decide : 16 > 0); have := fU_eq s₀; omega
  refine ⟨by rw [c.saved .r12 (by simp [calleeSaved]), hw.r12], by rw [c.saved .r13 (by simp [calleeSaved]), hw.r13],
    by rw [c.saved .r14 (by simp [calleeSaved]), hw.r14], by rw [c.saved .rsp (by simp [calleeSaved]), hw.rsp],
    by rw [c.rd, hw.rd], by rw [c.wr, hw.wr], hw.frame'.trans fc, ?_, fun q hq => ?_, ?_⟩
  · rw [blocksAt_frame' c.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (blk_sub s₀)
      · exact (hp.data_scr.sub_left (blk_sub s₀)).sub_right (Region.sub_prefix (by decide))
      · exact (hp.stk_data.sub_right (blk_sub s₀)).symm.sub_right stk]
    exact hw.blocks
  · rw [c.frame.bytes tailD hlen hq, hw.frame.bytes tailW hlen hq, (svMem_frame s₀).bytes tailS hlen hq]
  · rw [c.out, ← aesWith_state, bytesAt_frame big hp.sched_big hp.sched_len, hw.iv]

theorem toNat_tail {s₀ : State} (hp : FPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem final_xor_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Ciph M s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block [.mov .rax (.reg .r12)]) (.loop (.block (Impl.Modes.X86_64.xorByte .r13 .r14)) .ne)) s
      (Done M s₀) := by
  refine WP.seq (WP.of_runBlock ⟨s.setReg .rax (s.gpr .r12), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, Option.map_some], ?_⟩)
  have hU : fU s₀ < 16 := Nat.mod_lt _ (by decide)
  have hT := toNat_tail hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have xp : Modes.X86_64.XPre (s.setReg .rax (s.gpr .r12)) (fIv s₀) (fT s₀) (fU s₀) .r13 .r14 := {
    pos := by omega
    small := by omega
    fitK := by have := hp.iv_wrap; omega
    fitR := by rw [hT]; omega
    disj := (hp.iv_data.sub_left (Region.sub_prefix (by omega))).sub_right (tail_sub s₀)
    rdK := fun q hq => by
      rw [rd_setReg, wr_setReg, h.rd, h.wr, hp.rd, hp.wr]
      exact ⟨fIvR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    wrR := fun q hq => by
      rw [wr_setReg, h.wr, hp.wr]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show fT s₀ + BitVec.ofNat 64 q = fD s₀ + BitVec.ofNat 64 (16 * fN s₀ + q) from Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega)
    dl := by decide
    dRax := by decide
    dR10 := by decide
    dRcx := by decide }
  have x0 : Modes.X86_64.XInv (s.setReg .rax (s.gpr .r12)) (fIv s₀) (fT s₀) (fU s₀) .r13 .r14 0
      (s.setReg .rax (s.gpr .r12)) := {
    rax := by rw [gpr_setReg_self, h.r12]; exact (BitVec.add_zero _).symm
    dat := by rw [gpr_setReg_of_ne _ _ (by decide), h.r13]; exact (BitVec.add_zero _).symm
    left := by rw [gpr_setReg_of_ne _ _ (by decide), h.r14, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Modes.X86_64.xorLoop_wp xp x0) fun s' d => ?_
  have ivT : ∀ r ∈ [fTail s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.sub_right (tail_sub s₀)
  refine ⟨by rw [d.gpr .rsp (by decide) (by decide) (by decide) (by decide) (by decide), gpr_setReg_of_ne _ _ (by decide),
      h.rsp], by rw [d.rd, rd_setReg, h.rd], by rw [d.wr, wr_setReg, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact h.frame.trans (d.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' d.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact h.blocks
  · rw [d.data q hq, mem_setReg, h.tailb q hq, ← bytesAt_getD s.mem (fIv s₀) (show q < 16 by omega), h.iv]
  · rw [ite_eq_right hu, bytesAt_frame d.frame ivT (by decide), mem_setReg, h.iv]

theorem final_mid_wp (v : BlocksImpl) {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s)
    (hz : s.zf = some (decide (fU s₀ = 0))) :
    WP isa (.ite .e (.block []) (finalTail v.enc)) s (Done M s₀) := by
  have ev : isa.eval .e s = some (decide (fU s₀ = 0)) := hz
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [ev, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [ev, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (final_ivArgs_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (final_ciph_wp v hp h₁) fun _ h₂ => final_xor_wp hp h₂ hu))

/-! ## Restoring the registers -/

theorem calleeSaved_ne_rax' {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `save`'s address, on the stack, is unchanged when the registers are
restored. -/
theorem Done.saveArg {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Done M s₀ s) :
    stackArgAddr s 0 = stackArgAddr s₀ 0 ∧ stackArg s 0 = fV s₀ := by
  have big := big_frame h.frame
  have hA : stackArgAddr s 0 = stackArgAddr s₀ 0 := by simp only [stackArgAddr, h.rsp]
  refine ⟨hA, ?_⟩
  show s.mem.readW (stackArgAddr s 0) 64 = s₀.mem.readW (stackArgAddr s₀ 0) 64
  rw [hA]
  refine big.readW (r := fArg s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.iv_arg.symm
  · exact hp.data_arg.symm
  · exact hp.scr_arg.symm
  · exact hp.sv_arg.symm
  · exact hp.stk_arg.symm

theorem end_load_ok {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Done M s₀ s) :
    runBlock isa loadSave s = some (s.setReg .rax (fV s₀)) := by
  obtain ⟨hA, hV⟩ := h.saveArg hp
  rw [← hV]
  exact loadSave_ok s (by rw [h.rd, h.wr, hp.rd, hp.wr, hA]; exact ⟨fArg s₀, by simp, Region.contains_self _ _⟩)

theorem final_end_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Done M s₀ s) :
    WP isa (.seq (.block loadSave) (.block finalRestore)) s fun s' => gprPreserved s₀ s' ∧ s'.mem = s.mem := by
  have big := big_frame h.frame
  refine WP.seq (WP.of_runBlock ⟨_, end_load_ok hp h, ?_⟩)
  have hs : Spill.Saved (s.setReg .rax (fV s₀)).mem ((s.setReg .rax (fV s₀)).gpr .rax) (fG s₀) finalSaved := by
    rw [mem_setReg, gpr_setReg_self]
    refine (Spill.saveMem_saved _ _ _ _ (by decide)).frame h.frame fun p hp' r hr => ?_
    have hsub : Region.Sub ⟨Spill.slot (fV s₀) p.2, 8⟩ (fSv s₀) := Offset.sub_base _ (saved_slots p hp')
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.iv_sv.symm.sub_left hsub
    · exact hp.data_sv.symm.sub_left hsub
    · exact hp.scr_sv.symm.sub_left hsub
    · exact hp.stk_sv.symm.sub_left hsub
  show WP isa (.block (Spill.restoreCode .rax finalSaved)) _ _
  refine WP.mono (Spill.restore_ok .rax finalSaved (fG s₀) _ (by decide) (fun p hp' => ?_) hs)
    fun s' ⟨g₁, g₂, mem', _, _⟩ => ?_
  · rw [rd_setReg, wr_setReg, gpr_setReg_self, h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨fSv s₀, by simp, Offset.contains_base _ this (by omega)⟩
  · have cs := Spill.calleeSaved_ok g₁ g₂ (by decide)
      (show _ = (s₀.setReg .rax (fV s₀)).gpr .rsp by
        rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide), h.rsp])
    refine ⟨⟨fun r hr => by rw [cs r hr]; exact gpr_setReg_of_ne _ _ (calleeSaved_ne_rax' hr), ?_⟩,
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

theorem final_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86_64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86_64 M).post s s')
    (hsp : NoSp whole) (hd : whole.depth = 1) (v : BlocksImpl) {s₀ : State} (hp : FPre s₀) :
    WP isa (final name whole v.enc) s₀ fun s' => gprPreserved s₀ s' ∧ ∃ s₁, Done M s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_load_wp hp) fun s₁ e₁ => ?_)
  subst e₁
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (whole_wp hv hsp hd hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (final_test_wp h₃) fun s₄ ⟨h₄, z₄⟩ => ?_)
  refine WP.seq (WP.mono (final_mid_wp v hp h₄ z₄) fun s₅ h₅ => ?_)
  exact WP.mono (final_end_wp hp h₅) fun _ ⟨g, m⟩ => ⟨g, s₅, h₅, m⟩

/-- The specification's results, from what the function leaves. -/
theorem final_post {enc : Bool} {s₀ s₁ s' : State} (h : Done (cfbMode enc) s₀ s₁) (hm : s'.mem = s₁.mem) :
    (finalX86_64 enc).post s₀ s' := by
  cases enc
  · show Spec.Cfb.DecryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
    exact decryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)
  · show Spec.Cfb.EncryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
    exact encryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)

theorem final_correct {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86_64 (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (cfbMode enc)).post s s')
    (hsp : NoSp whole) (hd : whole.depth = 1) (v : BlocksImpl)
    (hmx : (final name whole v.enc).allInstrs (fun i => !loadsMxcsr i) = true) (s : State)
    (hs : (finalX86_64 enc).pre s) :
    ∃ t s', Exec isa (final name whole v.enc) s t s' ∧ abiPreserved s s' ∧ (finalX86_64 enc).post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp hv hsp hd v (FPre.of hs)
  exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, final_post h₁ hm⟩

/-! ## The code's properties -/

theorem noSp_of_all {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  intro i hi
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  simpa using h i hi

theorem all_of_noSp {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simp [h i hi]

theorem encrypt_noSp (v : BlocksImpl) : NoSp (encrypt v.enc) :=
  noSp_of_all (by
    simp only [encrypt, Impl.AesCbc.X86_64.whole, body, Code.allInstrs, all_of_noSp v.encNosp]
    decide +kernel)

theorem decrypt_noSp (v : BlocksImpl) : NoSp (decrypt v.enc) :=
  noSp_of_all (by
    simp only [decrypt, Impl.AesCbc.X86_64.batched, Impl.AesCbc.X86_64.groups, decGroup, body, Code.allInstrs,
      all_of_noSp v.encNosp]
    decide +kernel)

theorem encrypt_depth (v : BlocksImpl) : (encrypt v.enc).depth = 1 := by
  simp only [encrypt, Impl.AesCbc.X86_64.whole, body, Code.depth, v.encDepth]
  decide

theorem decrypt_depth (v : BlocksImpl) : (decrypt v.enc).depth = 1 := by
  simp only [decrypt, Impl.AesCbc.X86_64.batched, Impl.AesCbc.X86_64.groups, decGroup, body, Code.depth,
    v.encDepth]
  decide

theorem encryptFinal_mx (v : BlocksImpl) :
    (encryptFinal v.enc v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encryptFinal, final, finalTail, Code.allInstrs, encrypt_mx v, v.encMxcsr]
  decide +kernel

theorem decryptFinal_mx (v : BlocksImpl) :
    (decryptFinal v.enc v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decryptFinal, final, finalTail, Code.allInstrs, decrypt_mx v, v.encMxcsr]
  decide +kernel

theorem encryptFinal_spSafe (v : BlocksImpl) :
    (encryptFinal v.enc v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encryptFinal, final, finalTail, Code.all, encrypt_spSafe v, v.encSpSafe]
  decide +kernel

theorem decryptFinal_spSafe (v : BlocksImpl) :
    (decryptFinal v.enc v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decryptFinal, final, finalTail, Code.all, decrypt_spSafe v, v.encSpSafe]
  decide +kernel

theorem encryptFinal_xdepth (v : BlocksImpl) : (encryptFinal v.enc v.suffix).x86_64Depth ≤ 16 := by
  simp only [encryptFinal, final, finalTail, encrypt, Impl.AesCbc.X86_64.whole, body, Code.x86_64Depth,
    v.encNoStack]
  decide

/-- The whole-block decryption uses 8 bytes of stack, the return address of
its calls of the block function. -/
theorem decrypt_xdepth (v : BlocksImpl) : (decrypt v.enc).x86_64Depth = 8 := by
  simp only [decrypt, Impl.AesCbc.X86_64.batched, Impl.AesCbc.X86_64.groups, decGroup, body, Code.x86_64Depth,
    v.encNoStack]
  decide

theorem decryptFinal_xdepth (v : BlocksImpl) : (decryptFinal v.enc v.suffix).x86_64Depth ≤ 16 := by
  simp only [decryptFinal, final, finalTail, Code.x86_64Depth, decrypt_xdepth v, v.encNoStack]
  decide

/-! ## Constant time -/

theorem final_rel {enc : Bool} {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86_64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86_64 M).post s s')
    (hct : ConstantTime isa (modeX86_64 M).pre (modeX86_64 M).pub whole)
    (hsp : NoSp whole) (hd : whole.depth = 1) (v : BlocksImpl) {s₀ s₀' : State}
    (h0 : (finalX86_64 enc).pre s₀) (h0' : (finalX86_64 enc).pre s₀') (hq : (finalX86_64 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (final name whole v.enc) fun _ _ => True := by
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  obtain ⟨qW, qR, qIv, qD, qL, qS, qSp, qV⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, qD, qN]
  -- `save` to `rax`.
  obtain ⟨_, t₁⟩ : ∃ h, (taint.check (Taint.ofRegs [.rsp]) (.block loadSave) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact Taint.agree_ofRegs fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact qSp) t₁).wp
    (F₁ := (· = s₀.setReg .rax (fV s₀))) (F₂ := (· = s₀'.setReg .rax (fV s₀')))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨final_load_wp hp, final_load_wp hp'⟩
  -- The registers saved and the arguments set up.
  obtain ⟨_, t₂⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp, .rax])
      (.block finalSetup) h).isSome = true := ⟨_, by taint_decide⟩
  have r₂ := (RelCT.taint (A := taint)
    (P := fun a b => a = s₀.setReg .rax (fV s₀) ∧ b = s₀'.setReg .rax (fV s₀')) _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, reduceCtorEq, ↓reduceIte, qW, qR, qIv, qD, qL, qS, qSp, fV, qV]) t₂).wp
    (F₁ := Setup s₀) (F₂ := Setup s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨final_setup_wp hp, final_setup_wp hp'⟩
  -- The whole blocks.
  have r₃ := (RelCT.callEx (k := modeX86_64 M) (n := name) hv hct
    (P := fun a b => Setup s₀ a ∧ Setup s₀' b) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre (M := M) hp ha
      obtain ⟨pb, cb, wb⟩ := whole_pre (M := M) hp' hb
      refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb, by rw [ha.rsp, hb.rsp, fSp, fSp, qSp]⟩
      simp only [modeX86_64, State.withRegions_gpr, State.callEntry_rsp,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r9 ≠ .rsp),
        ha.rdi, ha.rsi, ha.rdx, ha.rcx, ha.r8, ha.r9, ha.rsp, hb.rdi, hb.rsi, hb.rdx, hb.rcx, hb.r8, hb.r9, hb.rsp]
      rw [fW, fW, fIv, fIv, fD, fD, fS, fS, fSp, fSp, qW, qR, qIv, qD, qS, qSp, qN]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).wp
    (F₁ := Whole M s₀) (F₂ := Whole M s₀')
    fun a b h => ⟨whole_wp hv hsp hd hp h.1, whole_wp hv hsp hd hp' h.2⟩
  -- The test.
  obtain ⟨_, t₄⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14]) (.block [.alu .test .r14 (.reg .r14)]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have r₄ := (RelCT.taint (A := taint)
    (P := fun a b => Whole M s₀ a ∧ Whole M s₀' b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.r14, h.2.r14, qU]) t₄).wp
    (F₁ := fun (s : State) => Whole M s₀ s ∧ s.zf = some (decide (fU s₀ = 0)))
    (F₂ := fun (s : State) => Whole M s₀' s ∧ s.zf = some (decide (fU s₀' = 0)))
    fun a b h => ⟨final_test_wp h.1, final_test_wp h.2⟩
  -- The partial last segment.
  obtain ⟨_, t₅⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp])
      (.block Impl.AesOfb.X86_64.ivArgs) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, t₆⟩ : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14])
      (.seq (.block [.mov .rax (.reg .r12)]) (.loop (.block (Impl.Modes.X86_64.xorByte .r13 .r14)) .ne)) h).isSome =
      true := ⟨_, by taint_decide⟩
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole M s₀ a ∧ Whole M s₀' b)
      (finalTail v.enc) fun a b => Done M s₀ a ∧ Done M s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₅ := (RelCT.taint (A := taint)
      (P := fun a b => Whole M s₀ a ∧ Whole M s₀' b) _
      (fun a b h => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [h.1.rbx, h.2.rbx, fW, fW, qW]
        · rw [h.1.rbp, h.2.rbp, qR]
        · rw [h.1.r12, h.2.r12, fIv, fIv, qIv]
        · rw [h.1.r15, h.2.r15, fS, fS, qS]
        · rw [h.1.rsp, h.2.rsp, fSp, fSp, qSp]) t₅).wp
      (F₁ := fun (s : State) => Whole M s₀ s ∧ CallPre s (fW s₀) (fIv s₀) (fS s₀) (fR s₀))
      (F₂ := fun (s : State) => Whole M s₀' s ∧ CallPre s (fW s₀') (fIv s₀') (fS s₀') (fR s₀'))
      fun a b h => ⟨final_ivArgs_wp hp h.1, final_ivArgs_wp hp' h.2⟩
    have a₆ := (AesCbc.X86_64.blk_rel (b := v.enc) v.encOk v.encCt
      (P := fun a b => (Whole M s₀ a ∧ CallPre a (fW s₀) (fIv s₀) (fS s₀) (fR s₀)) ∧
        (Whole M s₀' b ∧ CallPre b (fW s₀') (fIv s₀') (fS s₀') (fR s₀')))
      fun a b h => by
        have e₂ := h.2.2
        have eW : fW s₀' = fW s₀ := qW.symm
        have eIv : fIv s₀' = fIv s₀ := qIv.symm
        have eS : fS s₀' = fS s₀ := qS.symm
        have eR : fR s₀' = fR s₀ := by simp only [fR, qR]
        rw [eW, eIv, eS, eR] at e₂
        exact ⟨_, _, _, _, h.1.2, e₂, by rw [h.1.1.rsp, h.2.1.rsp, fSp, fSp, qSp]⟩).wp
      (F₁ := Ciph M s₀) (F₂ := Ciph M s₀')
      fun a b h => ⟨final_ciph_wp v hp h.1, final_ciph_wp v hp' h.2⟩
    have a₇ := (RelCT.taint (A := taint)
      (P := fun a b => Ciph M s₀ a ∧ Ciph M s₀' b) _
      (fun a b h => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.r12, h.2.r12, fIv, fIv, qIv]
        · rw [h.1.r13, h.2.r13, qT]
        · rw [h.1.r14, h.2.r14, qU]) t₆).wp
      (F₁ := Done M s₀) (F₂ := Done M s₀')
      fun a b h => ⟨final_xor_wp hp h.1 hu, final_xor_wp hp' h.2 hu'⟩
    exact (a₅.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((a₆.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₇.mono (fun _ _ h => h) fun _ _ h => h.2))
  have r₅ : RelCT isa (fun a b => (Whole M s₀ a ∧ a.zf = some (decide (fU s₀ = 0))) ∧
      (Whole M s₀' b ∧ b.zf = some (decide (fU s₀' = 0))))
      (.ite .e (.block []) (finalTail v.enc))
      (fun a b => Done M s₀ a ∧ Done M s₀' b) := by
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
  have r₆ := (RelCT.taint (A := taint)
    (P := fun a b => Done M s₀ a ∧ Done M s₀' b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, fSp, fSp, qSp]) t₁).wp
    (F₁ := fun (s : State) => s.gpr .rax = fV s₀) (F₂ := fun (s : State) => s.gpr .rax = fV s₀')
    fun a b h => ⟨WP.of_runBlock ⟨_, end_load_ok hp h.1, gpr_setReg_self _ _ _⟩,
      WP.of_runBlock ⟨_, end_load_ok hp' h.2, gpr_setReg_self _ _ _⟩⟩
  obtain ⟨_, t₇⟩ : ∃ h, (taint.check (Taint.ofRegs [.rax]) (.block finalRestore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have r₇ := RelCT.taint (A := taint) (P := fun a b => True ∧ a.gpr .rax = fV s₀ ∧ b.gpr .rax = fV s₀') _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1, h.2.2, fV, fV, qV]) t₇
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((r₃.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₄.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      (r₅.seq (r₆.seq r₇)))))

theorem final_ct {enc : Bool} {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86_64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86_64 M).post s s')
    (hct : ConstantTime isa (modeX86_64 M).pre (modeX86_64 M).pub whole)
    (hsp : NoSp whole) (hd : whole.depth = 1) (v : BlocksImpl) :
    ConstantTime isa (finalX86_64 enc).pre (finalX86_64 enc).pub (final name whole v.enc) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel hv hct hsp hd v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem encryptFinal_verified (v : BlocksImpl) :
    Verified X86_64.target (encryptFinal v.enc v.suffix) (finalScratchContract true) :=
  Verified.of_correct
    (final_correct (encrypt_correct v) (encrypt_noSp v) (encrypt_depth v) v (encryptFinal_mx v))
    (final_ct (encrypt_correct v) (AesCbc.X86_64.whole_ct (encBody_ok v) (encBody_ct v)) (encrypt_noSp v)
      (encrypt_depth v) v)
    (final_implies true)

theorem decryptFinal_verified (v : BlocksImpl) :
    Verified X86_64.target (decryptFinal v.enc v.suffix) (finalScratchContract false) :=
  Verified.of_correct
    (final_correct (decrypt_correct v) (decrypt_noSp v) (decrypt_depth v) v (decryptFinal_mx v))
    (final_ct (decrypt_correct v) (AesCbc.X86_64.batched_ct (decGroup_ok v) (decGroup_ct v) (decBody_ok v) (decBody_ct v)) (decrypt_noSp v)
      (decrypt_depth v) v)
    (final_implies false)

/-! ## With `save` on the stack

The final functions have six argument words, so `save` is their first stack
argument: they run their code in a frame of 64 bytes (`withStackArgScratchWiped`):
the quadword standing for the return address, `save`'s address, and `save`'s
48 bytes, which it zeroes before returning. The code's calls use 16 bytes
below it, so 80 in all. -/

/-- A state satisfying the precondition, without `save`. -/
def finalFrameSat : State :=
  { finalSatState with rd := [⟨0x1000, 240⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩] }

theorem encFrameSat_pre : ∃ s, (encryptFinalRoundsContract X86_64.abi 80).pre s := by
  implies_sat [encryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, encryptFinalPost, X86_64.abi,
    X86_64.argRegs] [finalFrameSat, finalSatState] using finalFrameSat

theorem decFrameSat_pre : ∃ s, (decryptFinalRoundsContract X86_64.abi 80).pre s := by
  implies_sat [decryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, decryptFinalPost, X86_64.abi,
    X86_64.argRegs] [finalFrameSat, finalSatState] using finalFrameSat

theorem encryptFinal_framed (v : BlocksImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 64 0 6 (encryptFinal v.enc v.suffix))
      (encryptFinalRoundsContract X86_64.abi 80) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 6)
    (pre := finalPre X86_64.abi.ptrBits) (post := encryptFinalPost X86_64.abi.ptrBits) (wa := false)
    (stack := 16) (bytes := 64) (words := 6) (encryptFinal_verified v) (by decide) (by decide) (by decide)
    (encryptFinal_spSafe v) (encryptFinal_xdepth v) (by decide) (finalPre_local _) (encryptFinalPost_local _)
    (encryptFinalPost_localOut _) encFrameSat_pre

theorem decryptFinal_framed (v : BlocksImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 64 0 6 (decryptFinal v.enc v.suffix))
      (decryptFinalRoundsContract X86_64.abi 80) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 6)
    (pre := finalPre X86_64.abi.ptrBits) (post := decryptFinalPost X86_64.abi.ptrBits) (wa := false)
    (stack := 16) (bytes := 64) (words := 6) (decryptFinal_verified v) (by decide) (by decide) (by decide)
    (decryptFinal_spSafe v) (decryptFinal_xdepth v) (by decide) (finalPre_local _) (decryptFinalPost_local _)
    (decryptFinalPost_localOut _) decFrameSat_pre

theorem encryptFinal_framed_spSafe (v : BlocksImpl) :
    (Impl.StackScratch.X86_64.withStackArgScratchWiped 64 0 6 (encryptFinal v.enc v.suffix)).all
      (fun i => !X86_64.isa.writesSp i) = true :=
  X86_64.withStackArgScratch_spSafe (by
    simp only [Code.all, encryptFinal_spSafe v, X86_64.wipeAt_spSafe, Bool.and_self])

theorem decryptFinal_framed_spSafe (v : BlocksImpl) :
    (Impl.StackScratch.X86_64.withStackArgScratchWiped 64 0 6 (decryptFinal v.enc v.suffix)).all
      (fun i => !X86_64.isa.writesSp i) = true :=
  X86_64.withStackArgScratch_spSafe (by
    simp only [Code.all, decryptFinal_spSafe v, X86_64.wipeAt_spSafe, Bool.and_self])

end VG.Proof.AesCfb.X86_64
