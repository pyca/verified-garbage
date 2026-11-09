module

public import VerifiedGarbage.Impl.AesCtr.X86.Final
public import VerifiedGarbage.Proof.AesCtr.Final
public import VerifiedGarbage.Proof.AesCtr.X86.Verified
public import VerifiedGarbage.Proof.AesCtr.Spec
public import VerifiedGarbage.Proof.AesCfb.X86.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.AesCbc.X86.Call
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Modes.X86.SeqFinal
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.X86.Body
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCbc.X86.CT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.AesCtr.X86.Final
meta import VerifiedGarbage.Proof.AesCtr.Final
meta import VerifiedGarbage.Proof.AesCtr.X86.Verified
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesCfb.X86.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.AesCbc.X86.Call
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.MdStream.X86.Common
meta import VerifiedGarbage.Proof.Modes.X86.SeqFinal
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.X86.Body
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.AesCbc.X86.CT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCbc.X86.Verified
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# AES-CTR of a message's last piece on x86 (32-bit)

`cryptFinal_framed`: `vg_aes_ctr_final` (`Impl/AesCtr/X86/Final.lean`), for any
implementation `v` of the block functions (`BlocksImpl`), meets
`Proof.AesCtr.finalRoundsContract`, from which the shared contract follows
(`Proof.AesCtr.final_keyed`).

The code is proven against `ctrFinalX86`, with a seventh stack argument
`save` of 32 bytes, for its caller's registers and a block of its own
(`final_implies`: the shared contract with it, `finalScratchContract`), as a
caller of the whole-block function, through its contract
(`modeX86 ctrMode`, `WP.callWith`). It shares AES-CFB's final functions'
setup and call of the whole-block function (`Proof/AesCfb/X86/Final.lean`:
`Setup`, `Whole`):

* `final_setup_wp`, `whole_wp`: the registers saved, and the whole-block
  function on the `n = len / 16` whole blocks (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, the block after the
  registers in `save` zeroed and the whole-block function on it
  (`tail_args_wp`, `tail_call_wp`), which leaves `CIPH_K(Tₙ₊₁)` there and
  `Tₙ₊₂` in `ctr`, and its first `u` bytes XORed into them
  (`Modes.X86.tailLoop_wp`, `final_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers restored from `save`;
* `final_post`: `Done` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`).

Every argument is reloaded from the stack, which nothing writes (`Pt`).
Constant time (`final_rel`): the blocks by the taint analysis from the
stack arguments (`argTaint`), the calls by the whole-block function's
constant time (`RelCT.callWith`), whose public arguments, the pointers,
`rounds` and the number of blocks, agree in both runs. `cryptFinal_framed`
runs the code with `save` in a frame of 64 bytes
(`Verified.stackScratchWiped`), zeroed on return, the block included; with
the 52 bytes its calls use below it, 116 in all.
-/

@[expose] public section

namespace VG.Proof.AesCtr.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)

/-- The code's contract, with the arguments on the stack `(schedule, rounds,
ctr, data, len, scratch, save)`, `save` of 32 bytes: the data and the
counter block as `Spec.Ctr.CryptFinal` says, by AES with the key schedule it
is given. -/
def ctrFinalX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let sv : Region := ⟨(arg s 6).setWidth 64, 32⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 52, 52⟩
    s.rd = [sched, args] ∧ s.wr = [iv, data, scr, sv] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint sv ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint sv ∧ iv.Disjoint args ∧
      data.Disjoint scr ∧ data.Disjoint sv ∧ data.Disjoint args ∧
      scr.Disjoint sv ∧ scr.Disjoint args ∧ sv.Disjoint args ∧
      ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ ret.Disjoint sv ∧
      stack.Disjoint sched ∧ stack.Disjoint iv ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      stack.Disjoint sv ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      (arg s 6).toNat + 32 ≤ 2 ^ 32 ∧
      52 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    Spec.Ctr.CryptFinal (ciphAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) s.mem s'.mem
      ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) (arg s 4).toNat
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-- The contract the frame needs: the shared one, with `save`, 32 bytes, as
a seventh argument, and 52 bytes of stack (the whole-block function's
arguments, its return address and its own 24 bytes). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract X86.abi Spec.Ctr.aesFinalSig "save" .u64 4 (finalPre X86.abi.ptrBits)
    (finalPost X86.abi.ptrBits) false 52 (some (finalLeak X86.abi.ptrBits))

/-- A state satisfying the precondition: AES-CFB's (`AesCfb.X86.finalSat`),
with `save` of 32 bytes. -/
def finalSat : State := { AesCfb.X86.finalSat with
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x5000, 32⟩] }

theorem final_implies : ctrFinalX86.Implies finalScratchContract := by
  have a0 : arg finalSat 0 = 0x1000 := by decide
  have a1 : arg finalSat 1 = 10 := by decide
  have a2 : arg finalSat 2 = 0x2000 := by decide
  have a3 : arg finalSat 3 = 0x3000 := by decide
  have a4 : arg finalSat 4 = 0 := by decide
  have a5 : arg finalSat 5 = 0x4000 := by decide
  have a6 : arg finalSat 6 = 0x5000 := by decide
  have e : argAddr finalSat 0 = 0x8004 := by decide
  have esp : finalSat.gpr .esp = 0x8000 := rfl
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ctrFinalX86] [a0, a1, a2, a3, a4, a5, a6, e, esp] using finalSat

/-! ## The arguments, by name -/

open VG.Impl.AesCtr.X86
open VG.Impl.AesCfb.X86 (finalSave wholeArgs wholeCall tailTest finalRestore finalSaved)
open VG.Impl.CmacAes.X86 (argOp)
open VG.Proof.CmacAes.X86 (wp_arg arg_ofNat ofNat_and_self_beq)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_andi wp_test wp_shr wp_sub wp_add wp_addi eval_e eval_ne)
open VG.Proof.AesCfb.X86 (fE fW fR fIv fD fL fS fV fN fU fT fSch fIvR fData fBlk fTail fScr fSv fArgs fRet
  fStk fWk fIv0 fBlks svMem Setup Whole Pt)

section
variable (s₀ : State)

/-- `save`: the registers, then the block. -/
abbrev cSv : Region := ⟨(fV s₀).setWidth 64, 32⟩
/-- The block after the registers in `save`, as the code computes it and as
a region. -/
abbrev cBk : BitVec 32 := fV s₀ + BitVec.ofNat 32 16
abbrev cBlk : Region := ⟨(fV s₀).setWidth 64 + BitVec.ofNat 64 16, 16⟩

/-- What the function writes. -/
abbrev cBig : List Region := [fIvR s₀, fData s₀, fScr s₀, cSv s₀, fStk s₀]
/-- What the function writes after saving the registers, with the whole
blocks rather than the data. -/
abbrev cW1 : List Region := [fIvR s₀, fBlk s₀, fScr s₀, cBlk s₀, fStk s₀]
/-- What the function writes after saving the registers. -/
abbrev cW : List Region := [fIvR s₀, fData s₀, fScr s₀, cBlk s₀, fStk s₀]

end

/-- The precondition, by name. -/
structure CPre (s₀ : State) : Prop where
  rd : s₀.rd = [fSch s₀, fArgs s₀]
  wr : s₀.wr = [fIvR s₀, fData s₀, fScr s₀, cSv s₀]
  sch_iv : (fSch s₀).Disjoint (fIvR s₀)
  sch_data : (fSch s₀).Disjoint (fData s₀)
  sch_scr : (fSch s₀).Disjoint (fScr s₀)
  sch_sv : (fSch s₀).Disjoint (cSv s₀)
  iv_data : (fIvR s₀).Disjoint (fData s₀)
  iv_scr : (fIvR s₀).Disjoint (fScr s₀)
  iv_sv : (fIvR s₀).Disjoint (cSv s₀)
  iv_args : (fIvR s₀).Disjoint (fArgs s₀)
  data_scr : (fData s₀).Disjoint (fScr s₀)
  data_sv : (fData s₀).Disjoint (cSv s₀)
  data_args : (fData s₀).Disjoint (fArgs s₀)
  scr_sv : (fScr s₀).Disjoint (cSv s₀)
  scr_args : (fScr s₀).Disjoint (fArgs s₀)
  sv_args : (cSv s₀).Disjoint (fArgs s₀)
  ret_iv : (fRet s₀).Disjoint (fIvR s₀)
  ret_data : (fRet s₀).Disjoint (fData s₀)
  ret_scr : (fRet s₀).Disjoint (fScr s₀)
  ret_sv : (fRet s₀).Disjoint (cSv s₀)
  stk_sch : (fStk s₀).Disjoint (fSch s₀)
  stk_iv : (fStk s₀).Disjoint (fIvR s₀)
  stk_data : (fStk s₀).Disjoint (fData s₀)
  stk_scr : (fStk s₀).Disjoint (fScr s₀)
  stk_sv : (fStk s₀).Disjoint (cSv s₀)
  sch_fit : (fW s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (fIv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (fD s₀).toNat + fL s₀ ≤ 2 ^ 32
  scr_fit : (fS s₀).toNat + 2176 ≤ 2 ^ 32
  sv_fit : (fV s₀).toNat + 32 ≤ 2 ^ 32
  esp52 : 52 ≤ (fE s₀).toNat
  esp_fit : (fE s₀).toNat + 32 ≤ 2 ^ 32
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem CPre.of {s₀ : State} (h : ctrFinalX86.pre s₀) : CPre s₀ := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33⟩ := h
  have e := AesCfb.X86.stk_eq a31
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    e ▸ a21, e ▸ a22, e ▸ a23, e ▸ a24, e ▸ a25, a26, a27, a28, a29, a30, a31, a32, a33⟩

/-! ## Addresses and regions -/

theorem sv16_sub (s₀ : State) : Region.Sub (fSv s₀) (cSv s₀) := Region.sub_prefix (by decide)
theorem blk_sv_sub (s₀ : State) : Region.Sub (cBlk s₀) (cSv s₀) := Offset.sub_base _ (by decide)
theorem sv_blk (s₀ : State) : (fSv s₀).Disjoint (cBlk s₀) := Offset.base_disjoint _ (Nat.le_refl _) (by decide)

section
variable {s₀ : State} (hp : CPre s₀)
include hp

theorem CPre.cBk_addr : (cBk s₀).setWidth 64 = (cBlk s₀).base := addr_eq (by have := hp.sv_fit; omega)

theorem CPre.cBk_toNat : (cBk s₀).toNat = (fV s₀).toNat + 16 := by
  have := hp.sv_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega)]

theorem CPre.argA {i : Nat} (hi : i < 7) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 32 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem CPre.arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (fArgs s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem CPre.arg_in {i : Nat} (hi : i < 7) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨fArgs s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem CPre.args_stk : (fArgs s₀).Disjoint (fStk s₀) := by
  have : (s₀.gpr .esp).toNat + 32 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (fE s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  rw [AesCfb.X86.stk_eq hp.esp52]
  show Region.Disjoint ⟨argAddr s₀ 0, 28⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

theorem CPre.ret_stk : (fRet s₀).Disjoint (fStk s₀) := by
  rw [AesCfb.X86.stk_eq hp.esp52]
  have := Offset.disjoint_below_above ((fE s₀).setWidth 64) (m := 52) (a := 0) (l := 4) (by decide)
  rw [BitVec.add_zero] at this
  exact this.symm

/-- The stack arguments are unchanged where only `cBig` changes. -/
theorem CPre.arg_keep {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.iv_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.data_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.scr_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.sv_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

/-- The return address is unchanged where only `cBig` changes. -/
theorem CPre.ret_keep {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) :
    m.readW ((fE s₀).setWidth 64) 32 = s₀.mem.readW ((fE s₀).setWidth 64) 32 :=
  hf.readW (r := fRet s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact hp.ret_sv
    · exact hp.ret_stk) (by decide)

theorem CPre.sched_sub : Region.Sub ⟨(fW s₀).setWidth 64, 16 * (fR s₀ + 1)⟩ (fSch s₀) :=
  Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)

theorem CPre.sched_len : 16 * (fR s₀ + 1) ≤ 2 ^ 64 := by rcases hp.rounds with h | h | h <;> omega

theorem CPre.sched_big : ∀ r ∈ cBig s₀, (⟨(fW s₀).setWidth 64, 16 * (fR s₀ + 1)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left hp.sched_sub
  · exact hp.sch_data.sub_left hp.sched_sub
  · exact hp.sch_scr.sub_left hp.sched_sub
  · exact hp.sch_sv.sub_left hp.sched_sub
  · exact hp.stk_sch.symm.sub_left hp.sched_sub

/-- The key schedule is unchanged where only `cBig` changes. -/
theorem CPre.sched_keep {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) :
    bytesAt m ((fW s₀).setWidth 64) (16 * (fR s₀ + 1)) = fWk s₀ :=
  Proof.Cmac.bytesAt_frame hf hp.sched_big hp.sched_len

theorem CPre.blk_fit : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 32 := by
  have := hp.data_fit; have := Nat.mul_div_le (fL s₀) 16; have : fN s₀ = fL s₀ / 16 := rfl; omega

theorem CPre.stk_sub {a k : Nat} (h : a + k ≤ 52) :
    Region.Sub (below (fE s₀ - BitVec.ofNat 32 k) a) (fStk s₀) := below_inner h hp.esp52

theorem CPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  have : fN s₀ = fL s₀ / 16 := rfl
  have : fU s₀ = fL s₀ % 16 := rfl
  exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)

end

/-! ## Frames -/

theorem cW1_cW {s₀ : State} {m : Mem} (hf : Frame (cW1 s₀) (svMem s₀) m) : Frame (cW s₀) (svMem s₀) m :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, AesCfb.X86.blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem whole_cW1 {M : AesCbc.Mode} {s₀ s : State} (h : Whole M s₀ s) : Frame (cW1 s₀) (svMem s₀) s.mem :=
  h.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-- Everything the function writes, from the save on. -/
theorem big_of {s₀ : State} {m : Mem} (hf : Frame (cW s₀) (svMem s₀) m) : Frame (cBig s₀) s₀.mem m :=
  ((AesCfb.X86.svMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨cSv s₀, by simp, sv16_sub s₀⟩).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨cSv s₀, by simp, blk_sv_sub s₀⟩
      · exact ⟨_, by simp, fun _ h => h⟩)

/-! ## Saving the registers, and the whole-block function's arguments -/

theorem final_setup_wp {s₀ : State} (hp : CPre s₀) :
    WP isa (.block (finalSave ++ wholeArgs)) s₀ (Setup s₀) := by
  rw [AesCfb.X86.setup_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = fV s₀ := u₁.gpr
  refine Spill.save_ofNat_ok finalSaved AesCfb.X86.finalSaved_fits
    (by rw [h₁]; have := hp.sv_fit; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb : p.2 + 4 ≤ 16 := AesCfb.X86.finalSaved_fits.1 p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = svMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, svMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' =>
      u₁.other _ (AesCfb.X86.finalSaved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  have big := big_of (s₀ := s₀) (Frame.refl _ (svMem s₀))
  have ak : ∀ i < 7, (svMem s₀).readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [AesCfb.X86.wholeArgs_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide))
    (by rw [hm₂]; exact ak 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact ak 1 (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, hm₂]; exact ak 2 (by decide)) fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem, u₃.mem, hm₂]; exact ak 3 (by decide)) fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]; exact ak 4 (by decide)) fun s₇ u₇ => ?_
  refine wp_shr (by decide) fun s₈ u₈ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), esp₂])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]
        exact hp.arg_in (by decide))
    (by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]; exact ak 5 (by decide)) fun s₉ u₉ => ?_
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, u₉.gpr, ?_, ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, AesCfb.X86.shr4]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## The calls of the whole-block function -/

open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.X86 (modeX86)
open VG.Proof.AesCfb.X86 (wholeRegs wholeRegs_esp wholeRd wholeWr toNat_n)
open VG.Proof.Aes.X86 (BlocksImpl)

/-- The regions the whole-block function is given on the partial block. -/
abbrev tailWr (s₀ : State) : List Region := [fIvR s₀, cBlk s₀, fScr s₀]

theorem one_toNat : (1 : BitVec 32).toNat = 1 := rfl

section
variable {s₀ : State} (hp : CPre s₀)
include hp

/-- The callee's return address and stack are in ours. -/
theorem CPre.retC_sub : Region.Sub ⟨(fE s₀ - BitVec.ofNat 32 28).setWidth 64, 4⟩ (fStk s₀) := by
  have : Region.Sub ⟨(fE s₀ - BitVec.ofNat 32 24 - BitVec.ofNat 32 4).setWidth 64, 4⟩ (fStk s₀) :=
    hp.stk_sub (by decide)
  rwa [show fE s₀ - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 = fE s₀ - BitVec.ofNat 32 28 by
    rw [BitVec.sub_sub]; rfl] at this

theorem CPre.stkC_sub :
    Region.Sub ⟨(fE s₀ - BitVec.ofNat 32 28).setWidth 64 - BitVec.ofNat 64 24, 24⟩ (fStk s₀) := by
  have := hp.esp52
  have : Region.Sub ⟨(fE s₀ - BitVec.ofNat 32 28 - BitVec.ofNat 32 24).setWidth 64, 24⟩ (fStk s₀) :=
    hp.stk_sub (by decide)
  rwa [Taint.sub_setWidth (by rw [sub_toNat (by omega)]; omega)] at this

theorem CPre.argsC_sub : Region.Sub (below (fE s₀) 24) (fStk s₀) := below_sub (by decide) hp.esp52

theorem CPre.callee_esp : 24 ≤ (fE s₀ - BitVec.ofNat 32 28).toNat ∧
    (fE s₀ - BitVec.ofNat 32 28).toNat + 28 ≤ 2 ^ 32 := by
  have := hp.esp52; have := hp.esp_fit
  rw [sub_toNat (by omega)]; omega

/-- The arguments the call pushes, from a state whose stack pointer is as
on entry. -/
theorem CPre.pushArgs {s : State} (hesp : s.gpr .esp = fE s₀) :
    arg (pushed wholeRegs s).callEntry 0 = s.gpr .eax ∧ arg (pushed wholeRegs s).callEntry 1 = s.gpr .ecx ∧
    arg (pushed wholeRegs s).callEntry 2 = s.gpr .edx ∧ arg (pushed wholeRegs s).callEntry 3 = s.gpr .ebx ∧
    arg (pushed wholeRegs s).callEntry 4 = s.gpr .esi ∧ arg (pushed wholeRegs s).callEntry 5 = s.gpr .edi := by
  have f : 4 * wholeRegs.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; have := hp.esp52; simp only [List.length_cons, List.length_nil]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [callEntry_arg f wholeRegs_esp (by decide)] <;> rfl

omit hp in
theorem calleeEsp_eq {s : State} (hesp : s.gpr .esp = fE s₀) :
    (pushed wholeRegs s).callEntry.gpr .esp = fE s₀ - BitVec.ofNat 32 28 := by
  rw [callEntry_esp', hesp]; rfl

omit hp in
theorem calleeArgs_eq {s : State} (hesp : s.gpr .esp = fE s₀) :
    argAddr (pushed wholeRegs s).callEntry 0 = (fE s₀ - BitVec.ofNat 32 24).setWidth 64 := by
  rw [callEntry_argAddr0, hesp]; rfl

theorem CPre.callPre {M : Mode} {s : State} (h : Setup s₀ s) :
    CallPre (modeX86 M) wholeRegs (wholeRd s₀) (wholeWr s₀) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hp.pushArgs h.esp
  have eA := calleeArgs_eq h.esp
  have eSp := calleeEsp_eq h.esp
  obtain ⟨c1, c2⟩ := hp.callee_esp
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, h.eax, h.ecx, h.edx, h.ebx, h.esi, h.edi,
      eA, eSp, toNat_n]
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_data.sub_right (AesCfb.X86.blk_sub s₀), hp.sch_scr,
      hp.iv_data.sub_right (AesCfb.X86.blk_sub s₀), hp.iv_scr, hp.data_scr.sub_left (AesCfb.X86.blk_sub s₀),
      hp.stk_iv.sub_left hp.argsC_sub, (hp.stk_data.sub_left hp.argsC_sub).sub_right (AesCfb.X86.blk_sub s₀),
      hp.stk_scr.sub_left hp.argsC_sub,
      hp.stk_iv.sub_left hp.retC_sub, (hp.stk_data.sub_left hp.retC_sub).sub_right (AesCfb.X86.blk_sub s₀),
      hp.stk_scr.sub_left hp.retC_sub,
      hp.stk_sch.sub_left hp.stkC_sub, hp.stk_iv.sub_left hp.stkC_sub,
      (hp.stk_data.sub_left hp.stkC_sub).sub_right (AesCfb.X86.blk_sub s₀), hp.stk_scr.sub_left hp.stkC_sub,
      hp.sch_fit, hp.iv_fit, hp.blk_fit, hp.scr_fit, c1, c2, hp.rounds⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr, h.esp]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨below (fE s₀) 24, by simp, 0, by simp, by simp⟩
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

end

theorem whole_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 M).post s s')
    (hsp : NoSp whole) (hst : stackUse whole = 24) {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    WP isa (wholeCall name whole) s (Whole M s₀) := by
  have f : 4 * wholeRegs.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [h.esp]; have := hp.esp52; simp only [List.length_cons, List.length_nil]; omega
  -- What the callee reads, on entry.
  have ef : Frame [fSv s₀, fStk s₀] s₀.mem (pushed wholeRegs s).callEntry.mem :=
    ((AesCfb.X86.svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
      (by
        rw [← h.mem]
        exact (callEntry_frame f wholeRegs_esp).sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨fStk s₀, by simp, by rw [h.esp]; exact below_sub (by decide) hp.esp52⟩)
  have eW : bytesAt (pushed wholeRegs s).callEntry.mem ((fW s₀).setWidth 64) (16 * (fR s₀ + 1)) = fWk s₀ :=
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.sch_sv.sub_left hp.sched_sub).sub_right (sv16_sub s₀)
      · exact hp.stk_sch.symm.sub_left hp.sched_sub) hp.sched_len
  have eIv : bytesAt (pushed wholeRegs s).callEntry.mem ((fIv s₀).setWidth 64) 16 = fIv0 s₀ :=
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.iv_sv.sub_right (sv16_sub s₀)
      · exact hp.stk_iv.symm) (by decide)
  have eB : Spec.Cbc.blocksAt (pushed wholeRegs s).callEntry.mem ((fD s₀).setWidth 64) (fN s₀) = fBlks s₀ :=
    AesCfb.X86.blocksAt_frame' ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.data_sv.sub_left (AesCfb.X86.blk_sub s₀)).sub_right (sv16_sub s₀)
      · exact hp.stk_data.symm.sub_left (AesCfb.X86.blk_sub s₀))
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hp.pushArgs h.esp
  refine WP.callWith (rs := wholeRegs) hv hsp (by decide) wholeRegs_esp
    (by rw [hst, h.esp]; have := hp.esp52; simp only [List.length_cons, List.length_nil]; omega)
    (hp.callPre h) fun s' rd' wr' cs' f' ⟨s₂, m₂, post₂⟩ => ?_
  rw [hst, h.esp, h.mem] at f'
  simp only [modeX86, State.withRegions_mem, arg_withRegions, a0, a1, a2, a3, a4, h.eax, h.ecx, h.edx, h.ebx,
    h.esi, toNat_n, m₂, eW, eIv, eB] at post₂
  exact ⟨by rw [cs' .esp (by simp [calleeSaved]), h.esp], by rw [rd', h.rd], by rw [wr', h.wr], f', post₂.1,
    post₂.2⟩

theorem whole_cW {M : Mode} {s₀ s : State} (h : Whole M s₀ s) : Frame (cW s₀) (svMem s₀) s.mem :=
  cW1_cW (whole_cW1 h)

/-- The test sets ZF if no bytes are left after the whole blocks. -/
theorem final_test_wp {M : Mode} {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.block tailTest) s fun s' => Whole M s₀ s' ∧ s'.zf = some (decide (fU s₀ = 0)) := by
  have big := big_of (whole_cW h)
  rw [AesCfb.X86.tailTest_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [h.rd, h.wr]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => wp_andi fun s₂ u₂ => wp_test fun s₃ f₃ z₃ => WP.block_nil
      ⟨h.of_eq (by rw [f₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd]) (by rw [f₃.wr, u₂.wr, u₁.wr]), ?_⟩
  have := AesCfb.X86.fU_lt s₀
  rw [z₃, u₂.gpr, u₁.gpr, AesCfb.X86.and15, ofNat_and_self_beq (by omega)]

/-! ## The partial last block: its arguments -/

theorem zeroSlots_fits : Spill.Fits 32 zeroSlots := by decide

/-- Four zeroed words make 16 zero bytes. -/
theorem zero_bytes (m : Mem) (A : Addr) {g : Reg → BitVec 32} (hg : g .ecx = 0) :
    bytesAt (Spill.saveMem m (A + BitVec.ofNat 64 ·) g zeroSlots) (A + BitVec.ofNat 64 16) 16 =
      List.replicate 16 0 := by
  have hs := Spill.saveMem_saved_ofNat m A g zeroSlots_fits (by decide)
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ _
  have hi : i < 16 := by simpa [bytesAt] using h₁
  simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  have e : A + BitVec.ofNat 64 16 + BitVec.ofNat 64 i =
      A + BitVec.ofNat 64 (16 + 4 * (i / 4)) + BitVec.ofNat 64 (i % 4) := by
    rw [Offset.add_add, Offset.add_add]; congr 2; omega
  have hmem : ((.ecx, 16 + 4 * (i / 4)) : Reg × Nat) ∈ zeroSlots := by
    rcases (by omega : i / 4 = 0 ∨ i / 4 = 1 ∨ i / 4 = 2 ∨ i / 4 = 3) with h | h | h | h <;> rw [h] <;> decide
  have hw := hs _ hmem
  rw [e, Mem.readW_byte (Spill.saveMem m (A + BitVec.ofNat 64 ·) g zeroSlots) _ (Nat.mod_lt _ (by decide))]
  simp only at hw
  rw [hw, hg]
  simp

theorem tailArgs_eq : tailArgs = .mov .eax (argOp 6) :: .mov .ecx (.imm 0) ::
    (Spill.saveCode .eax zeroSlots ++ ([.mov .ebx (.reg .eax), .alu .add .ebx (.imm 16), .mov .eax (argOp 0),
      .mov .ecx (argOp 1), .mov .edx (argOp 2), .mov .esi (.imm 1), .mov .edi (argOp 5)] : List Instr)) := rfl

/-- What zeroing the block and setting up the arguments leaves. -/
structure TArgs (s₀ s : State) : Prop where
  eax : s.gpr .eax = fW s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = fIv s₀
  ebx : s.gpr .ebx = cBk s₀
  esi : s.gpr .esi = 1
  edi : s.gpr .edi = fS s₀
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem ((fIv s₀).setWidth 64) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)
  zero : bytesAt s.mem (cBlk s₀).base 16 = List.replicate 16 0

theorem tail_args_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.block tailArgs) s (TArgs s₀) := by
  have f₁ := whole_cW1 h
  have big := big_of (cW1_cW f₁)
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have ak : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [tailArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (ak 6 (by decide)) fun s₁ u₁ => ?_
  refine wp_movi fun s₂ u₂ => ?_
  have eax₂ : s₂.gpr .eax = fV s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  refine Spill.save_ofNat_ok zeroSlots zeroSlots_fits (by rw [eax₂]; exact hp.sv_fit) (fun p hp' => ?_)
    fun s₃ u₃ => ?_
  · have hb : p.2 + 4 ≤ 32 := zeroSlots_fits.1 p hp'
    rw [eax₂, u₂.wr, u₁.wr, h.wr, hp.wr]
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₃ : s₃.mem = Spill.saveMem s.mem ((fV s₀).setWidth 64 + BitVec.ofNat 64 ·) s₂.gpr zeroSlots := by
    rw [u₃.mem, eax₂, u₂.mem, u₁.mem]
  have fz : Frame [cBlk s₀] s.mem s₃.mem := by
    rw [hm₃]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp' => by
      simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl
      · exact Offset.contains _ (by decide) (by decide) (by decide)
      · exact Offset.contains _ (by decide) (by decide) (by decide)
      · exact Offset.contains _ (by decide) (by decide) (by decide)
      · exact Offset.contains _ (by decide) (by decide) (by decide)
  have g₃ : s₃.gpr = s₂.gpr := u₃.gpr
  have esp₃ : s₃.gpr .esp = fE s₀ := by rw [g₃, u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have rw₃ : s₃.rd ++ s₃.wr = s₀.rd ++ s₀.wr := by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  have ak₃ : ∀ i < 7, s₃.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => by
    rw [fz.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.sv_args.symm.sub_left (hp.arg_sub hi)).sub_right (blk_sv_sub s₀)) (by decide)]
    exact ak i hi
  refine wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₅.mem, u₄.mem]; exact ak₃ 0 (by decide)) fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem]; exact ak₃ 1 (by decide)) fun s₇ u₇ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]; exact hp.arg_in (by decide))
    (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]; exact ak₃ 2 (by decide)) fun s₈ u₈ => wp_movi fun s₉ u₉ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), esp₃])
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]
        exact hp.arg_in (by decide))
    (by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]; exact ak₃ 5 (by decide)) fun s₁₀ u₁₀ => ?_
  have m₁₀ : s₁₀.mem = s₃.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have blkZ : ∀ r ∈ [cBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (AesCfb.X86.blk_sub s₀)).sub_right (blk_sv_sub s₀)
  have ivZ : ∀ r ∈ [cBlk s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, u₁₀.gpr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.gpr, u₄.gpr, g₃, eax₂]; rfl
  · rw [u₁₀.other _ (by decide), u₉.gpr]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), esp₃]
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [m₁₀]; exact f₁.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [m₁₀, AesCfb.X86.blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [m₁₀, Proof.Cmac.bytesAt_frame fz ivZ (by decide), h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]
  · rw [m₁₀, hm₃]
    exact zero_bytes _ _ (by rw [u₂.gpr])

/-! ## The partial last block: the call -/

theorem CPre.tailPre {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    CallPre (modeX86 AesCtr.ctrMode) wholeRegs (wholeRd s₀) (tailWr s₀) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hp.pushArgs h.esp
  have eA := calleeArgs_eq h.esp
  have eSp := calleeEsp_eq h.esp
  obtain ⟨c1, c2⟩ := hp.callee_esp
  have bs := blk_sv_sub s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, h.eax, h.ecx, h.edx, h.ebx, h.esi, h.edi,
      eA, eSp, hp.cBk_addr, one_toNat, Nat.mul_one]
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_sv.sub_right bs, hp.sch_scr,
      hp.iv_sv.sub_right bs, hp.iv_scr, (hp.scr_sv.sub_right bs).symm,
      hp.stk_iv.sub_left hp.argsC_sub, (hp.stk_sv.sub_left hp.argsC_sub).sub_right bs,
      hp.stk_scr.sub_left hp.argsC_sub,
      hp.stk_iv.sub_left hp.retC_sub, (hp.stk_sv.sub_left hp.retC_sub).sub_right bs,
      hp.stk_scr.sub_left hp.retC_sub,
      hp.stk_sch.sub_left hp.stkC_sub, hp.stk_iv.sub_left hp.stkC_sub,
      (hp.stk_sv.sub_left hp.stkC_sub).sub_right bs, hp.stk_scr.sub_left hp.stkC_sub,
      hp.sch_fit, hp.iv_fit, by rw [hp.cBk_toNat]; have := hp.sv_fit; omega, hp.scr_fit, c1, c2, hp.rounds⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr, h.esp]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨below (fE s₀) 24, by simp, 0, by simp, by simp⟩
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 16, by simp, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 16, by simp, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩

/-- What the call on the block leaves. -/
structure TCall (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem ((fIv s₀).setWidth 64) 16 = Spec.Ctr.next (Spec.Ctr.next (fIv0 s₀) (fN s₀)) 1
  out : bytesAt s.mem (cBlk s₀).base 16 = Spec.Cbc.aesWith (fR s₀) (fWk s₀) (Spec.Ctr.next (fIv0 s₀) (fN s₀))

theorem tail_call_wp {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 AesCtr.ctrMode).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 AesCtr.ctrMode).post s s')
    (hsp : NoSp whole) (hst : stackUse whole = 24) {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    WP isa (wholeCall name whole) s (TCall s₀) := by
  have f : 4 * wholeRegs.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [h.esp]; have := hp.esp52; simp only [List.length_cons, List.length_nil]; omega
  have ef : Frame [fStk s₀] s.mem (pushed wholeRegs s).callEntry.mem :=
    (callEntry_frame f wholeRegs_esp).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fStk s₀, by simp, by rw [h.esp]; exact below_sub (by decide) hp.esp52⟩
  have big := big_of (cW1_cW h.frame)
  have eW : bytesAt (pushed wholeRegs s).callEntry.mem ((fW s₀).setWidth 64) (16 * (fR s₀ + 1)) = fWk s₀ := by
    rw [Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.stk_sch.symm.sub_left hp.sched_sub) hp.sched_len]
    exact hp.sched_keep big
  have eT : bytesAt (pushed wholeRegs s).callEntry.mem ((fIv s₀).setWidth 64) 16 =
      Spec.Ctr.next (fIv0 s₀) (fN s₀) := by
    rw [Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.stk_iv.symm) (by decide)]
    exact h.ctr
  have eZ : bytesAt (pushed wholeRegs s).callEntry.mem (cBlk s₀).base 16 = List.replicate 16 0 := by
    rw [Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.stk_sv.symm.sub_left (blk_sv_sub s₀)) (by decide)]
    exact h.zero
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hp.pushArgs h.esp
  refine WP.callWith (rs := wholeRegs) hv hsp (by decide) wholeRegs_esp
    (by rw [hst, h.esp]; have := hp.esp52; simp only [List.length_cons, List.length_nil]; omega)
    (hp.tailPre h) fun s' rd' wr' cs' f' ⟨s₂, m₂, post₂⟩ => ?_
  rw [hst, h.esp] at f'
  simp only [modeX86, State.withRegions_mem, arg_withRegions, a0, a1, a2, a3, a4, h.eax, h.ecx, h.edx, h.ebx,
    h.esi, hp.cBk_addr, one_toNat, m₂, eW, eT, AesCtr.ctrMode_out, AesCtr.ctrMode_chain,
    AesCbc.length_blocksAt] at post₂
  have fc : Frame (cW1 s₀) s.mem s'.mem := f'.mono fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]
  refine ⟨by rw [cs' .esp (by simp [calleeSaved]), h.esp], by rw [rd', h.rd], by rw [wr', h.wr],
    h.frame.trans fc, ?_, post₂.2, ?_⟩
  · rw [AesCfb.X86.blocksAt_frame' f' fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (AesCfb.X86.blk_sub s₀)
      · exact (hp.data_sv.sub_left (AesCfb.X86.blk_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact hp.data_scr.sub_left (AesCfb.X86.blk_sub s₀)
      · exact hp.stk_data.symm.sub_left (AesCfb.X86.blk_sub s₀)]
    exact h.blocks
  · exact Modes.CtrFinal.bytesAt_of_blocksAt_one (aesWith_length _ _) eZ post₂.1

/-! ## The partial last block: the bytes XORed -/

theorem xorArgs_eq : xorArgs = [.mov .ebx (argOp 6), .alu .add .ebx (.imm 16), .mov .esi (argOp 3),
    .mov .ebp (argOp 4), .mov .eax (.reg .ebp), .alu .and .ebp (.imm 15), .alu .sub .eax (.reg .ebp),
    .alu .add .esi (.reg .eax)] := rfl

/-- The tail loop's operands. -/
structure XArgs (s₀ s : State) : Prop where
  call : TCall s₀ s
  ebx : s.gpr .ebx = cBk s₀
  esi : s.gpr .esi = fT s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (fU s₀)

theorem final_xorArgs_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TCall s₀ s) :
    WP isa (.block xorArgs) s (XArgs s₀) := by
  have big := big_of (cW1_cW h.frame)
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have ak : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [xorArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (ak 6 (by decide)) fun s₁ u₁ => ?_
  refine wp_addi fun s₁' u₁' => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁'.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₁'.rd, u₁'.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁'.mem, u₁.mem]; exact ak 3 (by decide)) fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁'.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁'.rd, u₁'.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁'.mem, u₁.mem]; exact ak 4 (by decide)) fun s₃ u₃ => ?_
  refine wp_mov fun s₄ u₄ => wp_andi fun s₅ u₅ => wp_sub fun s₆ u₆ _ => wp_add fun s₇ u₇ => WP.block_nil ?_
  have e₅ : s₅.gpr .ebp = BitVec.ofNat 32 (fU s₀) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, AesCfb.X86.and15]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁'.mem, u₁.mem]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁'.other _ (by decide), u₁.other _ (by decide), h.esp]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁'.rd, u₁.rd, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁'.wr, u₁.wr, h.wr]
  · rw [m₇]; exact h.frame
  · rw [m₇]; exact h.blocks
  · rw [m₇]; exact h.ctr
  · rw [m₇]; exact h.out
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁'.gpr, u₁.gpr]; rfl
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, e₅, AesCfb.X86.sub_mod16]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), e₅]

/-- What the function leaves before restoring the registers. -/
structure Done (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem ((fTail s₀).base + BitVec.ofNat 64 q) = s₀.mem ((fTail s₀).base + BitVec.ofNat 64 q) ^^^
    (Spec.Cbc.aesWith (fR s₀) (fWk s₀) (Spec.Ctr.next (fIv0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem ((fIv s₀).setWidth 64) 16 =
    Spec.Ctr.next (fIv0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : Whole AesCtr.ctrMode s₀ s) (hu : fU s₀ = 0) : Done s₀ s :=
  ⟨h.esp, h.rd, h.wr, whole_cW h, h.blocks, fun q hq => absurd hq (by omega), by
    rw [ite_eq_left hu, h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]⟩

theorem CPre.tail_addr {s₀ : State} (hp : CPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).setWidth 64 = (fTail s₀).base := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  have : fN s₀ = fL s₀ / 16 := rfl
  have : fU s₀ = fL s₀ % 16 := rfl
  exact addr_eq (by omega)

theorem CPre.toNat_tail {s₀ : State} (hp : CPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  have : fN s₀ = fL s₀ / 16 := rfl
  have : fU s₀ = fL s₀ % 16 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem final_xor_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : XArgs s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.loop (.block Impl.Modes.X86.tailByte) .ne) s (Done s₀) := by
  have hU := AesCfb.X86.fU_lt s₀
  have hT := hp.toNat_tail hu
  have eT := hp.tail_addr hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_fit
  have hVw := hp.sv_fit
  have hB := hp.cBk_toNat
  have eB := hp.cBk_addr
  have eN : fN s₀ = fL s₀ / 16 := rfl
  have eU : fU s₀ = fL s₀ % 16 := rfl
  have hc := h.call
  have xp : Modes.X86.XPre s (cBk s₀) (fT s₀) (fU s₀) := {
    fitK := by omega
    fitR := by rw [hT]; omega
    disj := by
      rw [eT, eB]
      exact ((((hp.data_sv.sub_left (AesCfb.X86.tail_sub s₀)).sub_right (blk_sv_sub s₀)).sub_right
        (Region.sub_prefix (by omega)))).symm
    rdK := fun q hq => by
      rw [hc.rd, hc.wr, hp.rd, hp.wr, eB]
      refine ⟨cSv s₀, by simp, ?_⟩
      rw [Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)
    wrR := fun q hq => by
      rw [hc.wr, hp.wr, eT]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show (fTail s₀).base + BitVec.ofNat 64 q = (fD s₀).setWidth 64 + BitVec.ofNat 64 (16 * fN s₀ + q) from
        Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega) }
  have x0 : Modes.X86.XInv s (cBk s₀) (fT s₀) (fU s₀) 0 s := {
    ebx := by rw [h.ebx]; exact (BitVec.add_zero _).symm
    esi := by rw [h.esi]; exact (BitVec.add_zero _).symm
    ebp := by rw [h.ebp, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    syms := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Modes.X86.tailLoop_wp xp x0) fun s' d => ?_
  have fT' : Frame [fTail s₀] s.mem s'.mem := by have := d.frame; rw [eT] at this; exact this
  have tailD : ∀ r ∈ cW1 s₀, (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (hp.iv_data.sub_right (AesCfb.X86.tail_sub s₀)).symm
    · exact hp.blk_tail.symm
    · exact hp.data_scr.sub_left (AesCfb.X86.tail_sub s₀)
    · exact (hp.data_sv.sub_left (AesCfb.X86.tail_sub s₀)).sub_right (blk_sv_sub s₀)
    · exact (hp.stk_data.sub_right (AesCfb.X86.tail_sub s₀)).symm
  have tailS : ∀ r ∈ [fSv s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (AesCfb.X86.tail_sub s₀)).sub_right (sv16_sub s₀)
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; omega
  refine ⟨by rw [d.gpr .esp (by decide) (by decide) (by decide) (by decide) (by decide), hc.esp],
    by rw [d.rd, hc.rd], by rw [d.wr, hc.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact (cW1_cW hc.frame).trans (fT'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, AesCfb.X86.tail_sub s₀⟩)
  · rw [AesCfb.X86.blocksAt_frame' fT' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact hc.blocks
  · have := d.data q hq
    rw [eT, eB] at this
    rw [this, hc.frame.bytes tailD hlen hq, (AesCfb.X86.svMem_frame s₀).bytes tailS hlen hq,
      MdStream.X86.bytesAt_getD hc.out (show q < 16 by omega)]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame fT' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.sub_right (AesCfb.X86.tail_sub s₀))
      (by decide), hc.ctr, ← AesCtr.next_add]

theorem final_mid_wp {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 AesCtr.ctrMode).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 AesCtr.ctrMode).post s s')
    (hsp : NoSp whole) (hst : stackUse whole = 24) {s₀ : State} (hp : CPre s₀) {s : State}
    (h : Whole AesCtr.ctrMode s₀ s) (hz : s.zf = some (decide (fU s₀ = 0))) :
    WP isa (.ite .e (.block []) (finalTail name whole)) s (Done s₀) := by
  have ev : isa.eval .e s = some (decide (fU s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, hz]
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [ev, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [ev, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (tail_args_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp hv hsp hst hp h₁) fun _ h₂ =>
        WP.seq (WP.mono (final_xorArgs_wp hp h₂) fun _ h₃ => final_xor_wp hp h₃ hu)))

/-! ## Restoring the registers -/

theorem final_end_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Done s₀ s) :
    WP isa (.block finalRestore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  have big := big_of h.frame
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hs : Spill.Saved s.mem ((fV s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr finalSaved :=
    (Spill.saveMem_saved_ofNat s₀.mem _ s₀.gpr AesCfb.X86.finalSaved_fits (by decide)).of_frame h.frame
      (fun p hp' => Offset.contains_base _ (AesCfb.X86.finalSaved_fits.1 p hp')
        (by have := AesCfb.X86.finalSaved_fits.1 p hp'; omega))
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact (hp.iv_sv.sub_right (sv16_sub s₀)).symm
        · exact (hp.data_sv.sub_right (sv16_sub s₀)).symm
        · exact (hp.scr_sv.sub_right (sv16_sub s₀)).symm
        · exact sv_blk s₀
        · exact (hp.stk_sv.sub_right (sv16_sub s₀)).symm
  rw [AesCfb.X86.restore_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok finalSaved AesCfb.X86.finalSaved_fits
    (by rw [u₁.gpr]; have h32 : (arg s₀ 6).toNat + 32 ≤ 2 ^ 32 := hp.sv_fit; omega) AesCfb.X86.finalSaved_ne_eax
    (fun p hp' => ?_) (by rw [u₁.gpr, u₁.mem]; exact hs) fun s₂ r₂ => WP.block_nil ?_
  · have := AesCfb.X86.finalSaved_fits.1 p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, hrw, hp.rd, hp.wr]
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, by rw [r₂.mem, u₁.mem]⟩
  rw [r₂.mem, u₁.mem]; exact hp.ret_keep big

/-! ## The whole function -/

theorem final_wp {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 AesCtr.ctrMode).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 AesCtr.ctrMode).post s s')
    (hsp : NoSp whole) (hst : stackUse whole = 24) {s₀ : State} (hp : CPre s₀) :
    WP isa (final name whole) s₀ fun s' => abiPreserved s₀ s' ∧ ∃ s₁, Done s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hv hsp hst hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_test_wp hp h₂) fun s₃ ⟨h₃, z₃⟩ => ?_)
  refine WP.seq (WP.mono (final_mid_wp hv hsp hst hp h₃ z₃) fun s₄ h₄ => ?_)
  exact WP.mono (final_end_wp hp h₄) fun _ ⟨g, m⟩ => ⟨g, s₄, h₄, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalX86.post s₀ s' := by
  show Spec.Ctr.CryptFinal (ciphAt s₀.mem ((fW s₀).setWidth 64) (fR s₀)) s₀.mem s'.mem
    ((fIv s₀).setWidth 64) ((fD s₀).setWidth 64) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem final_correct {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 AesCtr.ctrMode).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 AesCtr.ctrMode).post s s')
    (hsp : NoSp whole) (hst : stackUse whole = 24) (s : State) (hs : ctrFinalX86.pre s) :
    ∃ t s', Exec isa (final name whole) s t s' ∧ abiPreserved s s' ∧ ctrFinalX86.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp hv hsp hst (CPre.of hs)
  exact ⟨t, s', he, hg, final_post h₁ hm⟩

/-! ## Constant time -/

theorem CPre.argsOut {s₀ : State} (hp : CPre s₀) {s : State} (h : Pt s₀ s) : ArgsOut 7 s := by
  have hs := hp.esp_fit
  refine ⟨by rw [h.esp]; omega, ?_⟩
  rw [h.wr, hp.wr, h.esp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact Taint.frame_disjoint (n := 28) (by omega) hp.ret_iv hp.iv_args.symm
  · exact Taint.frame_disjoint (n := 28) (by omega) hp.ret_data hp.data_args.symm
  · exact Taint.frame_disjoint (n := 28) (by omega) hp.ret_scr hp.scr_args.symm
  · exact Taint.frame_disjoint (n := 28) (by omega) hp.ret_sv hp.sv_args.symm

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem Pt.agree {s₀ s₀' : State} (hq : ctrFinalX86.pub s₀ s₀') (hp : CPre s₀) (hp' : CPre s₀')
    {rs : List Reg} {s₁ s₂ : State} (h₁ : Pt s₀ s₁) (h₂ : Pt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 7)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp, fE, fE, hq.1]) (hp.argsOut h₁) (hp'.argsOut h₂)
    fun i hi => by
      rw [AesCfb.X86.arg_cur h₁.esp (h₁.args i hi), AesCfb.X86.arg_cur h₂.esp (h₂.args i hi), hq.2 i hi]

theorem whole_pt {M : Mode} {s₀ s : State} (hp : CPre s₀) (h : Whole M s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of (whole_cW h)) hi⟩

theorem TCall.pt {s₀ s : State} (hp : CPre s₀) (h : TCall s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of (cW1_cW h.frame)) hi⟩

theorem Done.pt {s₀ s : State} (hp : CPre s₀) (h : Done s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of h.frame) hi⟩

theorem setup_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block (finalSave ++ wholeArgs)) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem test_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block tailTest) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block tailArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7))
    (.seq (.block xorArgs) (.loop (.block Impl.Modes.X86.tailByte) .ne)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block finalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 AesCtr.ctrMode).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 AesCtr.ctrMode).post s s')
    (hct : ConstantTime isa (modeX86 AesCtr.ctrMode).pre (modeX86 AesCtr.ctrMode).pub whole)
    (hsp : NoSp whole) (hst : stackUse whole = 24) {s₀ s₀' : State}
    (h0 : ctrFinalX86.pre s₀) (h0' : ctrFinalX86.pre s₀') (hq : ctrFinalX86.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (final name whole) fun _ _ => True := by
  have hp := CPre.of h0
  have hp' := CPre.of h0'
  have qE : fE s₀ = fE s₀' := hq.1
  have qA : ∀ i < 7, arg s₀ i = arg s₀' i := hq.2
  have qW : fW s₀ = fW s₀' := qA 0 (by decide)
  have qIv : fIv s₀ = fIv s₀' := qA 2 (by decide)
  have qD : fD s₀ = fD s₀' := qA 3 (by decide)
  have qL : fL s₀ = fL s₀' := by simp only [fL, qA 4 (by decide)]
  have qS : fS s₀ = fS s₀' := qA 5 (by decide)
  have qV : fV s₀ = fV s₀' := qA 6 (by decide)
  have qU : fU s₀ = fU s₀' := by simp only [fU, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, qL]
  have pt₀ : ∀ {t : State}, Pt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  -- The registers saved and the whole-block function's arguments.
  obtain ⟨_, t₁⟩ := setup_taint
  have r₁ := ((RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact Pt.agree (rs := []) hq hp hp' pt₀ pt₀ fun r hr => by simp at hr) t₁).wp
    (F₁ := Setup s₀) (F₂ := Setup s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨final_setup_wp hp, final_setup_wp hp'⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  -- The whole blocks.
  have eRd : wholeRd s₀' = wholeRd s₀ := by simp only [wholeRd, fSch, fW, fE, qW, qE]
  have eWr : wholeWr s₀' = wholeWr s₀ := by simp only [wholeWr, fIvR, fBlk, fScr, fIv, fD, fS, qIv, qD, qS, qN]
  have c₂ := RelCT.callWith (k := modeX86 AesCtr.ctrMode) (n := name) (rs := wholeRegs) hv hct
    (P := fun a b => Setup s₀ a ∧ Setup s₀' b) (wholeRd s₀) (wholeWr s₀) fun a b ⟨ha, hb⟩ => by
      have pb := hp'.callPre (M := AesCtr.ctrMode) hb
      rw [eRd, eWr] at pb
      obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hp.pushArgs ha.esp
      obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hp'.pushArgs hb.esp
      refine ⟨hp.callPre ha, pb, by rw [ha.esp, hb.esp, qE], ?_, fun i hi => ?_⟩
      · simp only [State.withRegions_gpr, calleeEsp_eq ha.esp, calleeEsp_eq hb.esp, qE]
      · simp only [arg_withRegions]
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [a0, b0, ha.eax, hb.eax, qW]
        · rw [a1, b1, ha.ecx, hb.ecx, qA 1 (by decide)]
        · rw [a2, b2, ha.edx, hb.edx, qIv]
        · rw [a3, b3, ha.ebx, hb.ebx, qD]
        · rw [a4, b4, ha.esi, hb.esi, qN]
        · rw [a5, b5, ha.edi, hb.edi, qS]
  have r₂ : RelCT isa (fun a b => Setup s₀ a ∧ Setup s₀' b) (wholeCall name whole)
      (fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b) :=
    (RelCT.wp (c := wholeCall name whole) (F₁ := Whole AesCtr.ctrMode s₀) (F₂ := Whole AesCtr.ctrMode s₀') c₂
      fun a b h => ⟨whole_wp hv hsp hst hp h.1, whole_wp hv hsp hst hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  -- The test.
  obtain ⟨_, t₃⟩ := test_taint
  have r₃ := ((RelCT.taint (A := taint)
    (P := fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b) _
    (fun a b h => Pt.agree (rs := []) hq hp hp' (whole_pt hp h.1) (whole_pt hp' h.2) fun r hr => by simp at hr) t₃).wp
    (F₁ := fun (s : State) => Whole AesCtr.ctrMode s₀ s ∧ s.zf = some (decide (fU s₀ = 0)))
    (F₂ := fun (s : State) => Whole AesCtr.ctrMode s₀' s ∧ s.zf = some (decide (fU s₀' = 0)))
    fun a b h => ⟨final_test_wp hp h.1, final_test_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  -- The partial last block.
  obtain ⟨_, t₄⟩ := tailArgs_taint
  obtain ⟨_, t₅⟩ := xor_taint
  have tail (hu : fU s₀ ≠ 0) :
      RelCT isa (fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b)
        (finalTail name whole) fun a b => Done s₀ a ∧ Done s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₄ := ((RelCT.taint (A := taint)
      (P := fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b) _
      (fun a b h => Pt.agree (rs := []) hq hp hp' (whole_pt hp h.1) (whole_pt hp' h.2) fun r hr => by simp at hr) t₄).wp
      (F₁ := TArgs s₀) (F₂ := TArgs s₀')
      fun a b h => ⟨tail_args_wp hp h.1, tail_args_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    have eWr' : tailWr s₀' = tailWr s₀ := by simp only [tailWr, fIvR, cBlk, fScr, fIv, fV, fS, qIv, qV, qS]
    have c₅ := RelCT.callWith (k := modeX86 AesCtr.ctrMode) (n := name) (rs := wholeRegs) hv hct
      (P := fun a b => TArgs s₀ a ∧ TArgs s₀' b) (wholeRd s₀) (tailWr s₀) fun a b ⟨ha, hb⟩ => by
        have pb := hp'.tailPre hb
        rw [eRd, eWr'] at pb
        obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hp.pushArgs ha.esp
        obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hp'.pushArgs hb.esp
        refine ⟨hp.tailPre ha, pb, by rw [ha.esp, hb.esp, qE], ?_, fun i hi => ?_⟩
        · simp only [State.withRegions_gpr, calleeEsp_eq ha.esp, calleeEsp_eq hb.esp, qE]
        · simp only [arg_withRegions]
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
            rfl | rfl | rfl | rfl | rfl | rfl
          · rw [a0, b0, ha.eax, hb.eax, qW]
          · rw [a1, b1, ha.ecx, hb.ecx, qA 1 (by decide)]
          · rw [a2, b2, ha.edx, hb.edx, qIv]
          · rw [a3, b3, ha.ebx, hb.ebx, cBk, cBk, qV]
          · rw [a4, b4, ha.esi, hb.esi]
          · rw [a5, b5, ha.edi, hb.edi, qS]
    have a₅ : RelCT isa (fun a b => TArgs s₀ a ∧ TArgs s₀' b) (wholeCall name whole)
        (fun a b => TCall s₀ a ∧ TCall s₀' b) :=
      (RelCT.wp (c := wholeCall name whole) (F₁ := TCall s₀) (F₂ := TCall s₀') c₅
        fun a b h => ⟨tail_call_wp hv hsp hst hp h.1, tail_call_wp hv hsp hst hp' h.2⟩).mono
        (fun _ _ h => h) fun _ _ h => h.2
    have a₆ := ((RelCT.taint (A := taint)
      (P := fun a b => TCall s₀ a ∧ TCall s₀' b) _
      (fun a b h => Pt.agree (rs := []) hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr) t₅).wp
      (F₁ := Done s₀) (F₂ := Done s₀')
      fun a b h => ⟨WP.seq (WP.mono (final_xorArgs_wp hp h.1) fun _ h₃ => final_xor_wp hp h₃ hu),
        WP.seq (WP.mono (final_xorArgs_wp hp' h.2) fun _ h₃ => final_xor_wp hp' h₃ hu')⟩).mono
          (fun _ _ h => h) fun _ _ h => h.2
    exact a₄.seq (a₅.seq a₆)
  have r₄ : RelCT isa (fun a b => (Whole AesCtr.ctrMode s₀ a ∧ a.zf = some (decide (fU s₀ = 0))) ∧
      (Whole AesCtr.ctrMode s₀' b ∧ b.zf = some (decide (fU s₀' = 0))))
      (.ite .e (.block []) (finalTail name whole))
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
  -- The registers restored.
  obtain ⟨_, t₆⟩ := restore_taint
  have r₅ := RelCT.taint (A := taint) (P := fun a b => Done s₀ a ∧ Done s₀' b) _
    (fun a b h => Pt.agree (rs := []) hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr) t₆
  exact r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))

theorem final_ct {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 AesCtr.ctrMode).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 AesCtr.ctrMode).post s s')
    (hct : ConstantTime isa (modeX86 AesCtr.ctrMode).pre (modeX86 AesCtr.ctrMode).pub whole)
    (hsp : NoSp whole) (hst : stackUse whole = 24) :
    ConstantTime isa ctrFinalX86.pre ctrFinalX86.pub (final name whole) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel hv hct hsp hst h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The code's properties -/

theorem crypt_noSp (v : BlocksImpl) : NoSp (crypt v.enc) :=
  NoSp.of_all (by
    simp only [crypt, Impl.AesCbc.X86.whole, body, Impl.AesCbc.X86.blkCall, Code.allInstrs,
      AesCfb.X86.all_of_noSp v.encNosp]
    decide +kernel)

theorem crypt_stack (v : BlocksImpl) : stackUse (crypt v.enc) = 24 := by
  simp only [crypt, Impl.AesCbc.X86.whole, body, Impl.AesCbc.X86.blkCall, stackUse, v.encStack]
  decide

theorem cryptFinal_noSp (v : BlocksImpl) :
    (cryptFinal v.enc v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [cryptFinal, final, wholeCall, finalTail, Code.allInstrs, AesCfb.X86.all_of_noSp (crypt_noSp v)]
  decide +kernel

theorem cryptFinal_stack (v : BlocksImpl) : stackUse (cryptFinal v.enc v.suffix) ≤ 52 := by
  simp only [cryptFinal, final, wholeCall, finalTail, stackUse, crypt_stack v]
  decide

theorem cryptFinal_spSafe (v : BlocksImpl) :
    (cryptFinal v.enc v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [cryptFinal, final, wholeCall, finalTail, Code.all, crypt_spSafe v]
  decide +kernel

/-! ## Verified -/

theorem whole_ok (v : BlocksImpl) : ∀ s, (modeX86 AesCtr.ctrMode).pre s →
    ∃ t s', Exec isa (crypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeX86 AesCtr.ctrMode).post s s' :=
  fun _ hs => AesCbc.X86.whole_wp (body_ok v) hs

theorem cryptFinal_verified (v : BlocksImpl) :
    Verified X86.target (cryptFinal v.enc v.suffix) finalScratchContract :=
  Verified.of_correct (final_correct (whole_ok v) (crypt_noSp v) (crypt_stack v))
    (final_ct (whole_ok v) (AesCbc.X86.whole_ct (body_ok v) (body_ct v)) (crypt_noSp v) (crypt_stack v))
    final_implies

/-! ## With `save` on the stack

The final function has six argument slots, so `save` is its seventh
argument: it runs its code in a frame of 64 bytes
(`withStackScratchWiped 64 6 8`): the word standing for the return address,
a copy of the six arguments, `save`'s address, and `save`'s 32 bytes (the
registers, then the block that held the last output block), which it zeroes
before returning. The code's calls use 52 bytes below it, so 116 in all. -/

theorem frameSat_pre : ∃ s, (Spec.Ctr.aesFinalSig.contract X86.abi (pre := finalPre X86.abi.ptrBits)
    (post := finalPost X86.abi.ptrBits) (stack := 116)).pre s := by
  have a0 : arg AesCbc.X86.sat 0 = 0x1000 := by decide
  have a1 : arg AesCbc.X86.sat 1 = 10 := by decide
  have a2 : arg AesCbc.X86.sat 2 = 0x2000 := by decide
  have a3 : arg AesCbc.X86.sat 3 = 0x3000 := by decide
  have a4 : arg AesCbc.X86.sat 4 = 0 := by decide
  have a5 : arg AesCbc.X86.sat 5 = 0x4000 := by decide
  have e : argAddr AesCbc.X86.sat 0 = 0x8004 := by decide
  have esp : AesCbc.X86.sat.gpr .esp = 0x8000 := rfl
  sig_implies_sat [Spec.Ctr.aesFinalSig, finalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp] using AesCbc.X86.sat

theorem cryptFinal_framed (v : BlocksImpl) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 64 6 8 (cryptFinal v.enc v.suffix))
      (finalRoundsContract X86.abi 116) :=
  X86.Verified.stackScratchWiped (sig := Spec.Ctr.aesFinalSig) (nm := "save") (e := .u64) (n := 4)
    (pre := finalPre X86.abi.ptrBits) (post := finalPost X86.abi.ptrBits) (wa := false) (stack := 52)
    (leak := some (finalLeak X86.abi.ptrBits))
    (bytes := 64) (words := 8) (cryptFinal_verified v) (by decide) (cryptFinal_noSp v) (cryptFinal_stack v)
    (by decide) (finalPre_local _) (finalPost_local _) (finalPost_localOut _) frameSat_pre
    (hleak := finalLeak_local _)

theorem framed_spSafe {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.StackScratch.X86.withStackScratchWiped 64 6 8 c).all (fun i => !isa.writesSp i) = true := by
  have hf : (Impl.StackScratch.X86.withStackScratchWiped 64 6 8 (.block [])).all
      (fun i => !isa.writesSp i) = true := by decide +kernel
  simp only [Impl.StackScratch.X86.withStackScratchWiped, Impl.StackScratch.X86.withStackScratch, Code.all,
    List.all_nil, Bool.and_eq_true] at hf ⊢
  simp_all

theorem cryptFinal_framed_spSafe (v : BlocksImpl) :
    (Impl.StackScratch.X86.withStackScratchWiped 64 6 8 (cryptFinal v.enc v.suffix)).all
      (fun i => !isa.writesSp i) = true :=
  framed_spSafe (cryptFinal_spSafe v)

end VG.Proof.AesCtr.X86
