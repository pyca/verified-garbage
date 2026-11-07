module

public import VerifiedGarbage.Impl.AesCfb.X86.Final
public import VerifiedGarbage.Proof.AesCfb.Final
public import VerifiedGarbage.Proof.AesCfb.X86.Verified
public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.AesCbc.X86.Call
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Modes.X86.SeqFinal
import VerifiedGarbage.Proof.AesCbc.X86.CT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesCfb.X86.Body
import VerifiedGarbage.Proof.AesCbc.X86.Verified
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.ArgTaint
meta import VerifiedGarbage.Impl.AesCfb.X86.Final
meta import VerifiedGarbage.Proof.AesCfb.Final
meta import VerifiedGarbage.Proof.AesCfb.X86.Verified
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.AesCbc.X86.Call
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.CmacAes.X86.UpdateLoop
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.MdStream.X86.Common
meta import VerifiedGarbage.Proof.Modes.X86.SeqFinal
meta import VerifiedGarbage.Proof.AesCbc.X86.CT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesCfb.X86.Body
meta import VerifiedGarbage.Proof.AesCbc.X86.Verified
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Framework.X86.ArgTaint

/-!
# AES-CFB128 of a message's last piece on x86 (32-bit)

`encryptFinal_framed` and `decryptFinal_framed`: `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final` (`Impl/AesCfb/X86/Final.lean`), for any
implementation `v` of the block functions (`BlocksImpl`), meet
`Proof.AesCfb.encryptFinalRoundsContract` (and `decrypt…`), from which the
shared contracts follow (`Proof.AesCfb.encryptFinal_keyed`).

The code is proven against `finalX86`, with a seventh stack argument `save`
for its caller's registers (`final_implies`: the shared contract with it,
`finalScratchContract`), as a caller of two verified functions, through
their contracts (`WP.callWith`, `blk_call`):

* `final_setup_wp`: the registers saved in `save`, and the whole-block
  function's arguments loaded from ours (`Setup`);
* `whole_wp`: the whole-block function of the same direction and variant on
  the `n = len / 16` whole blocks, its six arguments pushed, from its
  contract (`modeX86 (cfbMode enc)`), with the regions it is given
  (`Setup.callPre`): the blocks and the chaining value the mode's (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left (`final_test_wp`), the
  block function on the chaining value in place (`final_ivArgs_wp`,
  `final_ciph_wp`), and its first `u` bytes XORed into them by the modes'
  loop (`Modes.X86.tailLoop_wp`, `final_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers restored from `save`, which nothing else
  wrote, and the return address intact;
* `final_post`: `Done` gives `Spec.Cfb.EncryptFinal` (or `DecryptFinal`), by
  `Proof.AesCfb.encryptFinal_of`.

Every argument is reloaded from the stack, which nothing writes (`Pt`).
Constant time (`final_rel`): the blocks by the taint analysis from the
stack arguments (`argTaint`), the calls by their contracts' constant time
(`RelCT.callWith`, `blk_rel`), every address and branch from the pointers
and `len`, which agree in both runs. `encryptFinal_framed` runs the code
with `save` in a frame of 48 bytes on the stack
(`Verified.stackScratchWiped`), zeroed on return; with the 52 bytes its
calls use below it, 100 in all.
-/

@[expose] public section

namespace VG.Proof.AesCfb.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)

/-- The code's contract, with the arguments on the stack `(schedule, rounds,
iv, data, len, scratch, save)`: in direction `enc`, the data and the block
at `iv` as `Spec.Cfb.EncryptFinal` (or `DecryptFinal`) says, by AES with the
key schedule it is given. -/
def finalX86 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let sv : Region := ⟨(arg s 6).setWidth 64, 16⟩
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
      (arg s 6).toNat + 16 ≤ 2 ^ 32 ∧
      52 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let ciph := ciphAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    if enc then Spec.Cfb.EncryptFinal ciph 16 s.mem s'.mem ((arg s 2).setWidth 64) ((arg s 3).setWidth 64)
      (arg s 4).toNat
    else Spec.Cfb.DecryptFinal ciph 16 s.mem s'.mem ((arg s 2).setWidth 64) ((arg s 3).setWidth 64)
      (arg s 4).toNat
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-- The postcondition in direction `enc`. -/
abbrev finalPost (enc : Bool) : Spec.Cfb.aesFinalSig.Post X86.abi.ptrBits :=
  if enc then encryptFinalPost X86.abi.ptrBits else decryptFinalPost X86.abi.ptrBits

/-- The contract the frame needs: the shared one, with `save`, 16 bytes, as
a seventh argument, and 52 bytes of stack (the whole-block function's
arguments, its return address and its own 24 bytes). -/
abbrev finalScratchContract (enc : Bool) : Contract isa :=
  Sig.scratchContract X86.abi Spec.Cfb.aesFinalSig "save" .u64 2 (finalPre X86.abi.ptrBits)
    (finalPost enc) false 52

/-- A state satisfying the precondition: the schedule at `0x1000`, 10
rounds, the block at `0x2000`, no data at `0x3000`, the scratch buffer at
`0x4000` and `save` at `0x5000`, as stack arguments at `0x8004`. -/
def finalSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10
    else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40
    else if a = 0x801d then 0x50 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x8004, 28⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x5000, 16⟩]

theorem final_implies (enc : Bool) : (finalX86 enc).Implies (finalScratchContract enc) := by
  have a0 : arg finalSat 0 = 0x1000 := by decide
  have a1 : arg finalSat 1 = 10 := by decide
  have a2 : arg finalSat 2 = 0x2000 := by decide
  have a3 : arg finalSat 3 = 0x3000 := by decide
  have a4 : arg finalSat 4 = 0 := by decide
  have a5 : arg finalSat 5 = 0x4000 := by decide
  have a6 : arg finalSat 6 = 0x5000 := by decide
  have e : argAddr finalSat 0 = 0x8004 := by decide
  have esp : finalSat.gpr .esp = 0x8000 := rfl
  cases enc
  · sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Cfb.aesFinalSig, finalPre, finalPost, decryptFinalPost, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, finalX86] [a0, a1, a2, a3, a4, a5, a6, e, esp] using finalSat
  · sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Cfb.aesFinalSig, finalPre, finalPost, encryptFinalPost, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, finalX86] [a0, a1, a2, a3, a4, a5, a6, e, esp] using finalSat

/-! ## The arguments, by name -/

open VG.Impl.AesCfb.X86
open VG.Impl.CmacAes.X86 (argOp)
open VG.Proof.CmacAes.X86 (wp_arg arg_ofNat ofNat_and_self_beq)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_andi wp_test wp_shr wp_sub wp_add eval_e eval_ne)

section
variable (s₀ : State)

abbrev fE : BitVec 32 := s₀.gpr .esp
abbrev fW : BitVec 32 := arg s₀ 0
abbrev fR : Nat := (arg s₀ 1).toNat
abbrev fIv : BitVec 32 := arg s₀ 2
abbrev fD : BitVec 32 := arg s₀ 3
abbrev fL : Nat := (arg s₀ 4).toNat
abbrev fS : BitVec 32 := arg s₀ 5
abbrev fV : BitVec 32 := arg s₀ 6
/-- The number of whole blocks, and of the bytes after them. -/
abbrev fN : Nat := fL s₀ / 16
abbrev fU : Nat := fL s₀ % 16
/-- The data after the whole blocks, as the code computes it. -/
abbrev fT : BitVec 32 := fD s₀ + BitVec.ofNat 32 (16 * fN s₀)

abbrev fSch : Region := ⟨(fW s₀).setWidth 64, 240⟩
abbrev fIvR : Region := ⟨(fIv s₀).setWidth 64, 16⟩
abbrev fData : Region := ⟨(fD s₀).setWidth 64, fL s₀⟩
abbrev fBlk : Region := ⟨(fD s₀).setWidth 64, 16 * fN s₀⟩
abbrev fTail : Region := ⟨(fD s₀).setWidth 64 + BitVec.ofNat 64 (16 * fN s₀), fU s₀⟩
abbrev fScr : Region := ⟨(fS s₀).setWidth 64, 2176⟩
abbrev fSv : Region := ⟨(fV s₀).setWidth 64, 16⟩
abbrev fArgs : Region := ⟨argAddr s₀ 0, 28⟩
abbrev fRet : Region := ⟨(fE s₀).setWidth 64, 4⟩
abbrev fStk : Region := below (fE s₀) 52

/-- The key schedule, the chaining value and the whole blocks on entry. -/
abbrev fWk : List Byte := bytesAt s₀.mem ((fW s₀).setWidth 64) (16 * (fR s₀ + 1))
abbrev fIv0 : List Byte := bytesAt s₀.mem ((fIv s₀).setWidth 64) 16
abbrev fBlks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem ((fD s₀).setWidth 64) (fN s₀)

/-- The memory once the registers are saved. -/
def svMem : Mem := Spill.saveMem s₀.mem ((fV s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr finalSaved

/-- The regions the function writes, with the stack below it. -/
abbrev fBig : List Region := [fIvR s₀, fData s₀, fScr s₀, fSv s₀, fStk s₀]

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [fSch s₀, fArgs s₀]
  wr : s₀.wr = [fIvR s₀, fData s₀, fScr s₀, fSv s₀]
  sch_iv : (fSch s₀).Disjoint (fIvR s₀)
  sch_data : (fSch s₀).Disjoint (fData s₀)
  sch_scr : (fSch s₀).Disjoint (fScr s₀)
  sch_sv : (fSch s₀).Disjoint (fSv s₀)
  iv_data : (fIvR s₀).Disjoint (fData s₀)
  iv_scr : (fIvR s₀).Disjoint (fScr s₀)
  iv_sv : (fIvR s₀).Disjoint (fSv s₀)
  iv_args : (fIvR s₀).Disjoint (fArgs s₀)
  data_scr : (fData s₀).Disjoint (fScr s₀)
  data_sv : (fData s₀).Disjoint (fSv s₀)
  data_args : (fData s₀).Disjoint (fArgs s₀)
  scr_sv : (fScr s₀).Disjoint (fSv s₀)
  scr_args : (fScr s₀).Disjoint (fArgs s₀)
  sv_args : (fSv s₀).Disjoint (fArgs s₀)
  ret_iv : (fRet s₀).Disjoint (fIvR s₀)
  ret_data : (fRet s₀).Disjoint (fData s₀)
  ret_scr : (fRet s₀).Disjoint (fScr s₀)
  ret_sv : (fRet s₀).Disjoint (fSv s₀)
  stk_sch : (fStk s₀).Disjoint (fSch s₀)
  stk_iv : (fStk s₀).Disjoint (fIvR s₀)
  stk_data : (fStk s₀).Disjoint (fData s₀)
  stk_scr : (fStk s₀).Disjoint (fScr s₀)
  stk_sv : (fStk s₀).Disjoint (fSv s₀)
  sch_fit : (fW s₀).toNat + 240 ≤ 2 ^ 32
  iv_fit : (fIv s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (fD s₀).toNat + fL s₀ ≤ 2 ^ 32
  scr_fit : (fS s₀).toNat + 2176 ≤ 2 ^ 32
  sv_fit : (fV s₀).toNat + 16 ≤ 2 ^ 32
  esp52 : 52 ≤ (fE s₀).toNat
  esp_fit : (fE s₀).toNat + 32 ≤ 2 ^ 32
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem stk_eq {s₀ : State} (h : 52 ≤ (fE s₀).toNat) :
    fStk s₀ = ⟨(fE s₀).setWidth 64 - BitVec.ofNat 64 52, 52⟩ := by
  show (⟨(fE s₀ - BitVec.ofNat 32 52).setWidth 64, 52⟩ : Region) = _
  rw [Taint.sub_setWidth h]

theorem FPre.of {enc : Bool} {s₀ : State} (h : (finalX86 enc).pre s₀) : FPre s₀ := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33⟩ := h
  have e := stk_eq a31
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    e ▸ a21, e ▸ a22, e ▸ a23, e ▸ a24, e ▸ a25, a26, a27, a28, a29, a30, a31, a32, a33⟩

/-! ## Addresses and regions -/

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.argA {i : Nat} (hi : i < 7) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 32 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem FPre.arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (fArgs s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem FPre.arg_in {i : Nat} (hi : i < 7) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨fArgs s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem FPre.args_stk : (fArgs s₀).Disjoint (fStk s₀) := by
  have : (s₀.gpr .esp).toNat + 32 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (fE s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  rw [stk_eq hp.esp52]
  show Region.Disjoint ⟨argAddr s₀ 0, 28⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

theorem FPre.ret_stk : (fRet s₀).Disjoint (fStk s₀) := by
  rw [stk_eq hp.esp52]
  have := Offset.disjoint_below_above ((fE s₀).setWidth 64) (m := 52) (a := 0) (l := 4) (by decide)
  rw [BitVec.add_zero] at this
  exact this.symm

/-- The stack arguments are unchanged where only `fBig` changes. -/
theorem FPre.arg_keep {m : Mem} (hf : Frame (fBig s₀) s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.iv_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.data_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.scr_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.sv_args.symm.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

/-- The return address is unchanged where only `fBig` changes. -/
theorem FPre.ret_keep {m : Mem} (hf : Frame (fBig s₀) s₀.mem m) :
    m.readW ((fE s₀).setWidth 64) 32 = s₀.mem.readW ((fE s₀).setWidth 64) 32 :=
  hf.readW (r := fRet s₀) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.ret_iv
    · exact hp.ret_data
    · exact hp.ret_scr
    · exact hp.ret_sv
    · exact hp.ret_stk) (by decide)

theorem FPre.sched_sub : Region.Sub ⟨(fW s₀).setWidth 64, 16 * (fR s₀ + 1)⟩ (fSch s₀) :=
  Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)

theorem FPre.sched_len : 16 * (fR s₀ + 1) ≤ 2 ^ 64 := by rcases hp.rounds with h | h | h <;> omega

/-- The key schedule is unchanged where only `fBig` changes. -/
theorem FPre.sched_keep {m : Mem} (hf : Frame (fBig s₀) s₀.mem m) :
    bytesAt m ((fW s₀).setWidth 64) (16 * (fR s₀ + 1)) = fWk s₀ :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hp.sch_iv.sub_left hp.sched_sub
    · exact hp.sch_data.sub_left hp.sched_sub
    · exact hp.sch_scr.sub_left hp.sched_sub
    · exact hp.sch_sv.sub_left hp.sched_sub
    · exact hp.stk_sch.symm.sub_left hp.sched_sub) hp.sched_len

theorem FPre.blk_fit : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 32 := by
  have := hp.data_fit; have := Nat.mul_div_le (fL s₀) 16; have : fN s₀ = fL s₀ / 16 := rfl; omega

theorem FPre.stk_sub {a k : Nat} (h : a + k ≤ 52) :
    Region.Sub (below (fE s₀ - BitVec.ofNat 32 k) a) (fStk s₀) := below_inner h hp.esp52

end

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)

theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])

theorem FPre.blk_tail {s₀ : State} (hp : FPre s₀) : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  have : fN s₀ = fL s₀ / 16 := rfl
  have : fU s₀ = fL s₀ % 16 := rfl
  exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)

/-- The save changes only `save`. -/
theorem svMem_frame (s₀ : State) : Frame [fSv s₀] s₀.mem (svMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp =>
    have : p.2 + 4 ≤ 16 := (show Spill.Fits 16 finalSaved by decide).1 p hp
    Offset.contains_base _ (by omega) (by omega)

/-- Everything the function writes, from the save on. -/
theorem big_of {s₀ : State} {m : Mem} (hf : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) m) :
    Frame (fBig s₀) s₀.mem m :=
  ((svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h])

/-- The `n` blocks at `D` are unchanged outside a frame that misses them. -/
theorem blocksAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨D, 16 * n⟩ : Region).Disjoint r) :
    Spec.Cbc.blocksAt m' D n = Spec.Cbc.blocksAt m D n :=
  List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame hf
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; omega))) (by decide)

/-! ## Saving the registers, and the whole-block function's arguments -/

theorem and15 (x : BitVec 32) : x &&& (15 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (15 : BitVec 32).toNat = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem shr4 (x : BitVec 32) : x >>> 4 = BitVec.ofNat 32 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem sub_mod16 (x : BitVec 32) :
    x - BitVec.ofNat 32 (x.toNat % 16) = BitVec.ofNat 32 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem finalSaved_fits : Spill.Fits 16 finalSaved := by decide
theorem finalSaved_ne_eax : ∀ p ∈ finalSaved, p.1 ≠ .eax := by decide

theorem setup_eq : finalSave ++ wholeArgs = .mov .eax (argOp 6) :: (Spill.saveCode .eax finalSaved ++ wholeArgs) := rfl

theorem wholeArgs_eq : wholeArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (argOp 2),
    .mov .ebx (argOp 3), .mov .esi (argOp 4), .shift .shr .esi 4, .mov .edi (argOp 5)] := rfl

/-- What saving the registers and setting up the arguments leaves. -/
structure Setup (s₀ s : State) : Prop where
  eax : s.gpr .eax = fW s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = fIv s₀
  ebx : s.gpr .ebx = fD s₀
  esi : s.gpr .esi = BitVec.ofNat 32 (fN s₀)
  edi : s.gpr .edi = fS s₀
  esp : s.gpr .esp = fE s₀
  mem : s.mem = svMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem final_setup_wp {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (finalSave ++ wholeArgs)) s₀ (Setup s₀) := by
  rw [setup_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = fV s₀ := u₁.gpr
  refine Spill.save_ofNat_ok finalSaved finalSaved_fits (by rw [h₁]; exact hp.sv_fit) (fun p hp' => ?_)
    fun s₂ u₂ => ?_
  · have hb : p.2 + 4 ≤ 16 := finalSaved_fits.1 p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = svMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, svMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (finalSaved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  have big := big_of (s₀ := s₀) (Frame.refl _ (svMem s₀))
  have ak : ∀ i < 7, (svMem s₀).readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [wholeArgs_eq]
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
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, shr4]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## The call of the whole-block function -/

open VG.Proof.AesCbc (Mode cts aesWith_state)
open VG.Proof.AesCbc.X86 (modeX86 BlkPre BlkPost blk_call blk_rel toNat_rounds)
open VG.Proof.Aes.X86 (BlocksImpl)

/-- The registers the call pushes, as the whole-block function's arguments. -/
abbrev wholeRegs : List Reg := [.edi, .esi, .ebx, .edx, .ecx, .eax]

theorem wholeRegs_esp : Reg.esp ∉ wholeRegs := by decide

/-- The regions the whole-block function is given. -/
abbrev wholeRd (s₀ : State) : List Region := [fSch s₀, below (fE s₀) 24]
abbrev wholeWr (s₀ : State) : List Region := [fIvR s₀, fBlk s₀, fScr s₀]

theorem toNat_n (s₀ : State) : (BitVec.ofNat 32 (fN s₀)).toNat = fN s₀ := by
  have := (arg s₀ 4).isLt; have : fN s₀ = fL s₀ / 16 := rfl; have : fL s₀ = (arg s₀ 4).toNat := rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

section
variable {s₀ : State} (hp : FPre s₀)
include hp

/-- The callee's return address and stack are in ours. -/
theorem FPre.retC_sub : Region.Sub ⟨(fE s₀ - BitVec.ofNat 32 28).setWidth 64, 4⟩ (fStk s₀) := by
  have : Region.Sub ⟨(fE s₀ - BitVec.ofNat 32 24 - BitVec.ofNat 32 4).setWidth 64, 4⟩ (fStk s₀) :=
    hp.stk_sub (by decide)
  rwa [show fE s₀ - BitVec.ofNat 32 24 - BitVec.ofNat 32 4 = fE s₀ - BitVec.ofNat 32 28 by
    rw [BitVec.sub_sub]; rfl] at this

theorem FPre.stkC_sub :
    Region.Sub ⟨(fE s₀ - BitVec.ofNat 32 28).setWidth 64 - BitVec.ofNat 64 24, 24⟩ (fStk s₀) := by
  have := hp.esp52
  have : Region.Sub ⟨(fE s₀ - BitVec.ofNat 32 28 - BitVec.ofNat 32 24).setWidth 64, 24⟩ (fStk s₀) :=
    hp.stk_sub (by decide)
  rwa [Taint.sub_setWidth (by rw [sub_toNat (by omega)]; omega)] at this

theorem FPre.argsC_sub : Region.Sub (below (fE s₀) 24) (fStk s₀) := below_sub (by decide) hp.esp52

theorem FPre.callee_esp : 24 ≤ (fE s₀ - BitVec.ofNat 32 28).toNat ∧
    (fE s₀ - BitVec.ofNat 32 28).toNat + 28 ≤ 2 ^ 32 := by
  have := hp.esp52; have := hp.esp_fit
  rw [sub_toNat (by omega)]; omega

end

section
variable {s₀ s : State} (hp : FPre s₀) (h : Setup s₀ s)
include hp h

theorem Setup.fit : 4 * wholeRegs.length + 4 ≤ (s.gpr .esp).toNat := by
  rw [h.esp]; have := hp.esp52; simp only [List.length_cons, List.length_nil]; omega

theorem Setup.args : arg (pushed wholeRegs s).callEntry 0 = fW s₀ ∧
    arg (pushed wholeRegs s).callEntry 1 = arg s₀ 1 ∧ arg (pushed wholeRegs s).callEntry 2 = fIv s₀ ∧
    arg (pushed wholeRegs s).callEntry 3 = fD s₀ ∧
    arg (pushed wholeRegs s).callEntry 4 = BitVec.ofNat 32 (fN s₀) ∧
    arg (pushed wholeRegs s).callEntry 5 = fS s₀ := by
  have f := h.fit hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg f wholeRegs_esp (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.esi, h.edi]

omit hp in
theorem Setup.calleeEsp : (pushed wholeRegs s).callEntry.gpr .esp = fE s₀ - BitVec.ofNat 32 28 := by
  rw [callEntry_esp', h.esp]; rfl

omit hp in
theorem Setup.calleeArgs : argAddr (pushed wholeRegs s).callEntry 0 = (fE s₀ - BitVec.ofNat 32 24).setWidth 64 := by
  rw [callEntry_argAddr0, h.esp]; rfl

theorem Setup.callPre {M : Mode} : CallPre (modeX86 M) wholeRegs (wholeRd s₀) (wholeWr s₀) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args hp
  have eA := h.calleeArgs
  have eSp := h.calleeEsp
  obtain ⟨c1, c2⟩ := hp.callee_esp
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, toNat_n]
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_data.sub_right (blk_sub s₀), hp.sch_scr,
      hp.iv_data.sub_right (blk_sub s₀), hp.iv_scr, hp.data_scr.sub_left (blk_sub s₀),
      hp.stk_iv.sub_left hp.argsC_sub, (hp.stk_data.sub_left hp.argsC_sub).sub_right (blk_sub s₀),
      hp.stk_scr.sub_left hp.argsC_sub,
      hp.stk_iv.sub_left hp.retC_sub, (hp.stk_data.sub_left hp.retC_sub).sub_right (blk_sub s₀),
      hp.stk_scr.sub_left hp.retC_sub,
      hp.stk_sch.sub_left hp.stkC_sub, hp.stk_iv.sub_left hp.stkC_sub,
      (hp.stk_data.sub_left hp.stkC_sub).sub_right (blk_sub s₀), hp.stk_scr.sub_left hp.stkC_sub,
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

/-- What the call of the whole-block function leaves, for the mode `M`. -/
structure Whole (M : Mode) (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fBlk s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  iv : bytesAt s.mem ((fIv s₀).setWidth 64) 16 = M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)

theorem Whole.frame' {M : Mode} {s₀ s : State} (h : Whole M s₀ s) :
    Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem :=
  h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem whole_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 M).post s s')
    (hsp : NoSp whole) (hst : stackUse whole = 24) {s₀ : State} (hp : FPre s₀) {s : State} (h : Setup s₀ s) :
    WP isa (wholeCall name whole) s (Whole M s₀) := by
  have f := h.fit hp
  -- What the callee reads, on entry.
  have ef : Frame [fSv s₀, fStk s₀] s₀.mem (pushed wholeRegs s).callEntry.mem :=
    ((svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
      (by
        rw [← h.mem]
        exact (callEntry_frame f wholeRegs_esp).sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨fStk s₀, by simp, by rw [h.esp]; exact below_sub (by decide) hp.esp52⟩)
  have eW : bytesAt (pushed wholeRegs s).callEntry.mem ((fW s₀).setWidth 64) (16 * (fR s₀ + 1)) = fWk s₀ :=
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.sch_sv.sub_left hp.sched_sub
      · exact hp.stk_sch.symm.sub_left hp.sched_sub) hp.sched_len
  have eIv : bytesAt (pushed wholeRegs s).callEntry.mem ((fIv s₀).setWidth 64) 16 = fIv0 s₀ :=
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.iv_sv
      · exact hp.stk_iv.symm) (by decide)
  have eB : Spec.Cbc.blocksAt (pushed wholeRegs s).callEntry.mem ((fD s₀).setWidth 64) (fN s₀) = fBlks s₀ :=
    blocksAt_frame' ef (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_sv.sub_left (blk_sub s₀)
      · exact hp.stk_data.symm.sub_left (blk_sub s₀))
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args hp
  refine WP.callWith (rs := wholeRegs) hv hsp (by decide) wholeRegs_esp
    (by rw [hst, h.esp]; have := hp.esp52; simp only [List.length_cons, List.length_nil]; omega)
    (h.callPre hp) fun s' rd' wr' cs' f' ⟨s₂, m₂, post₂⟩ => ?_
  rw [hst, h.esp, h.mem] at f'
  simp only [modeX86, State.withRegions_mem, arg_withRegions, a0, a1, a2, a3, a4, toNat_n, m₂, eW, eIv,
    eB] at post₂
  exact ⟨by rw [cs' .esp (by simp [calleeSaved]), h.esp], by rw [rd', h.rd], by rw [wr', h.wr], f', post₂.1,
    post₂.2⟩

theorem Whole.of_eq {M : Mode} {s₀ s s' : State} (h : Whole M s₀ s) (esp : s'.gpr .esp = s.gpr .esp)
    (mem : s'.mem = s.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) : Whole M s₀ s' :=
  ⟨by rw [esp, h.esp], by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem]; exact h.frame,
    by rw [mem]; exact h.blocks, by rw [mem]; exact h.iv⟩

/-! ## The partial last segment -/

theorem fU_lt (s₀ : State) : fU s₀ < 16 := Nat.mod_lt _ (by decide)

theorem tailTest_eq : tailTest = [.mov .eax (argOp 4), .alu .and .eax (.imm 15), .alu .test .eax (.reg .eax)] :=
  rfl

/-- The test sets ZF if no bytes are left after the whole blocks. -/
theorem final_test_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.block tailTest) s fun s' => Whole M s₀ s' ∧ s'.zf = some (decide (fU s₀ = 0)) := by
  have big := big_of h.frame'
  rw [tailTest_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [h.rd, h.wr]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => wp_andi fun s₂ u₂ => wp_test fun s₃ f₃ z₃ => WP.block_nil
      ⟨h.of_eq (by rw [f₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd]) (by rw [f₃.wr, u₂.wr, u₁.wr]), ?_⟩
  have := fU_lt s₀
  rw [z₃, u₂.gpr, u₁.gpr, and15, ofNat_and_self_beq (by omega)]

theorem ivArgs_eq : Impl.AesOfb.X86.ivArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (argOp 2),
    .mov .edi (.imm 1), .mov .ebp (argOp 5)] := rfl

/-- The arguments of the call of the block function on the block at `iv`. -/
theorem final_ivArgs_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.block Impl.AesOfb.X86.ivArgs) s fun s' =>
      Whole M s₀ s' ∧ BlkPre s' (fW s₀) (fIv s₀) (fS s₀) (fR s₀) := by
  have big := big_of h.frame'
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have ak : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [ivArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (ak 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact ak 1 (by decide))
    fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact ak 2 (by decide)) fun s₃ u₃ => wp_movi fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact ak 5 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have esp₅ : s₅.gpr .esp = fE s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.esp]
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  have hb : (below (s₅.gpr .esp) 24).Disjoint (fSch s₀) ∧ (below (s₅.gpr .esp) 24).Disjoint (fIvR s₀) ∧
      (below (s₅.gpr .esp) 24).Disjoint (fScr s₀) := by
    rw [esp₅]; exact ⟨hp.stk_sch.sub_left hp.argsC_sub, hp.stk_iv.sub_left hp.argsC_sub,
      hp.stk_scr.sub_left hp.argsC_sub⟩
  refine ⟨h.of_eq (by rw [esp₅, h.esp]) (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [rd₅, h.rd]) (by rw [wr₅, h.wr]), ?_⟩
  exact {
    eax := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
    ecx := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
              exact arg_ofNat s₀ 1
    ebx := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
    edi := by rw [u₅.other _ (by decide), u₄.gpr]
    ebp := u₅.gpr
    rounds := hp.rounds
    esp := by rw [esp₅]; have := hp.esp52; omega
    wd := hp.sch_iv
    ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
    ds := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    bw := hb.1
    bd := hb.2.1
    bs := hb.2.2.sub_right (Region.sub_prefix (by decide))
    hW := hp.sch_fit
    hD := hp.iv_fit
    hS := by have := hp.scr_fit; omega
    reads := by
      rw [rd₅, wr₅, hp.rd, hp.wr]
      exact Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [wr₅, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
      · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩ }

/-- What the call of the block function on the chaining value leaves. -/
structure Ciph (M : Mode) (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tailb : ∀ q < fU s₀, s.mem ((fTail s₀).base + BitVec.ofNat 64 q) = s₀.mem ((fTail s₀).base + BitVec.ofNat 64 q)
  iv : bytesAt s.mem ((fIv s₀).setWidth 64) 16 =
    Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))

theorem final_ciph_wp (v : BlocksImpl) {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State}
    (h : Whole M s₀ s ∧ BlkPre s (fW s₀) (fIv s₀) (fS s₀) (fR s₀)) :
    WP isa (Impl.AesCbc.X86.blkCall v.enc) s (Ciph M s₀) := by
  obtain ⟨hw, hc⟩ := h
  refine WP.mono (blk_call v.encOk v.encNosp v.encStack hc) fun s' c => ?_
  have stk : Region.Sub (below (s.gpr .esp) 24) (fStk s₀) := by rw [hw.esp]; exact hp.argsC_sub
  have fc : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] s.mem s'.mem :=
    c.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨fScr s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨fStk s₀, by simp, stk⟩
  have big := big_of hw.frame'
  have tailD : ∀ r ∈ [fIvR s₀, ⟨(fS s₀).setWidth 64, 2048⟩, below (s.gpr .esp) 24], (fTail s₀).Disjoint r := by
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
  refine ⟨by rw [c.saved .esp (by simp [calleeSaved]), hw.esp], by rw [c.rd, hw.rd], by rw [c.wr, hw.wr],
    hw.frame'.trans fc, ?_, fun q hq => ?_, ?_⟩
  · rw [blocksAt_frame' c.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (blk_sub s₀)
      · exact (hp.data_scr.sub_left (blk_sub s₀)).sub_right (Region.sub_prefix (by decide))
      · exact (hp.stk_data.sub_right (blk_sub s₀)).symm.sub_right stk]
    exact hw.blocks
  · rw [c.frame.bytes tailD hlen hq, hw.frame.bytes tailW hlen hq, (svMem_frame s₀).bytes tailS hlen hq]
  · rw [c.out, ← aesWith_state, hp.sched_keep big, hw.iv]

theorem xorArgs_eq : xorArgs = [.mov .ebx (argOp 2), .mov .esi (argOp 3), .mov .ebp (argOp 4),
    .mov .eax (.reg .ebp), .alu .and .ebp (.imm 15), .alu .sub .eax (.reg .ebp), .alu .add .esi (.reg .eax)] := rfl

/-- The tail loop's operands. -/
structure XArgs (M : Mode) (s₀ s : State) : Prop where
  ciph : Ciph M s₀ s
  ebx : s.gpr .ebx = fIv s₀
  esi : s.gpr .esi = fT s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (fU s₀)

theorem final_xorArgs_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Ciph M s₀ s) :
    WP isa (.block xorArgs) s (XArgs M s₀) := by
  have big := big_of h.frame
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have ak : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [xorArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (ak 2 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide)) (by rw [u₁.mem]; exact ak 3 (by decide))
    fun s₂ u₂ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₂.mem, u₁.mem]; exact ak 4 (by decide)) fun s₃ u₃ => ?_
  refine wp_mov fun s₄ u₄ => wp_andi fun s₅ u₅ => wp_sub fun s₆ u₆ _ => wp_add fun s₇ u₇ => WP.block_nil ?_
  have e₅ : s₅.gpr .ebp = BitVec.ofNat 32 (fU s₀) := by rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, and15]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact h.frame
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact h.blocks
  · intro q hq
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact h.tailb q hq
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact h.iv
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, e₅, sub_mod16]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), e₅]

theorem tail_addr {s₀ : State} (hp : FPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).setWidth 64 = (fTail s₀).base := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  have : fN s₀ = fL s₀ / 16 := rfl
  have : fU s₀ = fL s₀ % 16 := rfl
  exact addr_eq (by omega)

theorem toNat_tail {s₀ : State} (hp : FPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  have : fN s₀ = fL s₀ / 16 := rfl
  have : fU s₀ = fL s₀ % 16 := rfl
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- What the function leaves before restoring the registers. -/
structure Done (M : Mode) (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem ((fD s₀).setWidth 64) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem ((fTail s₀).base + BitVec.ofNat 64 q) = s₀.mem ((fTail s₀).base + BitVec.ofNat 64 q) ^^^
    (Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))).getD q 0
  iv : bytesAt s.mem ((fIv s₀).setWidth 64) 16 = if fU s₀ = 0 then M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
    else Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))

theorem done_of_zero {M : Mode} {s₀ s : State} (h : Whole M s₀ s) (hu : fU s₀ = 0) : Done M s₀ s :=
  ⟨h.esp, h.rd, h.wr, h.frame', h.blocks, fun q hq => absurd hq (by omega), by rw [ite_eq_left hu]; exact h.iv⟩

theorem final_xor_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : XArgs M s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.loop (.block Impl.Modes.X86.tailByte) .ne) s (Done M s₀) := by
  have hU := fU_lt s₀
  have hT := toNat_tail hp hu
  have eT := tail_addr hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_fit
  have eN : fN s₀ = fL s₀ / 16 := rfl
  have eU : fU s₀ = fL s₀ % 16 := rfl
  have hc := h.ciph
  have xp : Modes.X86.XPre s (fIv s₀) (fT s₀) (fU s₀) := {
    pos := by omega
    fitK := by have := hp.iv_fit; omega
    fitR := by rw [hT]; omega
    disj := by
      rw [eT]
      exact (hp.iv_data.sub_left (Region.sub_prefix (by omega))).sub_right (tail_sub s₀)
    rdK := fun q hq => by
      rw [hc.rd, hc.wr, hp.rd, hp.wr]
      exact ⟨fIvR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    wrR := fun q hq => by
      rw [hc.wr, hp.wr, eT]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show (fTail s₀).base + BitVec.ofNat 64 q = (fD s₀).setWidth 64 + BitVec.ofNat 64 (16 * fN s₀ + q) from
        Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega) }
  have x0 : Modes.X86.XInv s (fIv s₀) (fT s₀) (fU s₀) 0 s := {
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
  refine ⟨by rw [d.gpr .esp (by decide) (by decide) (by decide) (by decide) (by decide), hc.esp],
    by rw [d.rd, hc.rd], by rw [d.wr, hc.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact hc.frame.trans (fT'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' fT' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact hc.blocks
  · have := d.data q hq
    rw [eT] at this
    rw [this, hc.tailb q hq, MdStream.X86.bytesAt_getD hc.iv (show q < 16 by omega)]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame fT' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.sub_right (tail_sub s₀)) (by decide), hc.iv]

theorem final_mid_wp (v : BlocksImpl) {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s)
    (hz : s.zf = some (decide (fU s₀ = 0))) :
    WP isa (.ite .e (.block []) (finalTail v.enc)) s (Done M s₀) := by
  have ev : isa.eval .e s = some (decide (fU s₀ = 0)) := by
    show VG.X86.eval .e s = _; rw [eval_e, hz]
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [ev, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [ev, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (final_ivArgs_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (final_ciph_wp v hp h₁) fun _ h₂ =>
        WP.seq (WP.mono (final_xorArgs_wp hp h₂) fun _ h₃ => final_xor_wp hp h₃ hu)))

/-! ## Restoring the registers -/

theorem restore_eq : finalRestore = .mov .eax (argOp 6) :: (Spill.restoreCode .eax finalSaved ++ []) := rfl

theorem final_end_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Done M s₀ s) :
    WP isa (.block finalRestore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  have big := big_of h.frame
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hs : Spill.Saved s.mem ((fV s₀).setWidth 64 + BitVec.ofNat 64 ·) s₀.gpr finalSaved :=
    (Spill.saveMem_saved_ofNat s₀.mem _ s₀.gpr finalSaved_fits (by decide)).of_frame h.frame
      (fun p hp' => Offset.contains_base _ (finalSaved_fits.1 p hp') (by have := finalSaved_fits.1 p hp'; omega))
      fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.iv_sv.symm
        · exact hp.data_sv.symm
        · exact hp.scr_sv.symm
        · exact hp.stk_sv.symm
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => ?_
  refine Spill.restore_ofNat_ok finalSaved finalSaved_fits (by rw [u₁.gpr]; exact hp.sv_fit) finalSaved_ne_eax
    (fun p hp' => ?_) (by rw [u₁.gpr, u₁.mem]; exact hs) fun s₂ r₂ => WP.block_nil ?_
  · have := finalSaved_fits.1 p hp'
    rw [u₁.gpr, u₁.rd, u₁.wr, hrw, hp.rd, hp.wr]
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine ⟨⟨r₂.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, by rw [r₂.mem, u₁.mem]⟩
  rw [r₂.mem, u₁.mem]; exact hp.ret_keep big

/-! ## The whole function -/

theorem final_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 M).post s s')
    (hsp : NoSp whole) (hst : stackUse whole = 24) (v : BlocksImpl) {s₀ : State} (hp : FPre s₀) :
    WP isa (final name whole v.enc) s₀ fun s' => abiPreserved s₀ s' ∧ ∃ s₁, Done M s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hv hsp hst hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_test_wp hp h₂) fun s₃ ⟨h₃, z₃⟩ => ?_)
  refine WP.seq (WP.mono (final_mid_wp v hp h₃ z₃) fun s₄ h₄ => ?_)
  exact WP.mono (final_end_wp hp h₄) fun _ ⟨g, m⟩ => ⟨g, s₄, h₄, m⟩

/-- The specification's results, from what the function leaves. -/
theorem final_post {enc : Bool} {s₀ s₁ s' : State} (h : Done (cfbMode enc) s₀ s₁) (hm : s'.mem = s₁.mem) :
    (finalX86 enc).post s₀ s' := by
  cases enc
  · show Spec.Cfb.DecryptFinal (ciphAt s₀.mem ((fW s₀).setWidth 64) (fR s₀)) 16 s₀.mem s'.mem
      ((fIv s₀).setWidth 64) ((fD s₀).setWidth 64) (fL s₀)
    exact decryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)
  · show Spec.Cfb.EncryptFinal (ciphAt s₀.mem ((fW s₀).setWidth 64) (fR s₀)) 16 s₀.mem s'.mem
      ((fIv s₀).setWidth 64) ((fD s₀).setWidth 64) (fL s₀)
    exact encryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)

theorem final_correct {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 (cfbMode enc)).post s s')
    (hsp : NoSp whole) (hst : stackUse whole = 24) (v : BlocksImpl) (s : State) (hs : (finalX86 enc).pre s) :
    ∃ t s', Exec isa (final name whole v.enc) s t s' ∧ abiPreserved s s' ∧ (finalX86 enc).post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp hv hsp hst v (FPre.of hs)
  exact ⟨t, s', he, hg, final_post h₁ hm⟩

/-! ## Constant time -/

/-- What two runs agree on at a point between the calls. -/
structure Pt (s₀ s : State) : Prop where
  esp : s.gpr .esp = fE s₀
  wr : s.wr = s₀.wr
  args : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

theorem FPre.argsOut {s₀ : State} (hp : FPre s₀) {s : State} (h : Pt s₀ s) : ArgsOut 7 s := by
  have hs := hp.esp_fit
  refine ⟨by rw [h.esp]; omega, ?_⟩
  rw [h.wr, hp.wr, h.esp]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact Taint.frame_disjoint (n := 28) (by omega) hp.ret_iv hp.iv_args.symm
  · exact Taint.frame_disjoint (n := 28) (by omega) hp.ret_data hp.data_args.symm
  · exact Taint.frame_disjoint (n := 28) (by omega) hp.ret_scr hp.scr_args.symm
  · exact Taint.frame_disjoint (n := 28) (by omega) hp.ret_sv hp.sv_args.symm

theorem arg_cur {s₀ s : State} (hesp : s.gpr .esp = s₀.gpr .esp) {i : Nat}
    (hm : s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) : arg s i = arg s₀ i := by
  show s.mem.readW (argAddr s i) 32 = _
  rw [show argAddr s i = argAddr s₀ i by simp only [argAddr, hesp]]; exact hm

/-- Two runs agree on `esp`, the stack arguments and the registers `rs`. -/
theorem Pt.agree {enc : Bool} {s₀ s₀' : State} (hq : (finalX86 enc).pub s₀ s₀') (hp : FPre s₀) (hp' : FPre s₀')
    {rs : List Reg} {s₁ s₂ : State} (h₁ : Pt s₀ s₁) (h₂ : Pt s₀' s₂) (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (argTaint rs (4 + 4 * 7)) s₁ s₂ :=
  agree_argTaint hr (by rw [h₁.esp, h₂.esp, fE, fE, hq.1]) (hp.argsOut h₁) (hp'.argsOut h₂)
    fun i hi => by rw [arg_cur h₁.esp (h₁.args i hi), arg_cur h₂.esp (h₂.args i hi), hq.2 i hi]

theorem Setup.pt {s₀ s : State} (hp : FPre s₀) (h : Setup s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => by rw [h.mem]; exact hp.arg_keep (big_of (Frame.refl _ _)) hi⟩

theorem Whole.pt {M : Mode} {s₀ s : State} (hp : FPre s₀) (h : Whole M s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of h.frame') hi⟩

theorem Ciph.pt {M : Mode} {s₀ s : State} (hp : FPre s₀) (h : Ciph M s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of h.frame) hi⟩

theorem Done.pt {M : Mode} {s₀ s : State} (hp : FPre s₀) (h : Done M s₀ s) : Pt s₀ s :=
  ⟨h.esp, h.wr, fun _ hi => hp.arg_keep (big_of h.frame) hi⟩

theorem final_rel {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 (cfbMode enc)).post s s')
    (hct : ConstantTime isa (modeX86 (cfbMode enc)).pre (modeX86 (cfbMode enc)).pub whole)
    (hsp : NoSp whole) (hst : stackUse whole = 24) (v : BlocksImpl) {s₀ s₀' : State}
    (h0 : (finalX86 enc).pre s₀) (h0' : (finalX86 enc).pre s₀') (hq : (finalX86 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (final name whole v.enc) fun _ _ => True := by
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  have qE : fE s₀ = fE s₀' := hq.1
  have qA : ∀ i < 7, arg s₀ i = arg s₀' i := hq.2
  have qW : fW s₀ = fW s₀' := qA 0 (by decide)
  have qR : fR s₀ = fR s₀' := by simp only [fR, qA 1 (by decide)]
  have qIv : fIv s₀ = fIv s₀' := qA 2 (by decide)
  have qD : fD s₀ = fD s₀' := qA 3 (by decide)
  have qL : fL s₀ = fL s₀' := by simp only [fL, qA 4 (by decide)]
  have qS : fS s₀ = fS s₀' := qA 5 (by decide)
  have qU : fU s₀ = fU s₀' := by simp only [fU, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, qL]
  have pt₀ : ∀ {t : State}, Pt t t := ⟨rfl, rfl, fun _ _ => rfl⟩
  -- The registers saved and the whole-block function's arguments.
  obtain ⟨_, t₁⟩ : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block (finalSave ++ wholeArgs)) h).isSome =
      true := ⟨_, by taint_decide⟩
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
  have c₂ := RelCT.callWith (k := modeX86 (cfbMode enc)) (n := name) (rs := wholeRegs) hv hct
    (P := fun a b => Setup s₀ a ∧ Setup s₀' b) (wholeRd s₀) (wholeWr s₀) fun a b ⟨ha, hb⟩ => by
      have pb := hb.callPre (M := cfbMode enc) hp'
      rw [eRd, eWr] at pb
      obtain ⟨a0, a1, a2, a3, a4, a5⟩ := ha.args hp
      obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hb.args hp'
      refine ⟨ha.callPre hp, pb, by rw [ha.esp, hb.esp, qE], ?_, fun i hi => ?_⟩
      · simp only [State.withRegions_gpr, ha.calleeEsp, hb.calleeEsp, qE]
      · simp only [arg_withRegions]
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [a0, b0, qW]
        · rw [a1, b1, qA 1 (by decide)]
        · rw [a2, b2, qIv]
        · rw [a3, b3, qD]
        · rw [a4, b4, qN]
        · rw [a5, b5, qS]
  have r₂ : RelCT isa (fun a b => Setup s₀ a ∧ Setup s₀' b) (wholeCall name whole)
      (fun a b => Whole (cfbMode enc) s₀ a ∧ Whole (cfbMode enc) s₀' b) :=
    (RelCT.wp (c := wholeCall name whole) (F₁ := Whole (cfbMode enc) s₀) (F₂ := Whole (cfbMode enc) s₀') c₂
      fun a b h => ⟨whole_wp hv hsp hst hp h.1, whole_wp hv hsp hst hp' h.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  -- The test.
  obtain ⟨_, t₃⟩ : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block tailTest) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have r₃ := ((RelCT.taint (A := taint)
    (P := fun a b => Whole (cfbMode enc) s₀ a ∧ Whole (cfbMode enc) s₀' b) _
    (fun a b h => Pt.agree (rs := []) hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr) t₃).wp
    (F₁ := fun (s : State) => Whole (cfbMode enc) s₀ s ∧ s.zf = some (decide (fU s₀ = 0)))
    (F₂ := fun (s : State) => Whole (cfbMode enc) s₀' s ∧ s.zf = some (decide (fU s₀' = 0)))
    fun a b h => ⟨final_test_wp hp h.1, final_test_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  -- The partial last segment.
  obtain ⟨_, t₄⟩ : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block Impl.AesOfb.X86.ivArgs) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, t₅⟩ : ∃ h, (taint.check (argTaint [] (4 + 4 * 7))
      (.seq (.block xorArgs) (.loop (.block Impl.Modes.X86.tailByte) .ne)) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole (cfbMode enc) s₀ a ∧ Whole (cfbMode enc) s₀' b)
      (finalTail v.enc) fun a b => Done (cfbMode enc) s₀ a ∧ Done (cfbMode enc) s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₄ := ((RelCT.taint (A := taint)
      (P := fun a b => Whole (cfbMode enc) s₀ a ∧ Whole (cfbMode enc) s₀' b) _
      (fun a b h => Pt.agree (rs := []) hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr) t₄).wp
      (F₁ := fun (s : State) => Whole (cfbMode enc) s₀ s ∧ BlkPre s (fW s₀) (fIv s₀) (fS s₀) (fR s₀))
      (F₂ := fun (s : State) => Whole (cfbMode enc) s₀' s ∧ BlkPre s (fW s₀') (fIv s₀') (fS s₀') (fR s₀'))
      fun a b h => ⟨final_ivArgs_wp hp h.1, final_ivArgs_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    have a₅ := ((blk_rel (b := v.enc) v.encOk v.encCt (E := fE s₀)
      (P := fun a b => (Whole (cfbMode enc) s₀ a ∧ BlkPre a (fW s₀) (fIv s₀) (fS s₀) (fR s₀)) ∧
        (Whole (cfbMode enc) s₀' b ∧ BlkPre b (fW s₀') (fIv s₀') (fS s₀') (fR s₀')))
      fun a b h => by
        have e₂ := h.2.2
        rw [← qW, ← qIv, ← qS, ← qR] at e₂
        exact ⟨h.1.2, e₂, h.1.1.esp, by rw [h.2.1.esp, qE]⟩).wp
      (F₁ := Ciph (cfbMode enc) s₀) (F₂ := Ciph (cfbMode enc) s₀')
      fun a b h => ⟨final_ciph_wp v hp h.1, final_ciph_wp v hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
    have a₆ := ((RelCT.taint (A := taint)
      (P := fun a b => Ciph (cfbMode enc) s₀ a ∧ Ciph (cfbMode enc) s₀' b) _
      (fun a b h => Pt.agree (rs := []) hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr) t₅).wp
      (F₁ := Done (cfbMode enc) s₀) (F₂ := Done (cfbMode enc) s₀')
      fun a b h => ⟨WP.seq (WP.mono (final_xorArgs_wp hp h.1) fun _ h₃ => final_xor_wp hp h₃ hu),
        WP.seq (WP.mono (final_xorArgs_wp hp' h.2) fun _ h₃ => final_xor_wp hp' h₃ hu')⟩).mono
          (fun _ _ h => h) fun _ _ h => h.2
    exact a₄.seq (a₅.seq a₆)
  have r₄ : RelCT isa (fun a b => (Whole (cfbMode enc) s₀ a ∧ a.zf = some (decide (fU s₀ = 0))) ∧
      (Whole (cfbMode enc) s₀' b ∧ b.zf = some (decide (fU s₀' = 0))))
      (.ite .e (.block []) (finalTail v.enc))
      (fun a b => Done (cfbMode enc) s₀ a ∧ Done (cfbMode enc) s₀' b) := by
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
  obtain ⟨_, t₆⟩ : ∃ h, (taint.check (argTaint [] (4 + 4 * 7)) (.block finalRestore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have r₅ := RelCT.taint (A := taint) (P := fun a b => Done (cfbMode enc) s₀ a ∧ Done (cfbMode enc) s₀' b) _
    (fun a b h => Pt.agree (rs := []) hq hp hp' (h.1.pt hp) (h.2.pt hp') fun r hr => by simp at hr) t₆
  exact r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))

theorem final_ct {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeX86 (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeX86 (cfbMode enc)).post s s')
    (hct : ConstantTime isa (modeX86 (cfbMode enc)).pre (modeX86 (cfbMode enc)).pub whole)
    (hsp : NoSp whole) (hst : stackUse whole = 24) (v : BlocksImpl) :
    ConstantTime isa (finalX86 enc).pre (finalX86 enc).pub (final name whole v.enc) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel hv hct hsp hst v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The code's properties -/

theorem all_of_noSp {c : Prog isa} (h : NoSp c) : c.allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  rw [Code.allInstrs_eq, List.all_eq_true]
  intro i hi
  simp [h i hi]

theorem encrypt_noSp (v : BlocksImpl) : NoSp (encrypt v.enc) :=
  NoSp.of_all (by
    simp only [encrypt, Impl.AesCbc.X86.whole, body, Impl.AesCbc.X86.blkCall, Code.allInstrs,
      all_of_noSp v.encNosp]
    decide +kernel)

theorem decrypt_noSp (v : BlocksImpl) : NoSp (decrypt v.enc) :=
  NoSp.of_all (by
    simp only [decrypt, Impl.AesCbc.X86.whole, body, Impl.AesCbc.X86.blkCall, Code.allInstrs,
      all_of_noSp v.encNosp]
    decide +kernel)

theorem encrypt_stack (v : BlocksImpl) : stackUse (encrypt v.enc) = 24 := by
  simp only [encrypt, Impl.AesCbc.X86.whole, body, Impl.AesCbc.X86.blkCall, stackUse, v.encStack]
  decide

theorem decrypt_stack (v : BlocksImpl) : stackUse (decrypt v.enc) = 24 := by
  simp only [decrypt, Impl.AesCbc.X86.whole, body, Impl.AesCbc.X86.blkCall, stackUse, v.encStack]
  decide

theorem encryptFinal_noSp (v : BlocksImpl) :
    (encryptFinal v.enc v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [encryptFinal, final, wholeCall, finalTail, Impl.AesCbc.X86.blkCall, Code.allInstrs,
    all_of_noSp (encrypt_noSp v), all_of_noSp v.encNosp]
  decide +kernel

theorem decryptFinal_noSp (v : BlocksImpl) :
    (decryptFinal v.enc v.suffix).allInstrs (fun i => !Taint.clobbers i .esp) = true := by
  simp only [decryptFinal, final, wholeCall, finalTail, Impl.AesCbc.X86.blkCall, Code.allInstrs,
    all_of_noSp (decrypt_noSp v), all_of_noSp v.encNosp]
  decide +kernel

theorem encryptFinal_stack (v : BlocksImpl) : stackUse (encryptFinal v.enc v.suffix) ≤ 52 := by
  simp only [encryptFinal, final, wholeCall, finalTail, Impl.AesCbc.X86.blkCall, stackUse, encrypt_stack v,
    v.encStack]
  decide

theorem decryptFinal_stack (v : BlocksImpl) : stackUse (decryptFinal v.enc v.suffix) ≤ 52 := by
  simp only [decryptFinal, final, wholeCall, finalTail, Impl.AesCbc.X86.blkCall, stackUse, decrypt_stack v,
    v.encStack]
  decide

theorem encryptFinal_spSafe (v : BlocksImpl) :
    (encryptFinal v.enc v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [encryptFinal, final, wholeCall, finalTail, Impl.AesCbc.X86.blkCall, Code.all, encrypt_spSafe v,
    v.encSpSafe]
  decide +kernel

theorem decryptFinal_spSafe (v : BlocksImpl) :
    (decryptFinal v.enc v.suffix).all (fun i => !isa.writesSp i) = true := by
  simp only [decryptFinal, final, wholeCall, finalTail, Impl.AesCbc.X86.blkCall, Code.all, decrypt_spSafe v,
    v.encSpSafe]
  decide +kernel

/-! ## Verified -/

theorem encryptFinal_verified (v : BlocksImpl) :
    Verified X86.target (encryptFinal v.enc v.suffix) (finalScratchContract true) :=
  Verified.of_correct
    (final_correct (fun _ hs => AesCbc.X86.whole_wp (encBody_ok v) hs) (encrypt_noSp v) (encrypt_stack v) v)
    (final_ct (fun _ hs => AesCbc.X86.whole_wp (encBody_ok v) hs) (AesCbc.X86.whole_ct (encBody_ok v) (encBody_ct v))
      (encrypt_noSp v) (encrypt_stack v) v)
    (final_implies true)

theorem decryptFinal_verified (v : BlocksImpl) :
    Verified X86.target (decryptFinal v.enc v.suffix) (finalScratchContract false) :=
  Verified.of_correct
    (final_correct (fun _ hs => AesCbc.X86.whole_wp (decBody_ok v) hs) (decrypt_noSp v) (decrypt_stack v) v)
    (final_ct (fun _ hs => AesCbc.X86.whole_wp (decBody_ok v) hs) (AesCbc.X86.whole_ct (decBody_ok v) (decBody_ct v))
      (decrypt_noSp v) (decrypt_stack v) v)
    (final_implies false)

/-! ## With `save` on the stack

The final functions have six argument slots, so `save` is their seventh
argument: they run their code in a frame of 48 bytes
(`withStackScratchWiped 48 6 4`): the word standing for the return address,
a copy of the six arguments, `save`'s address, and `save`'s 16 bytes, which
it zeroes before returning. The code's calls use 52 bytes below it, so 100
in all. -/

theorem frameSat_pre (post : Spec.Cfb.aesFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cfb.aesFinalSig.contract X86.abi (pre := finalPre X86.abi.ptrBits) (post := post)
      (stack := 100)).pre s := by
  have a0 : arg AesCbc.X86.sat 0 = 0x1000 := by decide
  have a1 : arg AesCbc.X86.sat 1 = 10 := by decide
  have a2 : arg AesCbc.X86.sat 2 = 0x2000 := by decide
  have a3 : arg AesCbc.X86.sat 3 = 0x3000 := by decide
  have a4 : arg AesCbc.X86.sat 4 = 0 := by decide
  have a5 : arg AesCbc.X86.sat 5 = 0x4000 := by decide
  have e : argAddr AesCbc.X86.sat 0 = 0x8004 := by decide
  have esp : AesCbc.X86.sat.gpr .esp = 0x8000 := rfl
  sig_implies_sat [Spec.Cfb.aesFinalSig, finalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, a5, e, esp] using AesCbc.X86.sat

theorem encryptFinal_framed (v : BlocksImpl) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (encryptFinal v.enc v.suffix))
      (encryptFinalRoundsContract X86.abi 100) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 2)
    (pre := finalPre X86.abi.ptrBits) (post := encryptFinalPost X86.abi.ptrBits) (wa := false) (stack := 52)
    (bytes := 48) (words := 4) (encryptFinal_verified v) (by decide) (encryptFinal_noSp v) (encryptFinal_stack v)
    (by decide) (finalPre_local _) (encryptFinalPost_local _) (encryptFinalPost_localOut _) (frameSat_pre _)

theorem decryptFinal_framed (v : BlocksImpl) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (decryptFinal v.enc v.suffix))
      (decryptFinalRoundsContract X86.abi 100) :=
  X86.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 2)
    (pre := finalPre X86.abi.ptrBits) (post := decryptFinalPost X86.abi.ptrBits) (wa := false) (stack := 52)
    (bytes := 48) (words := 4) (decryptFinal_verified v) (by decide) (decryptFinal_noSp v) (decryptFinal_stack v)
    (by decide) (finalPre_local _) (decryptFinalPost_local _) (decryptFinalPost_localOut _) (frameSat_pre _)

theorem framed_spSafe {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.StackScratch.X86.withStackScratchWiped 48 6 4 c).all (fun i => !isa.writesSp i) = true := by
  have hf : (Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (.block [])).all
      (fun i => !isa.writesSp i) = true := by decide +kernel
  simp only [Impl.StackScratch.X86.withStackScratchWiped, Impl.StackScratch.X86.withStackScratch, Code.all,
    List.all_nil, Bool.and_eq_true] at hf ⊢
  simp_all

theorem encryptFinal_framed_spSafe (v : BlocksImpl) :
    (Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (encryptFinal v.enc v.suffix)).all
      (fun i => !isa.writesSp i) = true :=
  framed_spSafe (encryptFinal_spSafe v)

theorem decryptFinal_framed_spSafe (v : BlocksImpl) :
    (Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (decryptFinal v.enc v.suffix)).all
      (fun i => !isa.writesSp i) = true :=
  framed_spSafe (decryptFinal_spSafe v)

end VG.Proof.AesCfb.X86
