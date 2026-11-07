module

public import VerifiedGarbage.Impl.Camellia.Arm.CtrFinal
public import VerifiedGarbage.Proof.Camellia.CtrFinal
public import VerifiedGarbage.Proof.Camellia.CtrScratch
public import VerifiedGarbage.Proof.Camellia.Arm.CtrVerified
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.CmacAes.Arm.Words
public import VerifiedGarbage.Proof.AesGcm.Arm.Callee
import VerifiedGarbage.Proof.AesCfb.Arm.Final
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.Cmac.Block32
import VerifiedGarbage.Proof.AesCbc.Mem32
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Impl.Camellia.Arm.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.CtrFinal
meta import VerifiedGarbage.Proof.Camellia.CtrScratch
meta import VerifiedGarbage.Proof.Camellia.Arm.CtrVerified
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Spill
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.CmacAes.Arm.Words
meta import VerifiedGarbage.Proof.AesGcm.Arm.Callee
meta import VerifiedGarbage.Proof.AesCfb.Arm.Final
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.Cmac.Block32
meta import VerifiedGarbage.Proof.AesCbc.Mem32
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# Camellia-CTR of a message's last piece on ARMv7

`ctrFinal_framed`: `vg_camellia_ctr_final` (`Impl/Camellia/Arm/CtrFinal.lean`)
meets `Spec.Camellia.ctrFinalContract`, from `Proof.Camellia.ctrFinalContractSk`
(`Proof.Camellia.ctrFinal_of_sk`).

The code is proven against `ctrFinalArm`, with a sixth argument `save` of
56 bytes on the stack (`ctrFinal_implies`: the shared contract with it), as
a caller of `vg_camellia_ctr` (framed by its own working space on the stack,
`ctrFramed`), through its contract on the subkeys, `ctrContractSk`
(`ctrFramed_sk`), in a frame that pushes its stack argument: what a call
needs and leaves (`WCall`, `WPost`, `w_call`, constant time by `w_rel`). The
proof is AES-CTR's (`Proof/AesCtr/Arm/Final.lean`), with Camellia's
arguments:

* `setup_wp`, `whole_wp`: the registers saved in `save`, and the call on the
  `n = len / 16` whole blocks (`Whole`), which leaves `Tₙ₊₁` in `ctr`;
* `mid_wp`: if `u = len % 16` bytes are left, the block at `save + 40`
  zeroed and the call on it (`tail_args_wp`, `tail_call`), which leaves
  `CIPH_K(Tₙ₊₁)` there and `Tₙ₊₂` in `ctr`, and its first `u` bytes XORed
  into them (`Modes.Arm.xorLoop_wp`, `tail_xor_wp`); what is left before the
  registers are restored is `Done`;
* `end_wp`: the registers restored;
* `final_post`: `Done` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`).

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
the callee's constant time (`RelCT.call`), whose public arguments agree.
-/

@[expose] public section

namespace VG.Proof.Camellia.Arm.CtrFinal

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.Camellia.Arm (ctrFramed ctrSave ctrFinalMoves ctrFinalSetup ctrCall ctrTailArgs ctrXorArgs
  ctrFinalTail ctrFinal)
open VG.Impl.AesCfb.Arm (finalSaved finalSave finalRestore)
open VG.Proof.AesCfb.Arm (shr4 and15 shl4 blocksAt_frame' preserved_saved)
open VG.Proof.AesGcm.Arm (toNat_ofNat32 below pushed_sp8 hspA hA fA view_gpr view_sp arg0 arg1 argAddr0
  cover_pushed cover_pushed' cover_frame covers_append' stackArg_callEntry stackArgAddr_callEntry)
open VG.Arm.FrameStack (armStack belowA)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_and wp_cmp wp_ldrSp
  ofNat_beq_zero)
open VG.Proof.Modes.Arm (XPre XInv XDone xorLoop_wp xf add0_32)

/-- The code's contract, with the arguments `(schedule = r0, rounds = r1,
ctr = r2, data = r3, len = [sp], save = [sp + 4])`, `save` of 56 bytes: the
data and the counter block as `Spec.Ctr.CryptFinal` says, by Camellia with
the subkeys at `schedule`. -/
def ctrFinalArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 272⟩
    let ctr : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let sv : Region := ⟨State.addr (stackArg s 1), 56⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 2912, 2912⟩
    2912 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      s.rd = [sched, args] ∧ s.wr = [ctr, data, sv] ∧
      sched.Disjoint ctr ∧ sched.Disjoint data ∧ sched.Disjoint sv ∧
      ctr.Disjoint data ∧ ctr.Disjoint sv ∧ ctr.Disjoint args ∧
      data.Disjoint sv ∧ data.Disjoint args ∧ sv.Disjoint args ∧
      stk.Disjoint sched ∧ stk.Disjoint ctr ∧ stk.Disjoint data ∧ stk.Disjoint sv ∧ stk.Disjoint args ∧
      (s.gpr .r0).toNat + 272 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 56 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 18 ∨ (s.gpr .r1).toNat = 24)
  post s s' :=
    Spec.Ctr.CryptFinal (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem (State.addr (s.gpr .r0))
      (s.gpr .r1).toNat)) s.mem s'.mem (State.addr (s.gpr .r2)) (State.addr (s.gpr .r3)) (stackArg s 0).toNat
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- The contract the frame needs: the shared one on the subkeys, with
`save`, 56 bytes, as a sixth argument, and 2912 bytes of stack (the frame
pushing `vg_camellia_ctr`'s stack argument, and its frame and calls). -/
abbrev ctrFinalScratchContract : Contract isa :=
  Sig.scratchContract Arm.abi Spec.Camellia.ctrFinalSig "save" .u64 7 (Spec.Camellia.ctrFinalPre Arm.abi.ptrBits)
    (Proof.Camellia.ctrFinalPostSk Arm.abi.ptrBits) true 2912

/-- A state satisfying the precondition: the schedule at `0x1000`, 18
rounds, the counter block at `0x2000`, no data at `0x3000` and `save` at
`0x6000` (the stack arguments at `0x8000`). -/
def ctrFinalSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 18 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8005 then 0x60 else 0
  rd := [⟨0x1000, 272⟩, ⟨0x8000, 8⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x6000, 56⟩]

theorem ctrFinal_implies : ctrFinalArm.Implies ctrFinalScratchContract := by
  sig_implies [ctrFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Camellia.ctrFinalSig, Spec.Camellia.ctrFinalPre, Proof.Camellia.ctrFinalPostSk, ctrFinalArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [ctrFinalSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using ctrFinalSat

/-! ## The callee -/

/-- `vg_camellia_ctr` meets its contract on the subkeys. -/
theorem ctrFramed_sk : Verified Arm.target ctrFramed (Proof.Camellia.ctrContractSk Arm.abi 2904) :=
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64) (n := 9)
    (pre := Spec.Camellia.ctrPre Arm.abi.ptrBits) (post := Proof.Camellia.ctrPostSk Arm.abi.ptrBits)
    (wa := true) (stack := 2816) (m := 1) (bytes := 88)
    Proof.Camellia.Arm.ctr_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (Proof.Camellia.ctrPre_local _) (Proof.Camellia.ctrPost_local _) (Proof.Camellia.ctrPostOut_local _)
    Proof.Camellia.Arm.ctrFrameSat

theorem ctr_stack : armStack ctrFramed ≤ 2904 := by decide +kernel

/-- The 2912 bytes below the stack pointer `sp`, which a call uses: the 8
its frame pushes, and the 2904 of `vg_camellia_ctr` below them. -/
abbrev stk (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 2912, 2912⟩

theorem below_stk (sp : BitVec 32) : Region.Sub (below sp) (stk sp) :=
  Offset.sub_below _ (by decide) (by decide)

theorem belowA_stk {sp : BitVec 32} {n : Nat} (hn : n ≤ 2904) (hsp : 2912 ≤ sp.toNat) :
    Region.Sub (belowA (sp - 8) n) (stk sp) := by
  show Region.Sub ⟨State.addr (sp - 8 - BitVec.ofNat 32 n), n⟩ _
  rw [BitVec.sub_sub, show (8 : BitVec 32) + BitVec.ofNat 32 n = BitVec.ofNat 32 (8 + n) by
    rw [BitVec.ofNat_add]; rfl, FrameStack.addr_sub' (by omega)]
  have e : State.addr sp - BitVec.ofNat 64 (8 + n) =
      State.addr sp - BitVec.ofNat 64 2912 + BitVec.ofNat 64 (2904 - n) := by
    have := sp.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [State.addr, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact Offset.sub_base _ (by omega)

theorem res_stk (sp : BitVec 32) :
    Region.Sub ⟨State.addr sp - BitVec.ofNat 64 8 - BitVec.ofNat 64 2904, 2904⟩ (stk sp) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]
  exact Region.sub_prefix (by decide)

/-- What a call of `vg_camellia_ctr` needs: the subkeys at `W` for `R`
rounds, the counter block at `C` and `n` blocks at `D`, in `r0`–`r3`, `n` in
`r12` to push, and the 2912 bytes below the stack pointer. -/
structure WCall (s : State) (W R C D : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = R
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 n
  rounds : R.toNat = 18 ∨ R.toNat = 24
  hsp : 2912 ≤ s.sp.toNat
  fitW : W.toNat + 272 ≤ 2 ^ 32
  fitC : C.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  wc : (⟨State.addr W, 272⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  wd : (⟨State.addr W, 272⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  cd : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  bw : (stk s.sp).Disjoint ⟨State.addr W, 272⟩
  bc : (stk s.sp).Disjoint ⟨State.addr C, 16⟩
  bd : (stk s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  reads : Covers [⟨State.addr W, 272⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩] s.wr

/-- Camellia with the subkeys at `W` for `R` rounds. -/
abbrev wCiph (m : Mem) (W R : BitVec 32) : Spec.Cbc.Cipher :=
  Spec.Camellia.cipher (Spec.Camellia.subkeysAt m (State.addr W) R.toNat)

/-- What a call of `vg_camellia_ctr` leaves. -/
structure WPost (s : State) (W R C D : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, stk s.sp] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem (State.addr D) n =
    Spec.Ctr.crypt (wCiph s.mem W R) (bytesAt s.mem (State.addr C) 16) (Spec.Cbc.blocksAt s.mem (State.addr D) n)
  ctr : bytesAt s'.mem (State.addr C) 16 = Spec.Ctr.next (bytesAt s.mem (State.addr C) 16) n

abbrev wRd (sp W : BitVec 32) : List Region := [⟨State.addr W, 272⟩, ⟨State.addr sp - 8, 4⟩]
abbrev wWr (C D : BitVec 32) (n : Nat) : List Region := [⟨State.addr C, 16⟩, ⟨State.addr D, n * 16⟩]

namespace WCall
variable {s : State} {W R C D : BitVec 32} {n : Nat} (h : WCall s W R C D n)
include h

theorem hsp8 : 8 ≤ s.sp.toNat := by have := h.hsp; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem pre : (Proof.Camellia.ctrContractSk Arm.abi 2904).pre
    ((pushed [.r12, .lr] s).callEntry.withRegions (wRd s.sp W) (wWr C D n)) := by
  have hn := toNat_ofNat32 h.n_lt
  have hs8 := h.hsp8
  sig_pre [Proof.Camellia.ctrContractSk, Spec.Camellia.ctrSig, Spec.Camellia.ctrPre, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val]
  simp only [stackArgAddr_withRegions, stackArg_withRegions, stackArg_callEntry, stackArgAddr_callEntry,
    arg0 hs8, argAddr0 hs8, h.r0, h.r1, h.r2, h.r3, h.r12, hn, FrameStack.sub_toNat' (sp := s.sp) (k := 8) hs8,
    FrameStack.addr_sub' (x := s.sp) (k := 8) hs8, Nat.mul_comm n 16]
  have b4 : Region.Sub ⟨State.addr s.sp - 8, 4⟩ (stk s.sp) := fun a ha =>
    below_stk s.sp a (Region.sub_prefix (by decide) a ha)
  have rs := res_stk s.sp
  refine ⟨by have := h.hsp; omega, by have := s.sp.isLt; omega, rfl, by rw [wWr, Nat.mul_comm]; rfl, h.wc, h.wd,
    h.cd, (h.bc.sub_left b4).symm, (h.bd.sub_left b4).symm, h.bw.sub_left rs, h.bc.sub_left rs, h.bd.sub_left rs,
    (Offset.base_disjoint_below (State.addr s.sp - BitVec.ofNat 64 8) (n := 2904) (k := 4) (by decide)).symm,
    h.fitW, h.fitC, h.fitD, h.rounds⟩

theorem cov : Covers (wRd s.sp W ++ wWr C D n) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  rw [show wWr C D n = [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩] by rw [Nat.mul_comm]]
  refine covers_append' (covers_append' (cover_pushed' h.reads) (cover_frame h.hsp8 (by decide)))
    (cover_pushed' (fun x n' hi => ?_))
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (wWr C D n) (pushed [.r12, .lr] s).wr := by
  rw [show wWr C D n = [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩] by rw [Nat.mul_comm]]
  exact cover_pushed h.writes

end WCall

theorem w_call {s : State} {W R C D : BitVec 32} {n : Nat} (h : WCall s W R C D n) :
    WP isa ctrCall s (WPost s W R C D n) := by
  have hs8 := h.hsp8
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using hs8) (by simp) ?_
  refine FrameStack.WP.callF (k := Proof.Camellia.ctrContractSk Arm.abi 2904) ctrFramed_sk.1 (rd := wRd s.sp W)
    (wr := wWr C D n) h.pre h.cov h.covW
    (by rw [pushed_sp8, hspA hs8]; have := h.hsp; have := ctr_stack; omega) ?_
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs hpost
  have hn := toNat_ofNat32 h.n_lt
  have fA' := fA (s := s) hs8
  have b8 := below_stk s.sp
  have eW : Spec.Camellia.subkeysAt (pushed [.r12, .lr] s).mem (State.addr W) R.toNat =
      Spec.Camellia.subkeysAt s.mem (State.addr W) R.toNat :=
    Proof.Camellia.subkeysAt_congr (by rcases h.rounds with h' | h' <;> rw [h'] <;> decide)
      fun i hi => fA'.bytes (R := ⟨State.addr W, 272⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (h.bw.sub_left b8).symm) (by show 272 ≤ 2 ^ 64; decide) hi
  have bytesC : bytesAt (pushed [.r12, .lr] s).mem (State.addr C) 16 = bytesAt s.mem (State.addr C) 16 :=
    Proof.Cmac.bytesAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.bc.sub_left b8).symm) (by decide)
  have blocksD : Spec.Cbc.blocksAt (pushed [.r12, .lr] s).mem (State.addr D) n =
      Spec.Cbc.blocksAt s.mem (State.addr D) n :=
    blocksAt_frame' fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.bd.sub_left b8).symm)
  sig_post [Proof.Camellia.ctrContractSk, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at hpost
  have ep : storeWords s.mem (s.sp - 8#32) [s.gpr .r12, s.gpr .lr] = (pushed [.r12, .lr] s).mem := rfl
  rw [ep, h.r0, h.r1, h.r2, h.r3, stackArg_withRegions, stackArg_callEntry, arg0 hs8, h.r12, hn] at hpost
  obtain ⟨hdata, hctr⟩ := hpost h.rounds
  have hdata' : Spec.Cbc.blocksAt s₂.mem (State.addr D) n =
      Spec.Ctr.crypt (Spec.Camellia.cipher (Spec.Camellia.subkeysAt (pushed [.r12, .lr] s).mem (State.addr W) R.toNat))
        (bytesAt (pushed [.r12, .lr] s).mem (State.addr C) 16)
        (Spec.Cbc.blocksAt (pushed [.r12, .lr] s).mem (State.addr D) n) := hdata
  have hctr' : bytesAt s₂.mem (State.addr C) 16 =
      Spec.Ctr.next (bytesAt (pushed [.r12, .lr] s).mem (State.addr C) 16) n := hctr
  rw [eW, bytesC, blocksD] at hdata'
  rw [bytesC] at hctr'
  have fB : Frame (wWr C D n ++ [belowA (pushed [.r12, .lr] s).sp (armStack ctrFramed)])
      (pushed [.r12, .lr] s).mem s₂.mem := hf
  rw [pushed_sp8] at fB
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp8]; exact BitVec.sub_add_cancel _ _
  · rw [popped_gpr (by rintro rfl; simp [preserved] at hr), hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (fA'.sub fun r hr => ?_).trans (fB.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stk s.sp, by simp, b8⟩
    · simp only [wWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr D, 16 * n⟩, by simp, fun _ hx => by rwa [Nat.mul_comm] at hx⟩
      · exact ⟨stk s.sp, by simp, belowA_stk ctr_stack h.hsp⟩
  · rw [popped_mem]; exact hdata'
  · rw [popped_mem]; exact hctr'

/-- Calls of `vg_camellia_ctr` with the same arguments and stack pointer in
both runs are constant time. -/
theorem w_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W R C D : BitVec 32, ∃ n : Nat,
      WCall s₁ W R C D n ∧ WCall s₂ W R C D n ∧ s₁.sp = s₂.sp) :
    RelCT isa P ctrCall fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, _, _, _, _, _, e⟩ := h _ _ hp; exact e) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, pa, pb⟩ e₁ e₂
  obtain ⟨W, R, C, D, n, h₁, h₂, hsp⟩ := h _ _ hp
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₁.hsp8), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₂.hsp8), Option.some.injEq] at pb
  subst pa pb
  have hn := toNat_ofNat32 h₁.n_lt
  refine RelCT.call (k := Proof.Camellia.ctrContractSk Arm.abi 2904) ctrFramed_sk.1 ctrFramed_sk.2.1
    (wRd s₁.sp W) (wWr C D n) (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₂ := h₂.pre
  rw [← hsp] at p₂
  refine ⟨h₁.pre, p₂, ?_, h₁.cov, h₁.covW, hsp ▸ h₂.cov, h₂.covW⟩
  sig_pub [Proof.Camellia.ctrContractSk, Spec.Camellia.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  simp only [stackArg_withRegions, stackArg_callEntry, arg0 h₁.hsp8, arg0 h₂.hsp8, h₁.r0, h₁.r1, h₁.r2, h₁.r3,
    h₁.r12, h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.r12, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## The arguments, by name -/

section
variable (s₀ : State)

abbrev fW : BitVec 32 := s₀.gpr .r0
abbrev fR : Nat := (s₀.gpr .r1).toNat
abbrev fC : BitVec 32 := s₀.gpr .r2
abbrev fD : BitVec 32 := s₀.gpr .r3
abbrev fL : Nat := (stackArg s₀ 0).toNat
abbrev fV : BitVec 32 := stackArg s₀ 1
/-- The number of whole blocks, and of the bytes after them. -/
abbrev fN : Nat := fL s₀ / 16
abbrev fU : Nat := fL s₀ % 16
/-- The data after the whole blocks, as a register holds it and as an
address. -/
abbrev fT : BitVec 32 := fD s₀ + BitVec.ofNat 32 (16 * fN s₀)
abbrev fTa : Addr := State.addr (fD s₀) + BitVec.ofNat 64 (16 * fN s₀)

abbrev fSch : Region := ⟨State.addr (fW s₀), 272⟩
abbrev fCR : Region := ⟨State.addr (fC s₀), 16⟩
abbrev fData : Region := ⟨State.addr (fD s₀), fL s₀⟩
abbrev fBlk : Region := ⟨State.addr (fD s₀), 16 * fN s₀⟩
abbrev fTail : Region := ⟨fTa s₀, fU s₀⟩
abbrev cSv : Region := ⟨State.addr (fV s₀), 56⟩
abbrev fArg : Region := ⟨stackArgAddr s₀ 0, 8⟩
abbrev fStk : Region := stk s₀.sp

/-- The block in `save`. -/
abbrev cBk32 : BitVec 32 := fV s₀ + 40
abbrev cBk : Addr := State.addr (fV s₀) + BitVec.ofNat 64 40
abbrev cBlk : Region := ⟨cBk s₀, 16⟩

/-- The counter block and the whole blocks on entry, and the cipher. -/
abbrev fT0 : List Byte := bytesAt s₀.mem (State.addr (fC s₀)) 16
abbrev fBlks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (State.addr (fD s₀)) (fN s₀)
abbrev cCiph : Spec.Cbc.Cipher := wCiph s₀.mem (fW s₀) (s₀.gpr .r1)

/-- The memory once the registers are saved. -/
abbrev svMem : Mem := Spill.saveMem s₀.mem (State.addr (fV s₀)) s₀.gpr finalSaved

/-- What the function writes after the save: before the XOR, and in all. -/
abbrev cW1 : List Region := [fCR s₀, fBlk s₀, cBlk s₀, fStk s₀]
abbrev cW : List Region := [fCR s₀, fData s₀, cBlk s₀, fStk s₀]
abbrev cBig : List Region := [fCR s₀, fData s₀, cSv s₀, fStk s₀]

end

/-- The precondition, by name. -/
structure KPre (s₀ : State) : Prop where
  sp_lo : 2912 ≤ s₀.sp.toNat
  sp_hi : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rd : s₀.rd = [fSch s₀, fArg s₀]
  wr : s₀.wr = [fCR s₀, fData s₀, cSv s₀]
  sch_c : (fSch s₀).Disjoint (fCR s₀)
  sch_data : (fSch s₀).Disjoint (fData s₀)
  sch_sv : (fSch s₀).Disjoint (cSv s₀)
  c_data : (fCR s₀).Disjoint (fData s₀)
  c_sv : (fCR s₀).Disjoint (cSv s₀)
  c_arg : (fCR s₀).Disjoint (fArg s₀)
  data_sv : (fData s₀).Disjoint (cSv s₀)
  data_arg : (fData s₀).Disjoint (fArg s₀)
  sv_arg : (cSv s₀).Disjoint (fArg s₀)
  stk_sch : (fStk s₀).Disjoint (fSch s₀)
  stk_c : (fStk s₀).Disjoint (fCR s₀)
  stk_data : (fStk s₀).Disjoint (fData s₀)
  stk_sv : (fStk s₀).Disjoint (cSv s₀)
  stk_arg : (fStk s₀).Disjoint (fArg s₀)
  sch_fit : (fW s₀).toNat + 272 ≤ 2 ^ 32
  c_fit : (fC s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (fD s₀).toNat + fL s₀ ≤ 2 ^ 32
  sv_fit : (fV s₀).toNat + 56 ≤ 2 ^ 32
  rounds : fR s₀ = 18 ∨ fR s₀ = 24

theorem KPre.of {s₀ : State} (h : ctrFinalArm.pre s₀) : KPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23⟩

/-! ## Regions -/

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl
theorem fL_lt (s₀ : State) : fL s₀ < 2 ^ 32 := (stackArg s₀ 0).isLt
theorem fU_lt (s₀ : State) : fU s₀ < 16 := Nat.mod_lt _ (by decide)

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)
theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])
theorem blk_sv_sub (s₀ : State) : Region.Sub (cBlk s₀) (cSv s₀) := Offset.sub_base _ (by decide)

section
variable {s₀ : State} (hp : KPre s₀)
include hp

theorem KPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_fit
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [fN_eq, fU_eq]; omega)

theorem KPre.blk_fit : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 32 := by
  have := hp.data_fit; have := Nat.mul_div_le (fL s₀) 16; rw [fN_eq]; omega

/-- The stack arguments' addresses. -/
theorem KPre.argAddr {k : Nat} (hk : k < 2) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_hi
  simp only [stackArgAddr]
  rw [VG.Arm.addr_add (by omega), VG.Arm.addr_add (by omega)]
  simp

theorem KPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨fArg s₀, by simp [hp.rd], ?_⟩
  rw [hp.argAddr hk]
  exact Offset.contains_base _ (by omega) (by omega)

theorem KPre.tail_lt (hu : fU s₀ ≠ 0) : (fD s₀).toNat + 16 * fN s₀ < 2 ^ 32 := by
  have := hp.data_fit; have := Nat.div_add_mod (fL s₀) 16; rw [fN_eq]; rw [fU_eq] at hu; omega

theorem KPre.tailA (hu : fU s₀ ≠ 0) : State.addr (fT s₀) = fTa s₀ := VG.Arm.addr_add (hp.tail_lt hu)

theorem KPre.tail_toNat (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.tail_lt hu
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem KPre.bkA : State.addr (cBk32 s₀) = cBk s₀ := VG.Arm.addr_add (k := 40) (by have := hp.sv_fit; omega)

theorem KPre.bk_toNat : (cBk32 s₀).toNat = (fV s₀).toNat + 40 := by
  have := hp.sv_fit
  rw [BitVec.toNat_add, show (40 : BitVec 32).toNat = 40 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem KPre.c_blk : (fCR s₀).Disjoint (cBlk s₀) := hp.c_sv.sub_right (blk_sv_sub s₀)

theorem KPre.sch_big : ∀ r ∈ cBig s₀, (fSch s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_c
  · exact hp.sch_data
  · exact hp.sch_sv
  · exact hp.stk_sch.symm

/-- The cipher, from any memory the function leaves. -/
theorem KPre.ciph {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) : wCiph m (fW s₀) (s₀.gpr .r1) = cCiph s₀ := by
  show Spec.Camellia.cipher (Spec.Camellia.subkeysAt m _ _) = _
  rw [Proof.Camellia.subkeysAt_congr (by rcases hp.rounds with h | h <;> simp only [fR] at h <;> rw [h] <;> decide)
    fun i hi => hf.bytes (R := fSch s₀) hp.sch_big (by show 272 ≤ 2 ^ 64; decide) hi]

/-- The stack arguments survive what the function writes. -/
theorem KPre.argMem {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) {k : Nat} (hk : k < 2) :
    m.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := by
  refine hf.readW (r := fArg s₀) ?_ (fun r hr => ?_) (by decide)
  · rw [hp.argAddr hk]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.c_arg.symm
    · exact hp.data_arg.symm
    · exact hp.sv_arg.symm
    · exact hp.stk_arg.symm

end

/-- The save changes only `save`. -/
theorem svMem_frame (s₀ : State) : Frame [cSv s₀] s₀.mem (svMem s₀) :=
  Spill.saveMem_frame _ _ _ (L := 56) (by decide) finalSaved (by decide)

theorem big_frame {s₀ : State} {m : Mem} (hf : Frame (cW s₀) (svMem s₀) m) : Frame (cBig s₀) s₀.mem m :=
  ((svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨cSv s₀, by simp, blk_sv_sub s₀⟩
      · exact ⟨_, by simp, fun _ h => h⟩)

theorem cW1_cW {s₀ : State} {m : Mem} (hf : Frame (cW1 s₀) (svMem s₀) m) : Frame (cW s₀) (svMem s₀) m :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem KPre.svFrame {s₀ : State} (_ : KPre s₀) : Frame (cBig s₀) s₀.mem (svMem s₀) :=
  (svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]

theorem KPre.svArg {s₀ : State} (hp : KPre s₀) {k : Nat} (hk : k < 2) :
    (svMem s₀).readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := hp.argMem hp.svFrame hk

/-! ## Saving the registers -/

/-- What saving the registers and setting up the arguments leaves. -/
structure Setup (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = fW s₀
  r1 : s.gpr .r1 = s₀.gpr .r1
  r2 : s.gpr .r2 = fC s₀
  r3 : s.gpr .r3 = fD s₀
  r4 : s.gpr .r4 = fW s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = fC s₀
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 32 (fN s₀)
  sp : s.sp = s₀.sp
  mem : s.mem = svMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem moves_eq : ctrFinalMoves =
    [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2), .ldrSp .r8 0, .mov .r12 (.shifted .r8 .lsr 4),
     .dp .and .r8 .r8 (.imm 15), .dp .add .r7 .r3 (.shifted .r12 .lsl 4)] := rfl

theorem setup_wp {s₀ : State} (hp : KPre s₀) : WP isa (.block ctrFinalSetup) s₀ (Setup s₀) := by
  show WP isa (.block (.ldrSp .r12 4 :: (finalSave ++ ctrFinalMoves))) s₀ _
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
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
  rw [moves_eq]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂]; rfl) (by
      rw [u₅.rd, u₄.rd, u₃.rd, u₅.wr, u₄.wr, u₃.wr, rd₂, wr₂]; exact hp.arg_in (by decide)) fun s₆ u₆ => ?_
  have mem₅ : s₅.mem = svMem s₀ := by rw [u₅.mem, u₄.mem, u₃.mem, mem₂]
  have r8₆ : s₆.gpr .r8 = stackArg s₀ 0 := by rw [u₆.gpr, mem₅, hp.svArg (by decide)]
  refine wp_mov (op2_lsr (by decide)) fun s₇ u₇ => wp_and (op2_imm (by decide)) fun s₈ u₈ => ?_
  refine wp_add (op2_lsl (by decide)) fun s₉ u₉ => WP.block_nil ?_
  have hN : 16 * fN s₀ < 2 ^ 32 := by have := fL_lt s₀; rw [fN_eq]; omega
  have r12₇ : s₇.gpr .r12 = BitVec.ofNat 32 (fN s₀) := by rw [u₇.gpr, r8₆, shr4]
  have k₅ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s₅.gpr r = s₀.gpr r := fun r h4 h5 h6 h12 => by
    rw [u₅.other _ h6, u₄.other _ h5, u₃.other _ h4, keep₂ _ h12]
  have k₉ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → r ≠ .r8 → r ≠ .r7 → s₉.gpr r = s₀.gpr r :=
    fun r h4 h5 h6 h12 h8 h7 => by
      rw [u₉.other _ h7, u₈.other _ h8, u₇.other _ h12, u₆.other _ h8, k₅ _ h4 h5 h6 h12]
  exact {
    r0 := k₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r1 := k₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r2 := k₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r3 := k₉ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    r4 := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, keep₂ _ (by decide)]
    r5 := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), keep₂ _ (by decide)]
    r6 := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), keep₂ _ (by decide)]
    r7 := by
      rw [u₉.gpr, u₈.other .r12 (by decide), u₈.other .r3 (by decide), r12₇, shl4 hN, u₇.other _ (by decide),
        u₆.other _ (by decide), k₅ _ (by decide) (by decide) (by decide) (by decide)]
    r8 := by
      rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), r8₆]
      exact and15 _
    r12 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), r12₇]
    sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂]
    mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, mem₅]
    rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂]
    wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂] }

/-! ## The whole blocks -/

/-- What the call on the whole blocks leaves. -/
structure Whole (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = fW s₀
  r5 : s.gpr .r5 = s₀.gpr .r1
  r6 : s.gpr .r6 = fC s₀
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fCR s₀, fBlk s₀, fStk s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = Spec.Ctr.crypt (cCiph s₀) (fT0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (State.addr (fC s₀)) 16 = Spec.Ctr.next (fT0 s₀) (fN s₀)

theorem setup_call {s₀ : State} (hp : KPre s₀) {s : State} (h : Setup s₀ s) :
    WCall s (fW s₀) (s₀.gpr .r1) (fC s₀) (fD s₀) (fN s₀) := by
  have hst : stk s.sp = fStk s₀ := by rw [h.sp]
  refine ⟨h.r0, h.r1, h.r2, h.r3, h.r12, hp.rounds, by rw [h.sp]; exact hp.sp_lo, hp.sch_fit, hp.c_fit,
    hp.blk_fit, hp.sch_c, hp.sch_data.sub_right (blk_sub s₀), hp.c_data.sub_right (blk_sub s₀),
    by rw [hst]; exact hp.stk_sch, by rw [hst]; exact hp.stk_c, by rw [hst]; exact hp.stk_data.sub_right (blk_sub s₀),
    ?_, ?_⟩
  · rw [h.rd, h.wr, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fCR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fData s₀, by simp, 0, by simp, by simpa using Nat.mul_div_le (fL s₀) 16⟩

theorem whole_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : Setup s₀ s) : WP isa ctrCall s (Whole s₀) := by
  refine WP.mono (w_call (setup_call hp h)) fun s' w => ?_
  have keep : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r := w.saved
  have eW : wCiph s.mem (fW s₀) (s₀.gpr .r1) = cCiph s₀ := by rw [h.mem]; exact hp.ciph hp.svFrame
  have eC : bytesAt s.mem (State.addr (fC s₀)) 16 = fT0 s₀ := by
    rw [h.mem]; exact Proof.Cmac.bytesAt_frame (svMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_sv) (by decide)
  have eB : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = fBlks s₀ := by
    rw [h.mem]; exact blocksAt_frame' (svMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (blk_sub s₀))
  have hst : stk s.sp = fStk s₀ := by rw [h.sp]
  refine ⟨by rw [keep .r4 (by simp [preserved]) (by decide), h.r4],
    by rw [keep .r5 (by simp [preserved]) (by decide), h.r5],
    by rw [keep .r6 (by simp [preserved]) (by decide), h.r6],
    by rw [keep .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [keep .r8 (by simp [preserved]) (by decide), h.r8],
    by rw [w.sp, h.sp], by rw [w.rd, h.rd], by rw [w.wr, h.wr], ?_, ?_, ?_⟩
  · rw [← h.mem]; have f := w.frame; rw [hst] at f; exact f
  · rw [w.out, eW, eC, eB]
  · rw [w.ctr, eC]

theorem Whole.of_fupd {s₀ s s' : State} (h : Whole s₀ s) (g : s'.gpr = s.gpr) (m : s'.mem = s.mem)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Whole s₀ s' :=
  ⟨by rw [g, h.r4], by rw [g, h.r5], by rw [g, h.r6], by rw [g, h.r7], by rw [g, h.r8], by rw [sp, h.sp],
    by rw [rd, h.rd], by rw [wr, h.wr], by rw [m]; exact h.frame, by rw [m]; exact h.blocks, by rw [m]; exact h.ctr⟩

/-- The test sets Z if no bytes are left after the whole blocks. -/
theorem test_wp {s₀ s : State} (h : Whole s₀ s) :
    WP isa (.block [.cmp .r8 (.imm 0)]) s fun s' => Whole s₀ s' ∧ s'.z = decide (fU s₀ = 0) :=
  wp_cmp (op2_imm (by decide)) fun s' f z => WP.block_nil ⟨h.of_fupd f.gpr f.mem f.rd f.wr f.sp, by
    rw [z, h.r8]; exact MdStream.Arm.cmp0 (by have := fU_lt s₀; omega)⟩

/-! ## The partial last block -/

theorem whole_cW1 {s₀ s : State} (h : Whole s₀ s) : Frame (cW1 s₀) (svMem s₀) s.mem :=
  h.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h]

theorem KPre.tail_cW1 {s₀ : State} (hp : KPre s₀) : ∀ r ∈ cW1 s₀, (fTail s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.c_data.sub_right (tail_sub s₀)).symm
  · exact hp.blk_tail.symm
  · exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)
  · exact (hp.stk_data.sub_right (tail_sub s₀)).symm

theorem KPre.blk_tailW {s₀ : State} (hp : KPre s₀) : ∀ r ∈ [fCR s₀, cBlk s₀, fStk s₀], (fBlk s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.c_data.sub_right (blk_sub s₀)).symm
  · exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  · exact (hp.stk_data.sub_right (blk_sub s₀)).symm

/-- What the arguments of the call on the block leave. -/
structure TArgs (s₀ s : State) : Prop where
  call : WCall s (fW s₀) (s₀.gpr .r1) (fC s₀) (cBk32 s₀) 1
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = Spec.Ctr.crypt (cCiph s₀) (fT0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (State.addr (fC s₀)) 16 = Spec.Ctr.next (fT0 s₀) (fN s₀)
  zero : bytesAt s.mem (cBk s₀) 16 = List.replicate 16 0
  tailb : ∀ q < fU s₀, s.mem (fTa s₀ + BitVec.ofNat 64 q) = s₀.mem (fTa s₀ + BitVec.ofNat 64 q)

theorem tailArgs_eq : ctrTailArgs = .ldrSp .r12 4 :: .mov .r0 (.imm 0) :: (Proof.CmacAes.Arm.zeroBlk .r0 .r12 40 ++
    ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .mov .r2 (.reg .r6), .dp .add .r3 .r12 (.imm 40),
     .mov .r12 (.imm 1)] : List Instr)) := rfl

theorem tail_args_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : Whole s₀ s) :
    WP isa (.block ctrTailArgs) s (TArgs s₀) := by
  rw [tailArgs_eq]
  have f1 := whole_cW1 h
  have big := big_frame (cW1_cW f1)
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [h.sp]; rfl)
    (by rw [h.rd, h.wr]; exact hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have r12₁ : s₁.gpr .r12 = fV s₀ := by rw [u₁.gpr]; exact hp.argMem big (by decide)
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
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ =>
    wp_add (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_imm (by decide)) fun s₈ u₈ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h0 h12 => by
    rw [g₃, u₂.other _ h0, u₁.other _ h12]
  have mem₈ : s₈.mem = Proof.Cmac.zero4 s.mem (cBk s₀) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
  have sp₈ : s₈.sp = s₀.sp := by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, h.sp]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd]
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, h.wr]
  have zf : Frame [cBlk s₀] s.mem (Proof.Cmac.zero4 s.mem (cBk s₀)) := AesCbc.zero4_frame _ _
  have hst : stk s₈.sp = fStk s₀ := by rw [sp₈]
  have bkA := hp.bkA
  have hbk := hp.bk_toNat
  refine ⟨⟨?_, ?_, ?_, ?_, by rw [u₈.gpr]; rfl, hp.rounds, by rw [sp₈]; exact hp.sp_lo, hp.sch_fit, hp.c_fit,
    by rw [hbk]; omega, hp.sch_c, ?_, ?_, by rw [hst]; exact hp.stk_sch, by rw [hst]; exact hp.stk_c, ?_, ?_, ?_⟩,
    ?_, ?_, sp₈, rd₈, wr₈, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g₂ _ (by decide) (by decide), h.r4]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      g₂ _ (by decide) (by decide), h.r5]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g₂ _ (by decide) (by decide), h.r6]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, u₂.other _ (by decide), r12₁]
  · rw [bkA, Nat.mul_one]; exact hp.sch_sv.sub_right (blk_sv_sub s₀)
  · rw [bkA, Nat.mul_one]; exact hp.c_blk
  · rw [hst, bkA, Nat.mul_one]; exact hp.stk_sv.sub_right (blk_sv_sub s₀)
  · rw [rd₈, wr₈, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₈, hp.wr, bkA, Nat.mul_one]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fCR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 40, rfl, by simp⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), g₂ _ (by decide) (by decide), h.r7]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), g₂ _ (by decide) (by decide), h.r8]
  · rw [mem₈]
    exact f1.trans (zf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [mem₈, blocksAt_frame' zf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)), h.blocks]
  · rw [mem₈, Proof.Cmac.bytesAt_frame zf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_blk) (by decide), h.ctr]
  · rw [mem₈, Proof.Cmac.zero4_bytes]; rfl
  · rw [mem₈]
    have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; have := fU_lt s₀; omega
    rw [zf.bytes (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)) hlen hq,
      f1.bytes hp.tail_cW1 hlen hq,
      (svMem_frame s₀).bytes (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (tail_sub s₀)) hlen hq]

theorem cipher_length (sk : Spec.Camellia.Subkeys) (b : List Byte) : (Spec.Camellia.cipher sk b).length = 16 := by
  simp [Spec.Camellia.cipher]

/-- What the call on the block leaves. -/
structure TCall (s₀ s : State) : Prop where
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = Spec.Ctr.crypt (cCiph s₀) (fT0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (State.addr (fC s₀)) 16 = Spec.Ctr.next (fT0 s₀) (fN s₀ + 1)
  key : bytesAt s.mem (cBk s₀) 16 = cCiph s₀ (Spec.Ctr.next (fT0 s₀) (fN s₀))
  tailb : ∀ q < fU s₀, s.mem (fTa s₀ + BitVec.ofNat 64 q) = s₀.mem (fTa s₀ + BitVec.ofNat 64 q)

theorem tail_call {s₀ : State} (hp : KPre s₀) {s s' : State} (h : TArgs s₀ s)
    (w : WPost s (fW s₀) (s₀.gpr .r1) (fC s₀) (cBk32 s₀) 1 s') : TCall s₀ s' := by
  have keep : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r := w.saved
  have hst : stk s.sp = fStk s₀ := by rw [h.sp]
  have fw : Frame [fCR s₀, cBlk s₀, fStk s₀] s.mem s'.mem := by
    have f := w.frame; rw [hst, hp.bkA, Nat.mul_one] at f; exact f
  have big := big_frame (cW1_cW h.frame)
  have eW : wCiph s.mem (fW s₀) (s₀.gpr .r1) = cCiph s₀ := hp.ciph big
  have hout := w.out
  rw [hp.bkA, eW, h.ctr] at hout
  have hkey := Proof.Modes.CtrFinal.bytesAt_of_blocksAt_one (cipher_length _) h.zero hout
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; have := fU_lt s₀; omega
  refine ⟨by rw [keep .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [keep .r8 (by simp [preserved]) (by decide), h.r8], by rw [w.sp, h.sp], by rw [w.rd, h.rd],
    by rw [w.wr, h.wr], h.frame.trans (fw.sub fun r hr => ?_), ?_, ?_, hkey, fun q hq => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · rw [blocksAt_frame' fw hp.blk_tailW]; exact h.blocks
  · rw [w.ctr, h.ctr]; rfl
  · rw [fw.bytes (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.c_data.sub_right (tail_sub s₀)).symm
      · exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact (hp.stk_data.sub_right (tail_sub s₀)).symm) hlen hq]
    exact h.tailb q hq

/-- What the function leaves before restoring the registers. -/
structure Done (s₀ s : State) : Prop where
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = Spec.Ctr.crypt (cCiph s₀) (fT0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fTa s₀ + BitVec.ofNat 64 q) = s₀.mem (fTa s₀ + BitVec.ofNat 64 q) ^^^
    (cCiph s₀ (Spec.Ctr.next (fT0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem (State.addr (fC s₀)) 16 =
    Spec.Ctr.next (fT0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : Whole s₀ s) (hu : fU s₀ = 0) : Done s₀ s :=
  ⟨h.sp, h.rd, h.wr, cW1_cW (whole_cW1 h), h.blocks, fun q hq => absurd hq (by omega),
    by rw [ite_eq_left_of_eq_true _ _ (eq_true hu), h.ctr]⟩

theorem xorArgs_eq : ctrXorArgs = [.ldrSp .r12 4, .dp .add .r0 .r12 (.imm 40), .mov .r6 (.reg .r7),
    .mov .r7 (.reg .r8)] := rfl

theorem tail_xor_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : TCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block ctrXorArgs) (.loop (.block Impl.Modes.Arm.xorByte) .ne)) s (Done s₀) := by
  have big := big_frame (cW1_cW h.frame)
  rw [xorArgs_eq]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [h.sp]; rfl)
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
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_data.sub_right (tail_sub s₀)) (by decide),
      mem₄, h.ctr]

theorem mid_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : Whole s₀ s) (hz : s.z = decide (fU s₀ = 0)) :
    WP isa (.ite .eq (.block []) ctrFinalTail) s (Done s₀) := by
  have ev : isa.eval .eq s = some (decide (fU s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [VG.Proof.MdStream.Arm.eval_eq, hz]
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [ev, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [ev, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (tail_args_wp hp h) fun _ a =>
      WP.seq (WP.mono (w_call a.call) fun _ c => tail_xor_wp hp (tail_call hp a c) hu))

/-! ## Restoring the registers -/

theorem end_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : Done s₀ s) :
    WP isa (.block (ctrSave ++ finalRestore)) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  show WP isa (.block (.ldrSp .r12 4 :: finalRestore)) s _
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [h.sp]; rfl)
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
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.c_sv.symm.sub_left hsub
    · exact hp.data_sv.symm.sub_left hsub
    · exact Offset.disjoint _ (d := 0) (n := 36) (e := 40) (k := 16) (.inl (by decide)) (by decide) (by decide)
    · exact hp.stk_sv.symm.sub_left hsub
  refine WP.mono (Spill.restore_block_ok (b := .r12) (lo := 0) (hi := 36) (by decide) (by decide)
    (by rw [r12]; omega) (fun d _ hd => ?_) hs) fun s' ⟨g, _, m, _, _, sp⟩ => ?_
  · rw [u₁.rd, u₁.wr, h.rd, h.wr, r12]
    exact ⟨cSv s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  · exact ⟨⟨fun r hr => Spill.restored_reg g (preserved_saved r hr), by rw [sp, u₁.sp, h.sp]⟩, by rw [m, u₁.mem]⟩

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : KPre s₀) :
    WP isa ctrFinal s₀ fun s' => abiPreserved s₀ s' ∧ ∃ s₁, Done s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (test_wp h₂) fun s₃ ⟨h₃, z₃⟩ => ?_)
  refine WP.seq (WP.mono (mid_wp hp h₃ z₃) fun s₄ h₄ => ?_)
  exact WP.mono (end_wp hp h₄) fun _ ⟨g, m⟩ => ⟨g, s₄, h₄, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalArm.post s₀ s' := by
  show Spec.Ctr.CryptFinal (cCiph s₀) s₀.mem s'.mem (State.addr (fC s₀)) (State.addr (fD s₀)) (fL s₀)
  exact Proof.Modes.CtrFinal.cryptFinal_of (cipher_length _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem final_correct (s : State) (hs : ctrFinalArm.pre s) :
    ∃ t s', Exec isa ctrFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalArm.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp (KPre.of hs)
  exact ⟨t, s', he, hg, final_post h₁ hm⟩

/-! ## Constant time -/

section
variable {s₀ s₀' : State} (hq : ctrFinalArm.pub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_W : fW s₀ = fW s₀' := hq.2.1
theorem pub_r1 : s₀.gpr .r1 = s₀'.gpr .r1 := hq.2.2.1
theorem pub_C : fC s₀ = fC s₀' := hq.2.2.2.1
theorem pub_D : fD s₀ = fD s₀' := hq.2.2.2.2.1
theorem pub_L : stackArg s₀ 0 = stackArg s₀' 0 := hq.2.2.2.2.2.1
theorem pub_V : fV s₀ = fV s₀' := hq.2.2.2.2.2.2
theorem pub_N : fN s₀ = fN s₀' := by rw [fN, fN, fL, fL, pub_L hq]
theorem pub_U : fU s₀ = fU s₀' := by rw [fU, fU, fL, fL, pub_L hq]
theorem pub_T : fT s₀ = fT s₀' := by rw [fT, fT, pub_D hq, pub_N hq]

end

/-- The arguments' area, apart from what may be written. -/
theorem KPre.argsWf {s₀ : State} (hp : KPre s₀) :
    s₀.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 8⟩ r := by
  have e : (⟨State.addr s₀.sp, 8⟩ : Region) = fArg s₀ := by simp [stackArgAddr]
  refine ⟨hp.sp_hi, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.c_arg.symm
  · exact hp.data_arg.symm
  · exact hp.sv_arg.symm

/-- Two states of the runs agree on the taint that makes the registers `rs`
and the stack arguments public. -/
theorem agreeAt {s₀ s₀' : State} (hp : KPre s₀) (hp' : KPre s₀') (hq : ctrFinalArm.pub s₀ s₀') {a b : State}
    (sa : a.sp = s₀.sp) (sb : b.sp = s₀'.sp) (wa : a.wr = s₀.wr) (wb : b.wr = s₀'.wr)
    (ma : Frame (cBig s₀) s₀.mem a.mem) (mb : Frame (cBig s₀') s₀'.mem b.mem) {rs : List Reg}
    (hr : ∀ r ∈ rs, a.gpr r = b.gpr r) : VG.Arm.Taint.Agree (argTaint rs 8) a b := by
  have arg : ∀ {σ s : State}, KPre σ → s.sp = σ.sp → Frame (cBig σ) σ.mem s.mem →
      ∀ k < 2, stackArg s k = stackArg σ k :=
    fun {σ s} hσ hs hm k hk => by
      rw [stackArg, show stackArgAddr s k = stackArgAddr σ k by simp only [stackArgAddr, hs]]
      exact hσ.argMem hm hk
  refine agree_argTaint hr (by rw [sa, sb, pub_sp hq]) (by rw [sa, wa]; exact hp.argsWf)
    (by rw [sb, wb]; exact hp'.argsWf)
    (argMem_of (j := 2) (by rw [sa, sb, pub_sp hq]) (by rw [sa]; exact hp.sp_hi) fun i hi => ?_)
  rw [arg hp sa ma i hi, arg hp' sb mb i hi]
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact pub_L hq
  · exact pub_V hq

theorem setup_taint : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) (.block ctrFinalSetup) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem test_taint : ∃ h, (taint.check (Taint.ofRegs [.r8]) (.block [.cmp .r8 (.imm 0)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (argTaint [.r4, .r5, .r6] 8) (.block ctrTailArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (argTaint [.r7, .r8] 8)
    (.seq (.block ctrXorArgs) (.loop (.block Impl.Modes.Arm.xorByte) .ne)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

theorem end_taint : ∃ h, (taint.check (argTaint [] 8) (.block (ctrSave ++ finalRestore)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalArm.pre s₀) (h0' : ctrFinalArm.pre s₀')
    (hq : ctrFinalArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') ctrFinal fun _ _ => True := by
  have hp := KPre.of h0
  have hp' := KPre.of h0'
  -- The registers saved and the arguments set up.
  have r₁ := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := Setup s₀) (G' := Setup s₀')
    (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agreeAt hp hp' hq rfl rfl rfl rfl (Frame.refl _ _) (Frame.refl _ _) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact pub_W hq
      · exact pub_r1 hq
      · exact pub_C hq
      · exact pub_D hq) setup_taint
    (fun s e => by rw [e]; exact setup_wp hp) (fun s e => by rw [e]; exact setup_wp hp')
  -- The whole blocks.
  have r₂ := rel_wp (F := Setup s₀) (F' := Setup s₀') (G := Whole s₀) (G' := Whole s₀')
    (w_rel fun a b ⟨ha, hb⟩ => ⟨_, _, _, _, _, setup_call hp ha, by
      rw [pub_W hq, pub_r1 hq, pub_C hq, pub_D hq, pub_N hq]; exact setup_call hp' hb,
      by rw [ha.sp, hb.sp, pub_sp hq]⟩)
    (fun _ h => whole_wp hp h) (fun _ h => whole_wp hp' h)
  -- The test.
  have r₃ := rel_agree (F := Whole s₀) (F' := Whole s₀')
    (G := fun s => Whole s₀ s ∧ s.z = decide (fU s₀ = 0)) (G' := fun s => Whole s₀' s ∧ s.z = decide (fU s₀' = 0))
    (Taint.ofRegs [.r8]) (fun a b ha hb => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.r8, hb.r8, pub_U hq]) test_taint
    (fun _ h => test_wp h) (fun _ h => test_wp h)
  -- The partial last block.
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole s₀ a ∧ Whole s₀' b) ctrFinalTail
      fun a b => Done s₀ a ∧ Done s₀' b := by
    have hu' : fU s₀' ≠ 0 := pub_U hq ▸ hu
    have a₁ := rel_agree (F := Whole s₀) (F' := Whole s₀') (G := TArgs s₀) (G' := TArgs s₀')
      (argTaint [.r4, .r5, .r6] 8) (fun a b ha hb => by
        refine agreeAt hp hp' hq ha.sp hb.sp ha.wr hb.wr (big_frame (cW1_cW (whole_cW1 ha)))
          (big_frame (cW1_cW (whole_cW1 hb))) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [ha.r4, hb.r4, pub_W hq]
        · rw [ha.r5, hb.r5, pub_r1 hq]
        · rw [ha.r6, hb.r6, pub_C hq]) tailArgs_taint
      (fun _ h => tail_args_wp hp h) (fun _ h => tail_args_wp hp' h)
    have a₂ := rel_wp (F := TArgs s₀) (F' := TArgs s₀') (G := TCall s₀) (G' := TCall s₀')
      (w_rel fun a b ⟨ha, hb⟩ => ⟨_, _, _, _, _, ha.call, by
        rw [pub_W hq, pub_r1 hq, pub_C hq, cBk32, pub_V hq]; exact hb.call, by rw [ha.sp, hb.sp, pub_sp hq]⟩)
      (fun _ h => WP.mono (w_call h.call) fun _ c => tail_call hp h c)
      (fun _ h => WP.mono (w_call h.call) fun _ c => tail_call hp' h c)
    have a₃ := rel_agree (F := TCall s₀) (F' := TCall s₀') (G := Done s₀) (G' := Done s₀')
      (argTaint [.r7, .r8] 8) (fun a b ha hb => by
        refine agreeAt hp hp' hq ha.sp hb.sp ha.wr hb.wr (big_frame (cW1_cW ha.frame))
          (big_frame (cW1_cW hb.frame)) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.r7, hb.r7, pub_T hq]
        · rw [ha.r8, hb.r8, pub_U hq]) xor_taint
      (fun _ h => tail_xor_wp hp h hu) (fun _ h => tail_xor_wp hp' h hu')
    exact a₁.seq (a₂.seq a₃)
  have ev {s : State} {u : Nat} (h : s.z = decide (u = 0)) : isa.eval .eq s = some (decide (u = 0)) := by
    show VG.Arm.eval .eq s = _; rw [VG.Proof.MdStream.Arm.eval_eq, h]
  have r₄ : RelCT isa (fun a b => (Whole s₀ a ∧ a.z = decide (fU s₀ = 0)) ∧
      (Whole s₀' b ∧ b.z = decide (fU s₀' = 0)))
      (.ite .eq (.block []) ctrFinalTail) (fun a b => Done s₀ a ∧ Done s₀' b) := by
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
    (argTaint [] 8)
    (fun a b ha hb => agreeAt hp hp' hq ha.sp hb.sp ha.wr hb.wr (big_frame ha.frame) (big_frame hb.frame)
      fun r hr => by simp at hr) end_taint
    (fun _ h => WP.mono (end_wp hp h) fun _ _ => trivial)
    (fun _ h => WP.mono (end_wp hp' h) fun _ _ => trivial)
  exact (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem final_ct : ConstantTime isa ctrFinalArm.pre ctrFinalArm.pub ctrFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem ctrFinal_verified : Verified Arm.target ctrFinal ctrFinalScratchContract :=
  Verified.of_correct final_correct final_ct ctrFinal_implies

/-! ## With `save` on the stack

The final function has one stack argument, so `save` is its second: it runs
its code in a frame of 72 bytes (`withStackScratchWiped`): the copy of the
stack argument, `save`'s address, the word holding `lr`, and `save`'s 56
bytes, the block included, which it zeroes before returning (and 4 bytes of
padding). The code's calls use 2912 bytes below it, so 2984 in all. -/

/-- A state satisfying the precondition, without `save`. -/
def ctrFinalFrameSat : State :=
  { ctrFinalSat with rd := [⟨0x1000, 272⟩, ⟨0x8000, 4⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩] }

theorem ctrFinalFrameSat_pre : ∃ s, (Proof.Camellia.ctrFinalContractSk Arm.abi 2984).pre s := by
  implies_sat [Proof.Camellia.ctrFinalContractSk, Spec.Camellia.ctrFinalSig, Spec.Camellia.ctrFinalPre,
    Proof.Camellia.ctrFinalPostSk, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [ctrFinalFrameSat, ctrFinalSat] using ctrFinalFrameSat

/-- `ctrFinal`, with `save` on the stack (zeroed on return). -/
theorem ctrFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 72 1 14 ctrFinal)
      (Spec.Camellia.ctrFinalContract Arm.abi 2984) :=
  Proof.Camellia.ctrFinal_of_sk <|
  Arm.Verified.stackScratchWiped (sig := Spec.Camellia.ctrFinalSig) (nm := "save") (e := .u64) (n := 7)
    (pre := Spec.Camellia.ctrFinalPre Arm.abi.ptrBits) (post := Proof.Camellia.ctrFinalPostSk Arm.abi.ptrBits)
    (wa := true) (stack := 2912) (m := 1) (bytes := 72)
    ctrFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (ctrFinalPre_local _) (ctrFinalPost_local _) (Proof.Camellia.ctrFinalPostOut_local _) ctrFinalFrameSat_pre

end VG.Proof.Camellia.Arm.CtrFinal
