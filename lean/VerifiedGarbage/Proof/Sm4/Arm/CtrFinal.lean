module

public import VerifiedGarbage.Impl.Sm4.Arm.CtrFinal
public import VerifiedGarbage.Proof.Sm4.CtrFinal
public import VerifiedGarbage.Proof.Sm4.Arm.BatchVerified
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.AesCfb.Arm.Final
import VerifiedGarbage.Proof.Modes.CtrFinal
public import VerifiedGarbage.Proof.CmacAes.Arm.Words
import VerifiedGarbage.Proof.Cmac.Block32
import VerifiedGarbage.Proof.AesCbc.Mem32
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Impl.Sm4.Arm.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.CtrFinal
meta import VerifiedGarbage.Proof.Sm4.Arm.BatchVerified
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Spill
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.AesCfb.Arm.Final
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.CmacAes.Arm.Words
meta import VerifiedGarbage.Proof.Cmac.Block32
meta import VerifiedGarbage.Proof.AesCbc.Mem32
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Inline
meta import VerifiedGarbage.Proof.Framework.Arm.CallF
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# SM4-CTR of a message's last piece on ARMv7

`ctrFinal_framed`: `vg_sm4_ctr_final` (`Impl/Sm4/Arm/CtrFinal.lean`) meets
`Spec.Sm4.ctrFinalContract` (`Proof.Sm4.ctrFinalContract_eq`).

The code is proven against `ctrFinalArm`, with a fifth argument `save` of
56 bytes on the stack (`ctrFinal_implies`: the shared contract with it), as a
caller of `vg_sm4_ctr` (framed by its own working space on the stack,
`ctrFramed`), through its contract: what a call needs and leaves (`WCall`,
`WPost`, `w_call`, constant time by `w_rel`). The proof is AES-CTR's
(`Proof/AesCtr/Arm/Final.lean`), with SM4's arguments:

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

namespace VG.Proof.Sm4.Arm.CtrFinal

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Impl.Sm4.Arm (ctrFramed ctrSave ctrFinalMoves ctrFinalSetup ctrCall ctrTailArgs ctrXorArgs ctrFinalTail
  ctrFinal)
open VG.Impl.AesCfb.Arm (finalSaved finalSave finalRestore)
open VG.Proof.AesCfb.Arm (shr4 and15 shl4 blocksAt_frame' preserved_saved)
open VG.Proof.AesGcm.Arm (toNat_ofNat32)
open VG.Arm.FrameStack (armStack belowA)
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_and wp_cmp wp_ldrSp eval_eq
  eval_ne ofNat_beq_zero)
open VG.Proof.Modes.Arm (XPre XInv XDone xorLoop_wp xf add0_32)

/-- The code's contract, with the arguments `(schedule = r0, ctr = r1,
data = r2, len = r3, save = [sp])`, `save` of 56 bytes: the data and the
counter block as `Spec.Ctr.CryptFinal` says, by SM4 with the schedule at
`schedule`. -/
def ctrFinalArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let ctr : Region := ⟨State.addr (s.gpr .r1), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let sv : Region := ⟨State.addr (stackArg s 0), 56⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 1520, 1520⟩
    1520 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      s.rd = [sched, args] ∧ s.wr = [ctr, data, sv] ∧
      sched.Disjoint ctr ∧ sched.Disjoint data ∧ sched.Disjoint sv ∧
      ctr.Disjoint data ∧ ctr.Disjoint sv ∧ ctr.Disjoint args ∧
      data.Disjoint sv ∧ data.Disjoint args ∧ sv.Disjoint args ∧
      stk.Disjoint sched ∧ stk.Disjoint ctr ∧ stk.Disjoint data ∧ stk.Disjoint sv ∧ stk.Disjoint args ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 56 ≤ 2 ^ 32
  post s s' :=
    Spec.Ctr.CryptFinal (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem (State.addr (s.gpr .r0)))) s.mem s'.mem
      (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) (s.gpr .r3).toNat
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- The contract the frame needs: the shared one, with `save`, 56 bytes, as
a fifth argument, and 1520 bytes of stack (`vg_sm4_ctr`'s frame and
calls). -/
abbrev ctrFinalScratchContract : Contract isa :=
  Sig.scratchContract Arm.abi Spec.Sm4.ctrFinalSig "save" .u64 7 (Curry.const (fun _ => True) _)
    (Proof.Sm4.ctrFinalPost Arm.abi.ptrBits) true 1520

/-- A state satisfying the precondition: the schedule at `0x1000`, the
counter block at `0x2000`, no data at `0x3000` and `save` at `0x6000` (the
stack argument at `0x8000`). -/
def ctrFinalSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x60 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x6000, 56⟩]

theorem ctrFinal_implies : ctrFinalArm.Implies ctrFinalScratchContract := by
  sig_implies [ctrFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Sm4.ctrFinalSig, Proof.Sm4.ctrFinalPost, ctrFinalArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [ctrFinalSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using ctrFinalSat

theorem ctr_stack : armStack ctrFramed ≤ 1520 := by decide +kernel

/-! ## A call of `vg_sm4_ctr` -/

/-- The 1520 bytes below the stack pointer `sp`, which a call uses. -/
abbrev stk (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 1520, 1520⟩

theorem belowA_stk {sp : BitVec 32} {n : Nat} (hn : n ≤ 1520) (hsp : 1520 ≤ sp.toNat) :
    Region.Sub (belowA sp n) (stk sp) := by
  simp only [belowA]
  rw [FrameStack.addr_sub' (by omega)]
  have e : State.addr sp - BitVec.ofNat 64 n =
      State.addr sp - BitVec.ofNat 64 1520 + BitVec.ofNat 64 (1520 - n) := by
    have := sp.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [State.addr, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact Offset.sub_base _ (by omega)

/-- What a call of `vg_sm4_ctr` needs: the schedule at `W`, the counter block
at `C` and `n` blocks at `D`, in `r0`–`r3`, and the 1520 bytes below the
stack pointer. -/
structure WCall (s : State) (W C D : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = C
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  hsp : 1520 ≤ s.sp.toNat
  fitW : W.toNat + 128 ≤ 2 ^ 32
  fitC : C.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  wc : (⟨State.addr W, 128⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  wd : (⟨State.addr W, 128⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  cd : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  bw : (stk s.sp).Disjoint ⟨State.addr W, 128⟩
  bc : (stk s.sp).Disjoint ⟨State.addr C, 16⟩
  bd : (stk s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  reads : Covers [⟨State.addr W, 128⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩] s.wr

/-- SM4 with the schedule at `W`. -/
abbrev wCiph (m : Mem) (W : BitVec 32) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt m (State.addr W))

/-- What a call of `vg_sm4_ctr` leaves. -/
structure WPost (s : State) (W C D : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, stk s.sp] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem (State.addr D) n =
    Spec.Ctr.crypt (wCiph s.mem W) (bytesAt s.mem (State.addr C) 16) (Spec.Cbc.blocksAt s.mem (State.addr D) n)
  ctr : bytesAt s'.mem (State.addr C) 16 = Spec.Ctr.next (bytesAt s.mem (State.addr C) 16) n

abbrev wRd (W : BitVec 32) : List Region := [⟨State.addr W, 128⟩]
abbrev wWr (C D : BitVec 32) (n : Nat) : List Region := [⟨State.addr C, 16⟩, ⟨State.addr D, n * 16⟩]

namespace WCall
variable {s : State} {W C D : BitVec 32} {n : Nat} (h : WCall s W C D n)
include h

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem pre : (Spec.Sm4.ctrContract Arm.abi 1520).pre (s.callEntry.withRegions (wRd W) (wWr C D n)) := by
  have hn := toNat_ofNat32 h.n_lt
  sig_pre [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  rw [h.r0, h.r1, h.r2, h.r3, hn, Nat.mul_comm n 16]
  exact ⟨h.hsp, by have := s.sp.isLt; omega, rfl, by unfold wWr; rw [Nat.mul_comm n 16]; rfl, h.wc, h.wd, h.cd,
    h.bw, h.bc, h.bd, h.fitW, h.fitC, h.fitD⟩

theorem cov : Covers (wRd W ++ wWr C D n) (s.rd ++ s.wr) := by
  rw [show wWr C D n = [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩] by rw [Nat.mul_comm]]
  refine VG.Proof.AesGcm.Arm.covers_append' h.reads (fun x n' hi => ?_)
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (wWr C D n) s.wr := by
  rw [show wWr C D n = [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩] by rw [Nat.mul_comm]]
  exact h.writes

end WCall

theorem w_call {s : State} {W C D : BitVec 32} {n : Nat} (h : WCall s W C D n) :
    WP isa ctrCall s (WPost s W C D n) := by
  refine FrameStack.WP.callF (k := Spec.Sm4.ctrContract Arm.abi 1520) Proof.Sm4.Arm.BatchVerified.framed.1
    (rd := wRd W) (wr := wWr C D n) h.pre h.cov h.covW (Nat.le_trans ctr_stack h.hsp) ?_
  intro s' hrd hwr hsp hf hcs hpost
  have hn := toNat_ofNat32 h.n_lt
  sig_post [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpost
  rw [h.r0, h.r1, h.r2, h.r3, hn] at hpost
  obtain ⟨hdata, hctr⟩ := hpost
  refine ⟨hrd, hwr, hsp, hcs, hf.sub fun r hr => ?_, hdata, hctr⟩
  simp only [wWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨⟨State.addr D, 16 * n⟩, by simp, fun _ hx => by rwa [Nat.mul_comm] at hx⟩
  · exact ⟨stk s.sp, by simp, belowA_stk ctr_stack h.hsp⟩

/-- Calls of `vg_sm4_ctr` with the same arguments and stack pointer in both
runs are constant time. -/
theorem w_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W C D : BitVec 32, ∃ n : Nat,
      WCall s₁ W C D n ∧ WCall s₂ W C D n ∧ s₁.sp = s₂.sp) :
    RelCT isa P ctrCall fun _ _ => True := by
  intro a b t₁ t₂ a' b' hp e₁ e₂
  obtain ⟨W, C, D, n, h₁, h₂, hsp⟩ := h _ _ hp
  have hn := toNat_ofNat32 h₁.n_lt
  have r := RelCT.call (k := Spec.Sm4.ctrContract Arm.abi 1520) Proof.Sm4.Arm.BatchVerified.framed.1
    Proof.Sm4.Arm.BatchVerified.framed.2.1 (wRd W) (wWr C D n)
    (P := fun x y => x = a ∧ y = b) (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  · exact ⟨r.1, trivial⟩
  subst ex ey
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.cov, h₁.covW, h₂.cov, h₂.covW⟩
  sig_pub [Spec.Sm4.ctrContract, Spec.Sm4.ctrSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  rw [h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1, h₂.r2, h₂.r3, hsp]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The arguments, by name -/

section
variable (s₀ : State)

abbrev fW : BitVec 32 := s₀.gpr .r0
abbrev fC : BitVec 32 := s₀.gpr .r1
abbrev fD : BitVec 32 := s₀.gpr .r2
abbrev fL : Nat := (s₀.gpr .r3).toNat
abbrev fV : BitVec 32 := stackArg s₀ 0
/-- The number of whole blocks, and of the bytes after them. -/
abbrev fN : Nat := fL s₀ / 16
abbrev fU : Nat := fL s₀ % 16
/-- The data after the whole blocks, as a register holds it and as an
address. -/
abbrev fT : BitVec 32 := fD s₀ + BitVec.ofNat 32 (16 * fN s₀)
abbrev fTa : Addr := State.addr (fD s₀) + BitVec.ofNat 64 (16 * fN s₀)

abbrev fSch : Region := ⟨State.addr (fW s₀), 128⟩
abbrev fCR : Region := ⟨State.addr (fC s₀), 16⟩
abbrev fData : Region := ⟨State.addr (fD s₀), fL s₀⟩
abbrev fBlk : Region := ⟨State.addr (fD s₀), 16 * fN s₀⟩
abbrev fTail : Region := ⟨fTa s₀, fU s₀⟩
abbrev cSv : Region := ⟨State.addr (fV s₀), 56⟩
abbrev fArg : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev fStk : Region := stk s₀.sp

/-- The block in `save`. -/
abbrev cBk32 : BitVec 32 := fV s₀ + 40
abbrev cBk : Addr := State.addr (fV s₀) + BitVec.ofNat 64 40
abbrev cBlk : Region := ⟨cBk s₀, 16⟩

/-- The counter block and the whole blocks on entry, and the cipher. -/
abbrev fT0 : List Byte := bytesAt s₀.mem (State.addr (fC s₀)) 16
abbrev fBlks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (State.addr (fD s₀)) (fN s₀)
abbrev cCiph : Spec.Cbc.Cipher := wCiph s₀.mem (fW s₀)

/-- The memory once the registers are saved. -/
abbrev svMem : Mem := Spill.saveMem s₀.mem (State.addr (fV s₀)) s₀.gpr finalSaved

/-- What the function writes after the save: before the XOR, and in all. -/
abbrev cW1 : List Region := [fCR s₀, fBlk s₀, cBlk s₀, fStk s₀]
abbrev cW : List Region := [fCR s₀, fData s₀, cBlk s₀, fStk s₀]
abbrev cBig : List Region := [fCR s₀, fData s₀, cSv s₀, fStk s₀]

end

/-- The precondition, by name. -/
structure KPre (s₀ : State) : Prop where
  sp_lo : 1520 ≤ s₀.sp.toNat
  sp_hi : s₀.sp.toNat + 4 ≤ 2 ^ 32
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
  sch_fit : (fW s₀).toNat + 128 ≤ 2 ^ 32
  c_fit : (fC s₀).toNat + 16 ≤ 2 ^ 32
  data_fit : (fD s₀).toNat + fL s₀ ≤ 2 ^ 32
  sv_fit : (fV s₀).toNat + 56 ≤ 2 ^ 32

theorem KPre.of {s₀ : State} (h : ctrFinalArm.pre s₀) : KPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22⟩

/-! ## Regions -/

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl
theorem fL_lt (s₀ : State) : fL s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt
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

theorem KPre.arg_in : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 :=
  ⟨fArg s₀, by simp [hp.rd], Region.contains_self _ _⟩

theorem KPre.tail_lt (hu : fU s₀ ≠ 0) : (fD s₀).toNat + 16 * fN s₀ < 2 ^ 32 := by
  have := hp.data_fit; have := Nat.div_add_mod (fL s₀) 16; rw [fN_eq]; rw [fU_eq] at hu; omega

theorem KPre.tailA (hu : fU s₀ ≠ 0) : State.addr (fT s₀) = fTa s₀ := addr_add (hp.tail_lt hu)

theorem KPre.tail_toNat (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.tail_lt hu
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem KPre.bkA : State.addr (cBk32 s₀) = cBk s₀ := addr_add (k := 40) (by have := hp.sv_fit; omega)

theorem KPre.bk_toNat : (cBk32 s₀).toNat = (fV s₀).toNat + 40 := by
  have := hp.sv_fit
  rw [BitVec.toNat_add, show (40 : BitVec 32).toNat = 40 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem KPre.c_blk : (fCR s₀).Disjoint (cBlk s₀) := hp.c_sv.sub_right (blk_sv_sub s₀)

theorem KPre.sch_big : ∀ r ∈ cBig s₀, Region.Disjoint ⟨State.addr (fW s₀), 128⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_c
  · exact hp.sch_data
  · exact hp.sch_sv
  · exact hp.stk_sch.symm

/-- The cipher, from any memory the function leaves. -/
theorem KPre.ciph {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) : wCiph m (fW s₀) = cCiph s₀ := by
  show Spec.Sm4.cipher (Spec.Sm4.scheduleAt m _) = _
  rw [Proof.Sm4.scheduleAt_frame hf hp.sch_big]

/-- The stack argument survives what the function writes. -/
theorem KPre.argMem {m : Mem} (hf : Frame (cBig s₀) s₀.mem m) :
    m.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 := by
  refine hf.readW (r := fArg s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
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

/-! ## Saving the registers -/

/-- What saving the registers and setting up the arguments leaves. -/
structure Setup (s₀ s : State) : Prop where
  r0 : s.gpr .r0 = fW s₀
  r1 : s.gpr .r1 = fC s₀
  r2 : s.gpr .r2 = fD s₀
  r3 : s.gpr .r3 = BitVec.ofNat 32 (fN s₀)
  r4 : s.gpr .r4 = fW s₀
  r6 : s.gpr .r6 = fC s₀
  r7 : s.gpr .r7 = fT s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (fU s₀)
  sp : s.sp = s₀.sp
  mem : s.mem = svMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem moves_eq : ctrFinalMoves =
    [.mov .r4 (.reg .r0), .mov .r6 (.reg .r1), .dp .and .r8 .r3 (.imm 15), .mov .r3 (.shifted .r3 .lsr 4),
     .dp .add .r7 .r2 (.shifted .r3 .lsl 4)] := rfl

theorem setup_wp {s₀ : State} (hp : KPre s₀) : WP isa (.block ctrFinalSetup) s₀ (Setup s₀) := by
  show WP isa (.block (.ldrSp .r12 0 :: (finalSave ++ ctrFinalMoves))) s₀ _
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl hp.arg_in fun s₁ u₁ => ?_
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
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_and (op2_imm (by decide))
    fun s₅ u₅ => wp_mov (op2_lsr (by decide)) fun s₆ u₆ => wp_add (op2_lsl (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have hN : 16 * fN s₀ < 2 ^ 32 := by have := fL_lt s₀; rw [fN_eq]; omega
  have k₄ : ∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r12 → s₄.gpr r = s₀.gpr r := fun r h4 h6 h12 => by
    rw [u₄.other _ h6, u₃.other _ h4, keep₂ _ h12]
  have r3₆ : s₆.gpr .r3 = BitVec.ofNat 32 (fN s₀) := by
    rw [u₆.gpr, u₅.other _ (by decide), k₄ _ (by decide) (by decide) (by decide), shr4]
  exact {
    r0 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      k₄ _ (by decide) (by decide) (by decide)]
    r1 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      k₄ _ (by decide) (by decide) (by decide)]
    r2 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      k₄ _ (by decide) (by decide) (by decide)]
    r3 := by rw [u₇.other _ (by decide), r3₆]
    r4 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, keep₂ _ (by decide)]
    r6 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), keep₂ _ (by decide)]
    r7 := by
      rw [u₇.gpr, u₆.other .r2 (by decide), r3₆, shl4 hN, u₅.other _ (by decide),
        k₄ _ (by decide) (by decide) (by decide)]
    r8 := by
      rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, k₄ _ (by decide) (by decide) (by decide)]
      exact and15 _
    sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂]
    mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, mem₂]
    rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂]
    wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂] }

/-! ## The whole blocks -/

/-- What the call on the whole blocks leaves. -/
structure Whole (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = fW s₀
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
    WCall s (fW s₀) (fC s₀) (fD s₀) (fN s₀) := by
  have hst : stk s.sp = fStk s₀ := by rw [h.sp]
  refine ⟨h.r0, h.r1, h.r2, h.r3, by rw [h.sp]; exact hp.sp_lo, hp.sch_fit, hp.c_fit, hp.blk_fit, hp.sch_c,
    hp.sch_data.sub_right (blk_sub s₀), hp.c_data.sub_right (blk_sub s₀), by rw [hst]; exact hp.stk_sch,
    by rw [hst]; exact hp.stk_c, by rw [hst]; exact hp.stk_data.sub_right (blk_sub s₀), ?_, ?_⟩
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
  have eW : wCiph s.mem (fW s₀) = cCiph s₀ := by rw [h.mem]; exact hp.ciph hp.svFrame
  have eC : bytesAt s.mem (State.addr (fC s₀)) 16 = fT0 s₀ := by
    rw [h.mem]; exact Proof.Cmac.bytesAt_frame (svMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_sv) (by decide)
  have eB : Spec.Cbc.blocksAt s.mem (State.addr (fD s₀)) (fN s₀) = fBlks s₀ := by
    rw [h.mem]; exact blocksAt_frame' (svMem_frame s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (blk_sub s₀))
  have hst : stk s.sp = fStk s₀ := by rw [h.sp]
  refine ⟨by rw [keep .r4 (by simp [preserved]) (by decide), h.r4],
    by rw [keep .r6 (by simp [preserved]) (by decide), h.r6],
    by rw [keep .r7 (by simp [preserved]) (by decide), h.r7],
    by rw [keep .r8 (by simp [preserved]) (by decide), h.r8],
    by rw [w.sp, h.sp], by rw [w.rd, h.rd], by rw [w.wr, h.wr], ?_, ?_, ?_⟩
  · rw [← h.mem]; have f := w.frame; rw [hst] at f; exact f
  · rw [w.out, eW, eC, eB]
  · rw [w.ctr, eC]

theorem Whole.of_fupd {s₀ s s' : State} (h : Whole s₀ s) (g : s'.gpr = s.gpr) (m : s'.mem = s.mem)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (sp : s'.sp = s.sp) : Whole s₀ s' :=
  ⟨by rw [g, h.r4], by rw [g, h.r6], by rw [g, h.r7], by rw [g, h.r8], by rw [sp, h.sp], by rw [rd, h.rd],
    by rw [wr, h.wr], by rw [m]; exact h.frame, by rw [m]; exact h.blocks, by rw [m]; exact h.ctr⟩

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
  call : WCall s (fW s₀) (fC s₀) (cBk32 s₀) 1
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

theorem tailArgs_eq : ctrTailArgs = .ldrSp .r12 0 :: .mov .r0 (.imm 0) :: (Proof.CmacAes.Arm.zeroBlk .r0 .r12 40 ++
    ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r6), .dp .add .r2 .r12 (.imm 40), .mov .r3 (.imm 1)] : List Instr)) := rfl

theorem tail_args_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : Whole s₀ s) :
    WP isa (.block ctrTailArgs) s (TArgs s₀) := by
  rw [tailArgs_eq]
  have f1 := whole_cW1 h
  have big := big_frame (cW1_cW f1)
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [h.sp]; rfl)
    (by rw [h.rd, h.wr]; exact hp.arg_in) fun s₁ u₁ => ?_
  have r12₁ : s₁.gpr .r12 = fV s₀ := by rw [u₁.gpr]; exact hp.argMem big
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
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .r0 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h0 h12 => by
    rw [g₃, u₂.other _ h0, u₁.other _ h12]
  have mem₇ : s₇.mem = Proof.Cmac.zero4 s.mem (cBk s₀) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.mem, u₁.mem]
  have sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, u₁.sp, h.sp]
  have rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, h.wr]
  have zf : Frame [cBlk s₀] s.mem (Proof.Cmac.zero4 s.mem (cBk s₀)) := AesCbc.zero4_frame _ _
  have hst : stk s₇.sp = fStk s₀ := by rw [sp₇]
  have bkA := hp.bkA
  have hbk := hp.bk_toNat
  refine ⟨⟨?_, ?_, ?_, by rw [u₇.gpr]; rfl, by rw [sp₇]; exact hp.sp_lo, hp.sch_fit, hp.c_fit,
    by rw [hbk]; omega, hp.sch_c, ?_, ?_, by rw [hst]; exact hp.stk_sch, by rw [hst]; exact hp.stk_c, ?_, ?_, ?_⟩,
    ?_, ?_, sp₇, rd₇, wr₇, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g₂ _ (by decide) (by decide), h.r4]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      g₂ _ (by decide) (by decide), h.r6]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃,
      u₂.other _ (by decide), r12₁]
  · rw [bkA, Nat.mul_one]; exact hp.sch_sv.sub_right (blk_sv_sub s₀)
  · rw [bkA, Nat.mul_one]; exact hp.c_blk
  · rw [hst, bkA, Nat.mul_one]; exact hp.stk_sv.sub_right (blk_sv_sub s₀)
  · rw [rd₇, wr₇, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₇, hp.wr, bkA, Nat.mul_one]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fCR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 40, rfl, by simp⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g₂ _ (by decide) (by decide), h.r7]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g₂ _ (by decide) (by decide), h.r8]
  · rw [mem₇]
    exact f1.trans (zf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [mem₇, blocksAt_frame' zf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)), h.blocks]
  · rw [mem₇, Proof.Cmac.bytesAt_frame zf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_blk) (by decide), h.ctr]
  · rw [mem₇, Proof.Cmac.zero4_bytes]; rfl
  · rw [mem₇]
    have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; have := fU_lt s₀; omega
    rw [zf.bytes (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)) hlen hq,
      f1.bytes hp.tail_cW1 hlen hq,
      (svMem_frame s₀).bytes (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (tail_sub s₀)) hlen hq]

theorem cipher_length (sk : Spec.Sm4.Schedule) (b : List Byte) : (Spec.Sm4.cipher sk b).length = 16 := by
  simp [Spec.Sm4.cipher]

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
    (w : WPost s (fW s₀) (fC s₀) (cBk32 s₀) 1 s') : TCall s₀ s' := by
  have keep : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r := w.saved
  have hst : stk s.sp = fStk s₀ := by rw [h.sp]
  have fw : Frame [fCR s₀, cBlk s₀, fStk s₀] s.mem s'.mem := by
    have f := w.frame; rw [hst, hp.bkA, Nat.mul_one] at f; exact f
  have big := big_frame (cW1_cW h.frame)
  have eW : wCiph s.mem (fW s₀) = cCiph s₀ := hp.ciph big
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

theorem xorArgs_eq : ctrXorArgs = [.ldrSp .r12 0, .dp .add .r0 .r12 (.imm 40), .mov .r6 (.reg .r7),
    .mov .r7 (.reg .r8)] := rfl

theorem tail_xor_wp {s₀ : State} (hp : KPre s₀) {s : State} (h : TCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block ctrXorArgs) (.loop (.block Impl.Modes.Arm.xorByte) .ne)) s (Done s₀) := by
  have big := big_frame (cW1_cW h.frame)
  rw [xorArgs_eq]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [h.sp]; rfl)
    (by rw [h.rd, h.wr]; exact hp.arg_in) fun s₁ u₁ => ?_)
  have r12₁ : s₁.gpr .r12 = fV s₀ := by rw [u₁.gpr]; exact hp.argMem big
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
    pos := by omega
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
  show WP isa (.block (.ldrSp .r12 0 :: finalRestore)) s _
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [h.sp]; rfl)
    (by rw [h.rd, h.wr]; exact hp.arg_in) fun s₁ u₁ => ?_
  have big := big_frame h.frame
  have r12 : s₁.gpr .r12 = fV s₀ := by rw [u₁.gpr]; exact hp.argMem big
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
theorem pub_C : fC s₀ = fC s₀' := hq.2.2.1
theorem pub_D : fD s₀ = fD s₀' := hq.2.2.2.1
theorem pub_r3 : s₀.gpr .r3 = s₀'.gpr .r3 := hq.2.2.2.2.1
theorem pub_V : fV s₀ = fV s₀' := hq.2.2.2.2.2
theorem pub_N : fN s₀ = fN s₀' := by rw [fN, fN, fL, fL, pub_r3 hq]
theorem pub_U : fU s₀ = fU s₀' := by rw [fU, fU, fL, fL, pub_r3 hq]
theorem pub_T : fT s₀ = fT s₀' := by rw [fT, fT, pub_D hq, pub_N hq]

end

/-- The argument's area, apart from what may be written. -/
theorem KPre.argsWf {s₀ : State} (hp : KPre s₀) :
    s₀.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 4⟩ r := by
  have e : (⟨State.addr s₀.sp, 4⟩ : Region) = fArg s₀ := by simp [stackArgAddr]
  refine ⟨hp.sp_hi, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.c_arg.symm
  · exact hp.data_arg.symm
  · exact hp.sv_arg.symm

/-- Two states of the runs agree on the taint that makes the registers `rs`
and the stack argument public. -/
theorem agreeAt {s₀ s₀' : State} (hp : KPre s₀) (hp' : KPre s₀') (hq : ctrFinalArm.pub s₀ s₀') {a b : State}
    (sa : a.sp = s₀.sp) (sb : b.sp = s₀'.sp) (wa : a.wr = s₀.wr) (wb : b.wr = s₀'.wr)
    (ma : Frame (cBig s₀) s₀.mem a.mem) (mb : Frame (cBig s₀') s₀'.mem b.mem) {rs : List Reg}
    (hr : ∀ r ∈ rs, a.gpr r = b.gpr r) : VG.Arm.Taint.Agree (argTaint rs 4) a b := by
  have arg : ∀ {σ s : State}, KPre σ → s.sp = σ.sp → Frame (cBig σ) σ.mem s.mem → stackArg s 0 = stackArg σ 0 :=
    fun {σ s} hσ hs hm => by
      rw [stackArg, show stackArgAddr s 0 = stackArgAddr σ 0 by simp only [stackArgAddr, hs]]
      exact hσ.argMem hm
  refine agree_argTaint hr (by rw [sa, sb, pub_sp hq]) (by rw [sa, wa]; exact hp.argsWf)
    (by rw [sb, wb]; exact hp'.argsWf)
    (argMem_of (j := 1) (by rw [sa, sb, pub_sp hq]) (by rw [sa]; exact hp.sp_hi) fun i hi => ?_)
  obtain rfl : i = 0 := by omega
  rw [arg hp sa ma, arg hp' sb mb]
  exact pub_V hq

theorem setup_taint : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 4) (.block ctrFinalSetup) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem test_taint : ∃ h, (taint.check (Taint.ofRegs [.r8]) (.block [.cmp .r8 (.imm 0)]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (argTaint [.r4, .r6] 4) (.block ctrTailArgs) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (argTaint [.r7, .r8] 4)
    (.seq (.block ctrXorArgs) (.loop (.block Impl.Modes.Arm.xorByte) .ne)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true := ⟨_, by taint_decide⟩

theorem end_taint : ∃ h, (taint.check (argTaint [] 4) (.block (ctrSave ++ finalRestore)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalArm.pre s₀) (h0' : ctrFinalArm.pre s₀')
    (hq : ctrFinalArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') ctrFinal fun _ _ => True := by
  have hp := KPre.of h0
  have hp' := KPre.of h0'
  -- The registers saved and the arguments set up.
  have r₁ := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := Setup s₀) (G' := Setup s₀')
    (argTaint [.r0, .r1, .r2, .r3] 4)
    (fun s s' e e' => by
      subst e e'
      refine agreeAt hp hp' hq rfl rfl rfl rfl (Frame.refl _ _) (Frame.refl _ _) fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact pub_W hq
      · exact pub_C hq
      · exact pub_D hq
      · exact pub_r3 hq) setup_taint
    (fun s e => by rw [e]; exact setup_wp hp) (fun s e => by rw [e]; exact setup_wp hp')
  -- The whole blocks.
  have r₂ := rel_wp (F := Setup s₀) (F' := Setup s₀') (G := Whole s₀) (G' := Whole s₀')
    (w_rel fun a b ⟨ha, hb⟩ => ⟨_, _, _, _, setup_call hp ha, by
      rw [pub_W hq, pub_C hq, pub_D hq, pub_N hq]; exact setup_call hp' hb,
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
      (argTaint [.r4, .r6] 4) (fun a b ha hb => by
        refine agreeAt hp hp' hq ha.sp hb.sp ha.wr hb.wr (big_frame (cW1_cW (whole_cW1 ha)))
          (big_frame (cW1_cW (whole_cW1 hb))) fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ha.r4, hb.r4, pub_W hq]
        · rw [ha.r6, hb.r6, pub_C hq]) tailArgs_taint
      (fun _ h => tail_args_wp hp h) (fun _ h => tail_args_wp hp' h)
    have a₂ := rel_wp (F := TArgs s₀) (F' := TArgs s₀') (G := TCall s₀) (G' := TCall s₀')
      (w_rel fun a b ⟨ha, hb⟩ => ⟨_, _, _, _, ha.call, by
        rw [pub_W hq, pub_C hq, cBk32, pub_V hq]; exact hb.call, by rw [ha.sp, hb.sp, pub_sp hq]⟩)
      (fun _ h => WP.mono (w_call h.call) fun _ c => tail_call hp h c)
      (fun _ h => WP.mono (w_call h.call) fun _ c => tail_call hp' h c)
    have a₃ := rel_agree (F := TCall s₀) (F' := TCall s₀') (G := Done s₀) (G' := Done s₀')
      (argTaint [.r7, .r8] 4) (fun a b ha hb => by
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
    (argTaint [] 4)
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

The final function has no stack arguments, so `save` is its first: it runs
its code in a frame of 64 bytes (`withStackScratchWiped`): `save`'s address,
the word holding `lr`, and `save`'s 56 bytes, the block included, which it
zeroes before returning. The code's calls use 1520 bytes below it, so 1584
in all. -/

private theorem bytesAt_congr' {m₁ m₂ : Mem} {p : Addr} {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    bytesAt m₂ p k = bytesAt m₁ p k := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem agree_of' {m₁ m₂ : Mem} {p : Addr} {n : Nat} (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

/-- `Proof.Sm4.ctrFinalPost` reads the memory on entry only within the
buffers. -/
theorem ctrFinalPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Sm4.ctrFinalSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Sm4.ctrFinalSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Sm4.ctrFinalSig.words pb) (Proof.Sm4.ctrFinalPost pb) vs m₁ m' r →
      Curry.apply (Spec.Sm4.ctrFinalSig.words pb) (Proof.Sm4.ctrFinalPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [k, ctr, data, len], _ =>
    simp only [Spec.Sm4.ctrFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of' hb.1
    have hc := agree_of' hb.2.1
    have hd := agree_of' hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (Proof.Sm4.ctrFinalPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (Proof.Sm4.ctrFinalPost pb) _ m₂ m' r
    dsimp only [Curry.apply, Proof.Sm4.ctrFinalPost, ArgWord.ofRaw, Spec.Ctr.CryptFinal] at h ⊢
    have := Nat.mod_le len.toNat (2 ^ pb)
    rw [Proof.Sm4.scheduleAt_congr hk, bytesAt_congr' fun i hi => hd i (by rw [BitVec.toNat_setWidth] at hi; omega),
      bytesAt_congr' hc]
    exact h

/-- A state satisfying the precondition, without `save`. -/
def ctrFinalFrameSat : State := { ctrFinalSat with rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩] }

theorem ctrFinalFrameSat_pre :
    ∃ s, (Spec.Sm4.ctrFinalSig.contract Arm.abi (post := Proof.Sm4.ctrFinalPost Arm.abi.ptrBits)
      (writeArgs := true) (stack := 1584)).pre s := by
  implies_sat [Spec.Sm4.ctrFinalSig, Proof.Sm4.ctrFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [ctrFinalFrameSat, ctrFinalSat] using ctrFinalFrameSat

/-- `ctrFinal`, with `save` on the stack (zeroed on return). -/
theorem ctrFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 64 0 14 ctrFinal)
      (Spec.Sm4.ctrFinalContract Arm.abi 1584) := by
  rw [Proof.Sm4.ctrFinalContract_eq]
  exact Arm.Verified.stackScratchWiped (sig := Spec.Sm4.ctrFinalSig) (nm := "save") (e := .u64) (n := 7)
    (post := Proof.Sm4.ctrFinalPost Arm.abi.ptrBits) (wa := true) (stack := 1520) (m := 0) (bytes := 64)
    ctrFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (ctrFinalPost_local _)
    (Proof.Sm4.ctrFinalPostOut_local _) ctrFinalFrameSat_pre

end VG.Proof.Sm4.Arm.CtrFinal
