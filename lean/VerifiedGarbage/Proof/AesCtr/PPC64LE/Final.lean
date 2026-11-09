module

public import VerifiedGarbage.Impl.AesCtr.PPC64LE.Final
public import VerifiedGarbage.Proof.AesCtr.Final
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCtr.PPC64LE.CT
public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Impl.AesCtr.PPC64LE.Final
meta import VerifiedGarbage.Proof.AesCtr.Final
meta import VerifiedGarbage.Proof.AesCtr.PPC64LE.Verified
meta import VerifiedGarbage.Proof.AesCtr.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCfb.PPC64LE.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.AesCtr.PPC64LE.Call
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT

/-!
# AES-CTR of a message's last piece on PPC64LE

`cryptFinal_framed`: `vg_aes_ctr_final` (`Impl/AesCtr/PPC64LE/Final.lean`)
meets `Proof.AesCtr.finalRoundsContract`, from which the shared contract
follows (`Proof.AesCtr.final_keyed`).

The code is proven against `ctrFinalPPC64LE`, with a seventh argument `save`
(`r9`) of 80 bytes, for its return address and its caller's registers and a
block of its own (`final_implies`: the shared contract with it,
`finalScratchContract`), as a caller of the whole-block function, through its
contract (`modePPC64LE ctrMode`, with `ctrPub`). It shares AES-CFB's final
functions' setup (`Proof/AesCfb/PPC64LE/Final.lean`: `Setup`, `Whole`):

* `final_setup_wp`, `whole_wp`: the registers saved, and the whole-block
  function on the `n = len / 16` whole blocks (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, the block after the
  registers in `save` zeroed and the whole-block function on it
  (`tail_args_wp`, `tail_call_wp`), which leaves `CIPH_K(Tₙ₊₁)` there and
  `Tₙ₊₂` in `ctr`, and its first `u` bytes XORed into them
  (`Modes.PPC64LE.tailLoop_wp`, `tail_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers and the return address restored;
* `final_post`: `Done` gives `Spec.Ctr.CryptFinal`
  (`Proof.Modes.CtrFinal.cryptFinal_of`).

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
the whole-block function's constant time, whose public data, the last 32
bits of the counter block, agree in both runs at both calls: they do on
entry (the contract's leak), and after `n` blocks they are those on entry
plus `n` modulo `2³²`.
-/

@[expose] public section

namespace VG.Proof.AesCtr.PPC64LE.Final

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesCtr.PPC64LE (zeroSlots tailMoves tailArgs tailKey wholeCall finalTail cryptFinal crypt)
open VG.Impl.AesCfb.PPC64LE (finalSaved finalSetup finalRestore)
open VG.Proof.AesCfb.PPC64LE.Final (fW fR fIv fD fL fS fV fN fU fT fSch fIvR fData fBlk fTail fScr fSv
  fWk fIv0 fBlks saveG svMem Setup Whole Kept vars finalSat finalFrameSat moves_wp shr4 shr4_shl4 sub_shl4
  toNat_n eval_u bytesAt_getD blocksAt_frame' svMem_frame saved_slots saved_fits blk_sub tail_sub fN_eq
  fU_eq n_lt u_lt preserved_ne_r0 upd_gpr r4_ofNat restore_eq)
open VG.Proof.AesCbc (Mode)
open VG.Proof.AesCbc.PPC64LE (modePPC64LE callEntry_gpr' taintRegs wp_sp)

/-! ## The contract -/

/-- The code's contract, with the arguments `(schedule = r3, rounds = r4,
ctr = r5, data = r6, len = r7, scratch = r8, save = r9)`, `save` of 80
bytes: the data and the counter block as `Spec.Ctr.CryptFinal` says, by AES
with the key schedule it is given; the counter block's last four bytes are
public. -/
def ctrFinalPPC64LE : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let iv : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 2176⟩
    let sv : Region := ⟨s.gpr .r9, 80⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr, sv] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint sv ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint sv ∧
      data.Disjoint scr ∧ data.Disjoint sv ∧ scr.Disjoint sv ∧
      (s.gpr .r3).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 2176 ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 80 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    Spec.Ctr.CryptFinal (ciphAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) s.mem s'.mem (s.gpr .r5) (s.gpr .r6)
      (s.gpr .r7).toNat
  pub s₁ s₂ :=
    (s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.sp = s₂.sp) ∧
      Spec.Ctr.ctrLeak s₁.mem (s₁.gpr .r5) = Spec.Ctr.ctrLeak s₂.mem (s₂.gpr .r5)

/-- The contract the frame needs: the shared one, with `save`, 80 bytes, as
a seventh argument, and no stack (a call stores nothing in memory). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract PPC64LE.abi Spec.Ctr.aesFinalSig "save" .u64 10 (finalPre PPC64LE.abi.ptrBits)
    (finalPost PPC64LE.abi.ptrBits) false 0 (some (finalLeak PPC64LE.abi.ptrBits))

/-- A state satisfying the precondition. -/
def ctrSat : State := { finalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 80⟩] }

theorem final_implies : ctrFinalPPC64LE.Implies finalScratchContract := by
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, Spec.Ctr.ctrLeak, ctrFinalPPC64LE, PPC64LE.abi,
    PPC64LE.argRegs] [ctrSat, finalSat] using ctrSat

/-! ## The arguments, by name -/

section
variable (s₀ : State)

/-- `save`, the registers then the block. -/
abbrev cSv : Region := ⟨fV s₀, 80⟩
/-- The block after the registers in `save`. -/
abbrev cBk : Addr := fV s₀ + BitVec.ofNat 64 64
abbrev cBlk : Region := ⟨cBk s₀, 16⟩

end

/-- The precondition, by name. -/
structure CPre (s₀ : State) : Prop where
  rd : s₀.rd = [fSch s₀]
  wr : s₀.wr = [fIvR s₀, fData s₀, fScr s₀, cSv s₀]
  sch_iv : (fSch s₀).Disjoint (fIvR s₀)
  sch_data : (fSch s₀).Disjoint (fData s₀)
  sch_scr : (fSch s₀).Disjoint (fScr s₀)
  sch_sv : (fSch s₀).Disjoint (cSv s₀)
  iv_data : (fIvR s₀).Disjoint (fData s₀)
  iv_scr : (fIvR s₀).Disjoint (fScr s₀)
  iv_sv : (fIvR s₀).Disjoint (cSv s₀)
  data_scr : (fData s₀).Disjoint (fScr s₀)
  data_sv : (fData s₀).Disjoint (cSv s₀)
  scr_sv : (fScr s₀).Disjoint (cSv s₀)
  iv_wrap : (fIv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (fD s₀).toNat + fL s₀ ≤ 2 ^ 64
  scr_wrap : (fS s₀).toNat + 2176 ≤ 2 ^ 64
  sv_wrap : (fV s₀).toNat + 80 ≤ 2 ^ 64
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem CPre.of {s₀ : State} (h : ctrFinalPPC64LE.pre s₀) : CPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, _, a14, a15, a16, a17, a18⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a14, a15, a16, a17, a18⟩

/-! ## Regions -/

theorem sv64_sub (s₀ : State) : Region.Sub (fSv s₀) (cSv s₀) := Region.sub_prefix (by decide)
theorem blk_sv_sub (s₀ : State) : Region.Sub (cBlk s₀) (cSv s₀) := Offset.sub_base _ (by decide)

section
variable {s₀ : State} (hp : CPre s₀)
include hp

theorem CPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [fN_eq, fU_eq]; omega)

theorem CPre.blk_wrap : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := Nat.mul_div_le (fL s₀) 16; rw [fN_eq]; omega

theorem CPre.sched_sub : Region.Sub ⟨fW s₀, 16 * (fR s₀ + 1)⟩ (fSch s₀) :=
  Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)

theorem CPre.sched_len : 16 * (fR s₀ + 1) ≤ 2 ^ 64 := by
  rcases hp.rounds with h | h | h <;> omega

end

/-- The save changes only `save`. -/
theorem svMem_frame' (s₀ : State) : Frame [cSv s₀] s₀.mem (svMem s₀) :=
  (svMem_frame s₀).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨cSv s₀, by simp, sv64_sub s₀⟩

/-- The slots of the registers miss the block. -/
theorem slot_blk (s₀ : State) :
    ∀ p ∈ finalSaved, Region.Disjoint ⟨fV s₀ + BitVec.ofNat 64 p.2, 8⟩ (cBlk s₀) := by
  intro p hp'
  have := saved_slots p hp'
  exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)

/-! ## Saving the registers, and the whole blocks -/

theorem final_setup_wp {s₀ : State} (hp : CPre s₀) : WP isa (.block finalSetup) s₀ (Setup s₀) := by
  show WP isa (.block (.mflr .r0 :: (Spill.saveCode .r9 finalSaved ++ Impl.AesCfb.PPC64LE.finalMoves))) _ _
  refine WP.cons exec_mflr (Spill.save_ok (b := .r9) (l := finalSaved) (by decide) saved_fits
    (fun p hp' => ?_) ?_)
  · show InRegions s₀.wr (fV s₀ + BitVec.ofNat 64 p.2) 8
    rw [hp.wr]
    have := saved_slots p hp'
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
  refine moves_wp fun s' r14 r15 r16 r19 r20 r31 r30 r7 keep mem rd wr => ?_
  have g₀ (r : Reg) (hr : r ≠ .r0) : (s₀.write .r0 s₀.lr).gpr r = s₀.gpr r := by
    simp [State.write, hr]
  have k (r : Reg) (h₁ : r ≠ .r14) (h₂ : r ≠ .r15) (h₃ : r ≠ .r16) (h₄ : r ≠ .r19) (h₅ : r ≠ .r20)
      (h₆ : r ≠ .r10) (h₇ : r ≠ .r11) (h₈ : r ≠ .r31) (h₉ : r ≠ .r30) (h₁₀ : r ≠ .r7) (h₀ : r ≠ .r0) :
      s'.gpr r = s₀.gpr r := (keep r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀).trans (g₀ r h₀)
  exact {
    r14 := r14.trans (g₀ .r3 (by decide))
    r15 := r15.trans (g₀ .r4 (by decide))
    r16 := r16.trans (g₀ .r5 (by decide))
    r19 := r19.trans (g₀ .r8 (by decide))
    r20 := r20.trans (g₀ .r9 (by decide))
    r30 := by rw [r30, g₀ .r7 (by decide), shr4_shl4, sub_shl4]
    r31 := by rw [r31, g₀ .r6 (by decide), g₀ .r7 (by decide), shr4_shl4]
    r3 := k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    r4 := k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    r5 := k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    r6 := k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    r7 := by rw [r7, g₀ .r7 (by decide), shr4]
    r8 := k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
    kept := fun r hr hv => by
      obtain ⟨h7, -, -, h10, h11, h14, h15, h16, h19, h20, h30, h31⟩ := Proof.AesCfb.PPC64LE.Final.preserved_ne' hr hv
      exact k r h14 h15 h16 h19 h20 h10 h11 h31 h30 h7 (preserved_ne_r0 r hr)
    mem := mem
    rd := rd
    wr := wr }

theorem crypt_noFrames : crypt.noFrames = true := by
  simp only [crypt, Impl.AesCbc.PPC64LE.whole, Impl.AesCtr.PPC64LE.body, Impl.AesCtr.PPC64LE.ctrCall,
    Code.noFrames, Bool.true_and, Bool.and_true]
  exact Proof.AesCtr.PPC64LE.ctr32_noFrames

/-- The whole-block function's contract: `modePPC64LE ctrMode`, with the
last 32 bits of the counter block public. -/
abbrev wholeK : Contract isa := { modePPC64LE AesCtr.ctrMode with pub := ctrPub }

theorem whole_pre {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    wholeK.pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, fBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, fBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, fBlk s₀, fScr s₀] s.wr := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [modePPC64LE, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r8 ∉ linkRegs),
      h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, toNat_n]
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_data.sub_right (blk_sub s₀), hp.sch_scr,
      hp.iv_data.sub_right (blk_sub s₀), hp.iv_scr, hp.data_scr.sub_left (blk_sub s₀),
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

/-- The schedule, the counter block and the whole blocks once the registers
are saved, as on entry. -/
theorem sv_bytes {s₀ : State} (hp : CPre s₀) :
    bytesAt (svMem s₀) (fW s₀) (16 * (fR s₀ + 1)) = fWk s₀ ∧ bytesAt (svMem s₀) (fIv s₀) 16 = fIv0 s₀ ∧
      Spec.Cbc.blocksAt (svMem s₀) (fD s₀) (fN s₀) = fBlks s₀ := by
  have ef := svMem_frame' s₀
  exact ⟨Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.sch_sv.sub_left hp.sched_sub) hp.sched_len,
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv) (by decide),
    blocksAt_frame' ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (blk_sub s₀))⟩

theorem whole_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    WP isa wholeCall s (Whole AesCtr.ctrMode s₀) := by
  obtain ⟨eW, eIv, eB⟩ := sv_bytes hp
  obtain ⟨hpre, hc, hw⟩ := whole_pre hp h
  refine WP.call (k := wholeK) crypt_correct (rd := [fSch s₀]) (wr := [fIvR s₀, fBlk s₀, fScr s₀]) hpre
    hc hw ?_ crypt_noFrames
  intro s' rd' wr' _ fr' cs' _ post₂
  rw [h.mem] at fr'
  simp only [modePPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7,
    toNat_n, h.mem, eW, eIv, eB] at post₂
  exact ⟨by rw [cs' .r14 (by decide), h.r14], by rw [cs' .r15 (by decide), h.r15],
    by rw [cs' .r16 (by decide), h.r16], by rw [cs' .r19 (by decide), h.r19],
    by rw [cs' .r20 (by decide), h.r20], by rw [cs' .r30 (by decide), h.r30],
    by rw [cs' .r31 (by decide), h.r31],
    fun r hr hv => by rw [cs' r hr, h.kept r hr hv],
    by rw [rd', h.rd], by rw [wr', h.wr], fr', post₂.1, post₂.2⟩

/-! ## The partial last block: its arguments -/

/-- Two zeroed doublewords make 16 zero bytes. -/
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

/-- The arguments of the whole-block function on the block. -/
theorem tailMoves_wp {s : State} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r3 = s.gpr .r14 → s'.gpr .r4 = s.gpr .r15 → s'.gpr .r5 = s.gpr .r16 →
      s'.gpr .r6 = s.gpr .r20 + BitVec.ofNat 64 64 → s'.gpr .r7 = BitVec.ofNat 64 1 →
      s'.gpr .r8 = s.gpr .r19 →
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block tailMoves) s Φ := by
  unfold tailMoves Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_addi (by decide) (by decide) fun s₄ u₄ =>
    wp_li (by decide) fun s₅ u₅ => wp_mr fun s₆ u₆ => wp_nil ?_
  refine k s₆ ?_ ?_ ?_ ?_ ?_ ?_ (fun r h₃ h₄ h₅ h₆ h₇ h₈ => ?_) ?_ ?_ ?_
  all_goals try (simp only [upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁,
    reduceCtorEq, ↓reduceIte]; done)
  · simp only [upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, h₃, h₄, h₅, h₆, h₇,
      h₈, ↓reduceIte]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## Frames -/

section
variable (s₀ : State)

/-- What the function writes after saving the registers, with the whole
blocks rather than the data. -/
abbrev cW1 : List Region := [fIvR s₀, fBlk s₀, fScr s₀, cBlk s₀]
/-- What the function writes after saving the registers. -/
abbrev cW : List Region := [fIvR s₀, fData s₀, fScr s₀, cBlk s₀]
/-- What the function writes. -/
abbrev cBig : List Region := [fIvR s₀, fData s₀, fScr s₀, cSv s₀]

end

theorem cW1_cW {s₀ : State} {m : Mem} (hf : Frame (cW1 s₀) (svMem s₀) m) : Frame (cW s₀) (svMem s₀) m :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem whole_cW1 {M : Mode} {s₀ s : State} (h : Whole M s₀ s) : Frame (cW1 s₀) (svMem s₀) s.mem :=
  h.frame.mono fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp [h]

theorem big_of {s₀ : State} {m : Mem} (hf : Frame (cW s₀) (svMem s₀) m) : Frame (cBig s₀) s₀.mem m :=
  ((svMem_frame' s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨cSv s₀, by simp, blk_sv_sub s₀⟩)

theorem CPre.sched_big {s₀ : State} (hp : CPre s₀) :
    ∀ r ∈ cBig s₀, (⟨fW s₀, 16 * (fR s₀ + 1)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left hp.sched_sub
  · exact hp.sch_data.sub_left hp.sched_sub
  · exact hp.sch_scr.sub_left hp.sched_sub
  · exact hp.sch_sv.sub_left hp.sched_sub

/-! ## The partial last block -/

/-- What zeroing the block and setting up the arguments leaves. -/
structure TArgs (s₀ s : State) : Prop where
  r3 : s.gpr .r3 = fW s₀
  r4 : s.gpr .r4 = s₀.gpr .r4
  r5 : s.gpr .r5 = fIv s₀
  r6 : s.gpr .r6 = cBk s₀
  r7 : s.gpr .r7 = BitVec.ofNat 64 1
  r8 : s.gpr .r8 = fS s₀
  r20 : s.gpr .r20 = fV s₀
  r30 : s.gpr .r30 = BitVec.ofNat 64 (fU s₀)
  r31 : s.gpr .r31 = fT s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (fN s₀)
  zero : bytesAt s.mem (cBk s₀) 16 = List.replicate 16 0

theorem zero_frame (s₀ : State) (m : Mem) (g : Reg → BitVec 64) :
    Frame [cBlk s₀] m (Spill.saveMem m (fV s₀) g zeroSlots) :=
  Spill.saveMem_frame (lo := 64) (n := 16) (fun p hp' => by
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> decide) (by decide) m _ g

theorem preserved_ne_args {r : Reg} (hr : r ∈ preserved) :
    r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 := by
  revert hr; cases r <;> decide

theorem tail_args_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.block tailArgs) s (TArgs s₀) := by
  have f₁ := whole_cW1 h
  show WP isa (.block (.li .r9 0 :: (Spill.saveCode .r20 zeroSlots ++ tailMoves))) _ _
  refine wp_li (by decide) fun s₁ u₁ => ?_
  have h20 : s₁.gpr .r20 = fV s₀ := by rw [u₁.other _ (by decide), h.r20]
  have hw : ∀ p ∈ zeroSlots, InRegions s₁.wr (s₁.gpr .r20 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [u₁.wr, h.wr, hp.wr, h20]
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨cSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega)⟩
    · exact ⟨cSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega)⟩
  refine Spill.save_ok (by decide) (by decide) hw ?_
  refine tailMoves_wp fun s' r3 r4 r5 r6 r7 r8 o mem rd wr => ?_
  have c (r : Reg) (hr : r ∈ preserved) : s'.gpr r = s.gpr r := by
    obtain ⟨h3, h4, h5, h6, h7, h8, h9⟩ := preserved_ne_args hr
    rw [o r h3 h4 h5 h6 h7 h8]
    exact u₁.other r h9
  have hm : s'.mem = Spill.saveMem s.mem (fV s₀) s₁.gpr zeroSlots := by
    rw [mem]; show Spill.saveMem s₁.mem _ _ _ = _; rw [u₁.mem, h20]
  have fz : Frame [cBlk s₀] s.mem s'.mem := by rw [hm]; exact zero_frame s₀ _ _
  have ivZ : ∀ r ∈ [cBlk s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  have blkZ : ∀ r ∈ [cBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  have g₁ (r : Reg) (hr : r ≠ .r9) : s₁.gpr r = s.gpr r := u₁.other r hr
  refine ⟨by rw [r3, show ({ s₁ with mem := _ } : State).gpr = s₁.gpr from rfl, g₁ _ (by decide), h.r14],
    by rw [r4, show ({ s₁ with mem := _ } : State).gpr = s₁.gpr from rfl, g₁ _ (by decide), h.r15],
    by rw [r5, show ({ s₁ with mem := _ } : State).gpr = s₁.gpr from rfl, g₁ _ (by decide), h.r16],
    by rw [r6, show ({ s₁ with mem := _ } : State).gpr = s₁.gpr from rfl, h20],
    r7,
    by rw [r8, show ({ s₁ with mem := _ } : State).gpr = s₁.gpr from rfl, g₁ _ (by decide), h.r19],
    by rw [c .r20 (by decide), h.r20], by rw [c .r30 (by decide), h.r30], by rw [c .r31 (by decide), h.r31],
    fun r hr hv => by rw [c r hr, h.kept r hr hv],
    by rw [rd, show ({ s₁ with mem := _ } : State).rd = s₁.rd from rfl, u₁.rd, h.rd],
    by rw [wr, show ({ s₁ with mem := _ } : State).wr = s₁.wr from rfl, u₁.wr, h.wr], ?_, ?_, ?_, ?_⟩
  · exact f₁.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [Proof.Cmac.bytesAt_frame fz ivZ (by decide), h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]
  · have z₁ : s₁.gpr .r9 = (0 : BitVec 64) := u₁.gpr
    rw [hm, show Spill.saveMem s.mem (fV s₀) s₁.gpr zeroSlots =
        ((s.mem.writeW (cBk s₀) (s₁.gpr .r9)).writeW (cBk s₀ + BitVec.ofNat 64 8) (s₁.gpr .r9)) by
      simp only [Spill.saveMem, zeroSlots, Offset.add_add], z₁]
    exact zero_bytes _ _

theorem one_toNat : (BitVec.ofNat 64 1).toNat = 1 := rfl

theorem cBk_toNat {s₀ : State} (hp : CPre s₀) : (cBk s₀).toNat = (fV s₀).toNat + 64 := by
  have := hp.sv_wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega)]

theorem tail_pre {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    wholeK.pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, cBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, cBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, cBlk s₀, fScr s₀] s.wr := by
  have bs := blk_sv_sub s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [modePPC64LE, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
      callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r8 ∉ linkRegs),
      h.r3, h.r4, h.r5, h.r6, h.r7, h.r8, one_toNat, Nat.mul_one]
    have := hp.sv_wrap
    exact ⟨trivial, trivial, hp.sch_iv, hp.sch_sv.sub_right bs, hp.sch_scr, hp.iv_sv.sub_right bs, hp.iv_scr,
      (hp.scr_sv.sub_right bs).symm, hp.iv_wrap, by rw [cBk_toNat hp]; omega, hp.scr_wrap, hp.rounds⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨fSch s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 64, by simp, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fIvR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨cSv s₀, by simp, 64, by simp, by simp⟩
    · exact ⟨fScr s₀, by simp, 0, by simp, by simp⟩

/-- What the call on the block leaves. -/
structure TCall (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = fV s₀
  r30 : s.gpr .r30 = BitVec.ofNat 64 (fU s₀)
  r31 : s.gpr .r31 = fT s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (Spec.Ctr.next (fIv0 s₀) (fN s₀)) 1
  out : bytesAt s.mem (cBk s₀) 16 = Spec.Cbc.aesWith (fR s₀) (fWk s₀) (Spec.Ctr.next (fIv0 s₀) (fN s₀))

theorem tail_call_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    WP isa wholeCall s (TCall s₀) := by
  obtain ⟨hpre, hc, hw⟩ := tail_pre hp h
  have big := big_of (cW1_cW h.frame)
  have eW : bytesAt s.mem (fW s₀) (16 * (fR s₀ + 1)) = fWk s₀ :=
    Proof.Cmac.bytesAt_frame big hp.sched_big hp.sched_len
  refine WP.call (k := wholeK) crypt_correct (rd := [fSch s₀]) (wr := [fIvR s₀, cBlk s₀, fScr s₀]) hpre
    hc hw ?_ crypt_noFrames
  intro s' rd' wr' _ fr' cs' _ post₂
  simp only [modePPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_gpr' s (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r4 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' s (by decide : Reg.r6 ∉ linkRegs),
    callEntry_gpr' s (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7,
    one_toNat, eW, h.ctr, AesCtr.ctrMode_out, AesCtr.ctrMode_chain, AesCbc.length_blocksAt] at post₂
  refine ⟨by rw [cs' .r20 (by decide), h.r20], by rw [cs' .r30 (by decide), h.r30],
    by rw [cs' .r31 (by decide), h.r31], fun r hr hv => by rw [cs' r hr, h.kept r hr hv],
    by rw [rd', h.rd], by rw [wr', h.wr], ?_, ?_, post₂.2, ?_⟩
  · exact h.frame.trans (fr'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  · rw [blocksAt_frame' fr' fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_data.symm.sub_left (blk_sub s₀)
      · exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
      · exact hp.data_scr.sub_left (blk_sub s₀)]
    exact h.blocks
  · exact Modes.CtrFinal.bytesAt_of_blocksAt_one (aesWith_length _ _) h.zero post₂.1

/-- What the function leaves before restoring the registers. -/
structure Done (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = fV s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q) ^^^
    (Spec.Cbc.aesWith (fR s₀) (fWk s₀) (Spec.Ctr.next (fIv0 s₀) (fN s₀))).getD q 0
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (fIv0 s₀) (if fU s₀ = 0 then fN s₀ else fN s₀ + 1)

theorem done_of_zero {s₀ s : State} (h : Whole AesCtr.ctrMode s₀ s) (hu : fU s₀ = 0) : Done s₀ s :=
  ⟨h.r20, h.kept, h.rd, h.wr, cW1_cW (whole_cW1 h), h.blocks, fun q hq => absurd hq (by omega), by
    rw [ite_eq_left hu, h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]⟩

theorem toNat_tail {s₀ : State} (hp : CPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- The XOR of the partial last block. -/
abbrev xorCode : Prog isa :=
  .seq (.block tailKey) (.loop (.block Impl.Modes.PPC64LE.tailByte) (.nonzero .d .r30))

theorem tail_xor_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa xorCode s (Done s₀) := by
  refine WP.seq (wp_addi (by decide) (by decide) fun s₁ u₁ => wp_nil ?_)
  have hU := u_lt s₀
  have hT := toNat_tail hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hVw := hp.sv_wrap
  have hB := cBk_toNat hp
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have xp : Proof.Modes.PPC64LE.XPre s₁ (cBk s₀) (fT s₀) (fU s₀) := {
    fitR := by omega
    disj := (((hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)).sub_right
      (Region.sub_prefix (by omega))).symm
    rdK := fun q hq => by
      rw [u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]
      refine ⟨cSv s₀, by simp, ?_⟩
      rw [Offset.add_add]
      exact Offset.contains_base _ (by omega) (by omega)
    wrR := fun q hq => by
      rw [u₁.wr, h.wr, hp.wr]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show fT s₀ + BitVec.ofNat 64 q = fD s₀ + BitVec.ofNat 64 (16 * fN s₀ + q) from Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega) }
  have x0 : Proof.Modes.PPC64LE.XInv s₁ (cBk s₀) (fT s₀) (fU s₀) 0 s₁ := {
    r8 := by rw [u₁.gpr, h.r20]; exact (BitVec.add_zero _).symm
    r31 := by rw [u₁.other _ (by decide), h.r31]; exact (BitVec.add_zero _).symm
    r30 := by rw [u₁.other _ (by decide), h.r30, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Proof.Modes.PPC64LE.tailLoop_wp xp x0) fun s' d => ?_
  have tailD : ∀ r ∈ cW1 s₀, (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
    · exact hp.blk_tail.symm
    · exact hp.data_scr.sub_left (tail_sub s₀)
    · exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (blk_sv_sub s₀)
  have tailS : ∀ r ∈ [fSv s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (tail_sub s₀)).sub_right (sv64_sub s₀)
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by show fU s₀ ≤ 2 ^ 64; omega
  have ivT : ∀ r ∈ [fTail s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.iv_data.sub_right (tail_sub s₀)
  have df : Frame [fTail s₀] s.mem s'.mem := by rw [← u₁.mem]; exact d.frame
  have g (r : Reg) (h8 : r ≠ .r8) (h9 : r ≠ .r9) (h10 : r ≠ .r10) (h30 : r ≠ .r30) (h31 : r ≠ .r31) :
      s'.gpr r = s.gpr r := by
    rw [d.gpr r h8 h9 h10 h30 h31, u₁.other r h8]
  refine ⟨by rw [g .r20 (by decide) (by decide) (by decide) (by decide) (by decide), h.r20],
    fun r hr hv => ?_, by rw [d.rd, u₁.rd, h.rd], by rw [d.wr, u₁.wr, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · obtain ⟨-, h8, h9, h10, -, -, -, -, -, -, h30, h31⟩ := Proof.AesCfb.PPC64LE.Final.preserved_ne' hr hv
    rw [g r h8 h9 h10 h30 h31, h.kept r hr hv]
  · exact (cW1_cW h.frame).trans (df.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' df fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact h.blocks
  · rw [d.data q hq, u₁.mem, h.frame.bytes tailD hlen hq, (svMem_frame s₀).bytes tailS hlen hq,
      ← bytesAt_getD s.mem (cBk s₀) (show q < 16 by omega), h.out]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame df ivT (by decide), h.ctr, ← AesCtr.next_add]

theorem final_mid_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.ite (.zero .d .r30) (.block []) finalTail) s (Done s₀) := by
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [eval_u h, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [eval_u h, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (tail_args_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp hp h₁) fun _ h₂ => tail_xor_wp hp h₂ hu))

/-! ## Restoring the registers -/

theorem final_end_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Done s₀ s) :
    WP isa (.block finalRestore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ s'.mem = s.mem := by
  have hs : Spill.Saved (fV s₀) (saveG s₀) finalSaved s.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (fV s₀) (saveG s₀)).frame h.frame fun p hp' r hr => by
      have hsub : Region.Sub ⟨fV s₀ + BitVec.ofNat 64 p.2, 8⟩ (cSv s₀) :=
        Offset.sub_base _ (by have := saved_slots p hp'; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.iv_sv.symm.sub_left hsub
      · exact hp.data_sv.symm.sub_left hsub
      · exact hp.scr_sv.symm.sub_left hsub
      · exact slot_blk s₀ p hp'
  rw [restore_eq]
  refine Spill.restore_ok (b := .r20) (l := finalSaved) (by decide) h.r20 saved_fits (by decide)
    (fun p hp' => ?_) hs fun s₃ r₃ => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
  refine WP.cons exec_mtlr (wp_nil ⟨fun r hr => ?_, ?_, r₃.mem⟩)
  · show s₃.gpr r = _
    have h0 : saveG s₀ r = s₀.gpr r := by
      show (s₀.write .r0 s₀.lr).gpr r = _
      simp [State.write, preserved_ne_r0 r hr]
    rw [r₃.gpr_of (r := r) ?_, h0]
    by_cases hv : r ∈ vars
    · left
      simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · right; rw [h.kept r hr hv, h0]
  · show s₃.gpr .r0 = _
    rw [r₃.gpr (.r0, 0) (by decide)]; rfl

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : CPre s₀) :
    WP isa cryptFinal s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ ∃ s₁, Done s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_mid_wp hp h₂) fun s₃ h₃ => ?_)
  exact WP.mono (final_end_wp hp h₃) fun _ ⟨g, l, m⟩ => ⟨g, l, s₃, h₃, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalPPC64LE.post s₀ s' := by
  show Spec.Ctr.CryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem final_correct (s : State) (hs : ctrFinalPPC64LE.pre s) :
    ∃ t s', Exec isa cryptFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalPPC64LE.post s s' := by
  obtain ⟨t, s', he, hg, hl, s₁, h₁, hm⟩ := final_wp (CPre.of hs)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hl⟩, final_post h₁ hm⟩

/-! ## Constant time -/

/-- Counter blocks whose last 32 bits agree still do after `k` increments. -/
theorem lo32_next_of {t t' : List Byte} (ht : t.length = 16) (ht' : t'.length = 16)
    (h : AesCtr.lo32 t = AesCtr.lo32 t') (k : Nat) :
    AesCtr.lo32 (Spec.Ctr.next t k) = AesCtr.lo32 (Spec.Ctr.next t' k) := by
  rw [AesCtr.lo32_next ht, AesCtr.lo32_next ht']
  unfold AesCtr.lo32 at h
  omega

theorem setup_taint : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (.block finalSetup) h).isSome = true := ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15, .r16, .r19, .r20])
    (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (Taint.ofRegs [.r20, .r30, .r31]) xorCode h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.r20]) (.block finalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalPPC64LE.pre s₀) (h0' : ctrFinalPPC64LE.pre s₀')
    (hq : ctrFinalPPC64LE.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') cryptFinal fun _ _ => True := by
  have hp := CPre.of h0
  have hp' := CPre.of h0'
  obtain ⟨⟨qW, qR, qIv, qD, qL, qS, qV, qSp⟩, qLk⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, fD, qD, qN]
  have qLo : AesCtr.lo32 (fIv0 s₀) = AesCtr.lo32 (fIv0 s₀') :=
    AesCtr.lo32_of_leak (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _) qLk
  -- The registers saved and the arguments set up.
  obtain ⟨_, t₁⟩ := setup_taint
  have r₁ := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qSp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) t₁).wp
    (F₁ := fun (s : State) => Setup s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => Setup s₀' s ∧ s.sp = s₀'.sp)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨wp_sp (final_setup_wp hp), wp_sp (final_setup_wp hp')⟩
  -- The whole blocks.
  have r₂ := (RelCT.callEx (k := wholeK) (n := "vg_aes_ctr") crypt_correct crypt_ct
    (P := fun a b => (Setup s₀ a ∧ a.sp = s₀.sp) ∧ (Setup s₀' b ∧ b.sp = s₀'.sp)) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre hp ha.1
      obtain ⟨pb, cb, wb⟩ := whole_pre hp' hb.1
      refine ⟨_, _, _, _, pa, pb, ⟨?_, ?_⟩, ca, wa, cb, wb⟩
      · simp only [modePPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
          callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
          callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
          callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r8 ∉ linkRegs),
          ha.1.r3, ha.1.r4, ha.1.r5, ha.1.r6, ha.1.r7, ha.1.r8, ha.2,
          hb.1.r3, hb.1.r4, hb.1.r5, hb.1.r6, hb.1.r7, hb.1.r8, hb.2]
        rw [fW, fW, fIv, fIv, fD, fD, fS, fS, qW, qR, qIv, qD, qS, qSp, qN]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [AesCbc.PPC64LE.iv0, AesCbc.PPC64LE.Iv, State.withRegions_gpr, State.withRegions_mem,
          State.callEntry_mem, callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), ha.1.r5, hb.1.r5,
          ha.1.mem, hb.1.mem]
        rw [(sv_bytes hp).2.1, (sv_bytes hp').2.1]
        exact qLo).wp
    (F₁ := fun (s : State) => Whole AesCtr.ctrMode s₀ s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => Whole AesCtr.ctrMode s₀' s ∧ s.sp = s₀'.sp)
    fun a b h => ⟨WP.mono (wp_sp (whole_wp hp h.1.1)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
      WP.mono (wp_sp (whole_wp hp' h.2.1)) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
  -- The partial last block.
  obtain ⟨_, t₃⟩ := tailArgs_taint
  obtain ⟨_, t₄⟩ := xor_taint
  have tail (hu : fU s₀ ≠ 0) : RelCT isa
      (fun a b => (Whole AesCtr.ctrMode s₀ a ∧ a.sp = s₀.sp) ∧ (Whole AesCtr.ctrMode s₀' b ∧ b.sp = s₀'.sp))
      finalTail fun a b => (Done s₀ a ∧ a.sp = s₀.sp) ∧ (Done s₀' b ∧ b.sp = s₀'.sp) := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₁ := (taintRegs
      (P := fun a b => (Whole AesCtr.ctrMode s₀ a ∧ a.sp = s₀.sp) ∧ (Whole AesCtr.ctrMode s₀' b ∧ b.sp = s₀'.sp)) _
      (fun a b h => ⟨by rw [h.1.2, h.2.2, qSp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [h.1.1.r14, h.2.1.r14, fW, fW, qW]
        · rw [h.1.1.r15, h.2.1.r15, qR]
        · rw [h.1.1.r16, h.2.1.r16, fIv, fIv, qIv]
        · rw [h.1.1.r19, h.2.1.r19, fS, fS, qS]
        · rw [h.1.1.r20, h.2.1.r20, fV, fV, qV]⟩) t₃).wp
      (F₁ := fun (s : State) => TArgs s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => TArgs s₀' s ∧ s.sp = s₀'.sp)
      fun a b h => ⟨WP.mono (wp_sp (tail_args_wp hp h.1.1)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
        WP.mono (wp_sp (tail_args_wp hp' h.2.1)) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
    have a₂ := (RelCT.callEx (k := wholeK) (n := "vg_aes_ctr") crypt_correct crypt_ct
      (P := fun a b => (TArgs s₀ a ∧ a.sp = s₀.sp) ∧ (TArgs s₀' b ∧ b.sp = s₀'.sp)) fun a b ⟨ha, hb⟩ => by
        obtain ⟨pa, ca, wa⟩ := tail_pre hp ha.1
        obtain ⟨pb, cb, wb⟩ := tail_pre hp' hb.1
        refine ⟨_, _, _, _, pa, pb, ⟨?_, ?_⟩, ca, wa, cb, wb⟩
        · simp only [modePPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
            callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
            callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
            callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r8 ∉ linkRegs),
            ha.1.r3, ha.1.r4, ha.1.r5, ha.1.r6, ha.1.r7, ha.1.r8, ha.2,
            hb.1.r3, hb.1.r4, hb.1.r5, hb.1.r6, hb.1.r7, hb.1.r8, hb.2]
          rw [fW, fW, fIv, fIv, cBk, cBk, fV, fV, fS, fS, qW, qR, qIv, qV, qS, qSp]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
        · simp only [AesCbc.PPC64LE.iv0, AesCbc.PPC64LE.Iv, State.withRegions_gpr, State.withRegions_mem,
            State.callEntry_mem, callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), ha.1.r5, hb.1.r5]
          rw [ha.1.ctr, hb.1.ctr, qN]
          exact lo32_next_of (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _) qLo _).wp
      (F₁ := fun (s : State) => TCall s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => TCall s₀' s ∧ s.sp = s₀'.sp)
      fun a b h => ⟨WP.mono (wp_sp (tail_call_wp hp h.1.1)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
        WP.mono (wp_sp (tail_call_wp hp' h.2.1)) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
    have a₃ := (taintRegs
      (P := fun a b => (TCall s₀ a ∧ a.sp = s₀.sp) ∧ (TCall s₀' b ∧ b.sp = s₀'.sp)) _
      (fun a b h => ⟨by rw [h.1.2, h.2.2, qSp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.1.r20, h.2.1.r20, fV, fV, qV]
        · rw [h.1.1.r30, h.2.1.r30, qU]
        · rw [h.1.1.r31, h.2.1.r31, qT]⟩) t₄).wp
      (F₁ := fun (s : State) => Done s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => Done s₀' s ∧ s.sp = s₀'.sp)
      fun a b h => ⟨WP.mono (wp_sp (tail_xor_wp hp h.1.1 hu)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
        WP.mono (wp_sp (tail_xor_wp hp' h.2.1 hu')) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
    exact (a₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((a₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₃.mono (fun _ _ h => h) fun _ _ h => h.2))
  have r₃ : RelCT isa
      (fun a b => (Whole AesCtr.ctrMode s₀ a ∧ a.sp = s₀.sp) ∧ (Whole AesCtr.ctrMode s₀' b ∧ b.sp = s₀'.sp))
      (.ite (.zero .d .r30) (.block []) finalTail)
      (fun a b => (Done s₀ a ∧ a.sp = s₀.sp) ∧ (Done s₀' b ∧ b.sp = s₀'.sp)) := by
    refine RelCT.ite (fun a b h => by rw [eval_u h.1.1, eval_u h.2.1, qU]) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have h0 : fU s₀ = 0 := by
        have := h.2; rw [eval_u h.1.1.1] at this; simpa using this
      exact ⟨⟨done_of_zero h.1.1.1 h0, h.1.1.2⟩, ⟨done_of_zero h.1.2.1 (qU ▸ h0), h.1.2.2⟩⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1⟩) fun _ _ h => h
      have := h.2; rw [eval_u h.1.1.1] at this; simpa using this
  -- The registers restored.
  obtain ⟨_, t₅⟩ := restore_taint
  have r₄ := taintRegs
    (P := fun a b => (Done s₀ a ∧ a.sp = s₀.sp) ∧ (Done s₀' b ∧ b.sp = s₀'.sp)) _
    (fun a b h => ⟨by rw [h.1.2, h.2.2, qSp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.r20, h.2.1.r20, fV, fV, qV]⟩) t₅
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (r₃.seq r₄))

theorem final_ct : ConstantTime isa ctrFinalPPC64LE.pre ctrFinalPPC64LE.pub cryptFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem cryptFinal_verified : Verified PPC64LE.target cryptFinal finalScratchContract :=
  Verified.of_correct final_correct final_ct final_implies

/-! ## With `save` on the stack

The final function has six argument words, so `save` is its seventh, in
`r9`: it runs its code in a frame of 112 bytes on the stack
(`withStackScratchWiped`), its 32-byte header and `save`'s 80 bytes (the
registers, then the block that held the last output block), which it zeroes
before returning. The code's calls use no stack, so 112 in all. -/

theorem frameSat_pre : ∃ s, (finalRoundsContract PPC64LE.abi (0 + 112)).pre s := by
  implies_sat [finalRoundsContract, Spec.Ctr.aesFinalSig, finalPre, finalPost, PPC64LE.abi,
    PPC64LE.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem cryptFinal_framed :
    Verified PPC64LE.target (Impl.StackScratch.PPC64LE.withStackScratchWiped 112 .r9 10 cryptFinal)
      (finalRoundsContract PPC64LE.abi 112) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Ctr.aesFinalSig) (nm := "save") (e := .u64) (n := 10)
    (pre := finalPre PPC64LE.abi.ptrBits) (post := finalPost PPC64LE.abi.ptrBits) (wa := false)
    (leak := some (finalLeak PPC64LE.abi.ptrBits))
    (stack := 0) (bytes := 112) (words := 10) cryptFinal_verified (by decide) (by decide) (by decide)
    (finalPre_local _) (finalPost_local _) (finalPost_localOut _) frameSat_pre (hleak := finalLeak_local _)

end VG.Proof.AesCtr.PPC64LE.Final
