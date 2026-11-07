module

public import VerifiedGarbage.Impl.AesCtr.RISCV64.Final
public import VerifiedGarbage.Proof.AesCtr.Final
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Verified
public import VerifiedGarbage.Proof.AesCtr.RISCV64.CT
public import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit
import VerifiedGarbage.Proof.AesCtr.Ctr32
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Modes.CtrFinal
import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32Verified
meta import VerifiedGarbage.Impl.AesCtr.RISCV64.Final
meta import VerifiedGarbage.Proof.AesCtr.Final
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.CT
meta import VerifiedGarbage.Proof.AesCfb.RISCV64.Final
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
meta import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit
meta import VerifiedGarbage.Proof.AesCtr.Ctr32
meta import VerifiedGarbage.Proof.AesCtr.Spec
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Modes.CtrFinal
meta import VerifiedGarbage.Proof.Modes.Words
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-CTR of a message's last piece on RISC-V

`cryptFinal_framed`: `vg_aes_ctr_final` (`Impl/AesCtr/RISCV64/Final.lean`)
meets `Proof.AesCtr.finalRoundsContract`, from which the shared contract
follows (`Proof.AesCtr.final_keyed`).

The code is proven against `ctrFinalRISCV64`, with a seventh argument `save`
(`a6`) of 80 bytes, for its return address and its caller's registers and a
block of its own (`final_implies`: the shared contract with it,
`finalScratchContract`), as a caller of the whole-block function, through its
contract (`modeRISCV64 ctrMode`, with `ctrPub`). It shares AES-CFB's final
functions' setup (`Proof/AesCfb/RISCV64/Final.lean`: `Setup`, `Whole`):

* `final_setup_wp`, `whole_wp`: the registers saved, and the whole-block
  function on the `n = len / 16` whole blocks (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, the block after the
  registers in `save` zeroed and the whole-block function on it
  (`tail_args_wp`, `tail_call_wp`), which leaves `CIPH_K(Tₙ₊₁)` there and
  `Tₙ₊₂` in `ctr`, and its first `u` bytes XORed into them
  (`Modes.RISCV64.xorLoop_wp`, `tail_xor_wp`); what is left before the
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

namespace VG.Proof.AesCtr.RISCV64.Final

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesCtr.RISCV64 (tailArgs tailMoves tailKey zeroSlots finalTail cryptFinal crypt)
open VG.Impl.AesCfb.RISCV64 (finalSaved finalMoves finalSetup finalRestore)
open VG.Proof.AesCfb.RISCV64.Final (fW fR fIv fD fL fS fV fN fU fT fSch fIvR fData fBlk fTail fScr fSv
  fWk fIv0 fBlks svMem Setup Whole Kept finalSat finalFrameSat shr4 shr4_shl4 sub_shl4 cs_of callEntry
  toNat_n eval_u bytesAt_getD blocksAt_frame' svMem_frame saved_slots saved_fits blk_sub tail_sub fN_eq
  fU_eq n_lt u_lt agree_of upd_gpr a1_ofNat)
open VG.Proof.AesCbc (Mode)
open VG.RISCV64.Steps
open VG.Proof.AesCbc.RISCV64 (modeRISCV64 one_toNat)

/-! ## The contract -/

/-- The code's contract, with the arguments `(schedule = a0, rounds = a1,
ctr = a2, data = a3, len = a4, scratch = a5, save = a6)`, `save` of 80
bytes: the data and the counter block as `Spec.Ctr.CryptFinal` says, by AES
with the key schedule it is given; the counter block's last four bytes are
public. -/
def ctrFinalRISCV64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let iv : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    let sv : Region := ⟨s.gpr .a6, 80⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr, sv] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint sv ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint sv ∧
      data.Disjoint scr ∧ data.Disjoint sv ∧ scr.Disjoint sv ∧
      (s.gpr .a0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      (s.gpr .a6).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat % 8 = 0 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    Spec.Ctr.CryptFinal (ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) s.mem s'.mem (s.gpr .a2) (s.gpr .a3)
      (s.gpr .a4).toNat
  pub s₁ s₂ :=
    (s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp) ∧
      Spec.Ctr.ctrLeak s₁.mem (s₁.gpr .a2) = Spec.Ctr.ctrLeak s₂.mem (s₂.gpr .a2)

/-- The contract the frame needs: the shared one, with `save`, 80 bytes, as
a seventh argument, and no stack (a call keeps its return address in
`ra`). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract RISCV64.abi Spec.Ctr.aesFinalSig "save" .u64 10 (finalPre RISCV64.abi.ptrBits)
    (finalPost RISCV64.abi.ptrBits) false 0 (some (finalLeak RISCV64.abi.ptrBits))

/-- A state satisfying the precondition. -/
def ctrSat : State := { finalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 80⟩] }

theorem final_implies : ctrFinalRISCV64.Implies finalScratchContract := by
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ctr.aesFinalSig, finalPre, finalPost, finalLeak, Spec.Ctr.ctrLeak, ctrFinalRISCV64, RISCV64.abi,
    RISCV64.argRegs] [ctrSat, finalSat] using ctrSat

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
  sv_al : (fV s₀).toNat % 8 = 0
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem CPre.of {s₀ : State} (h : ctrFinalRISCV64.pre s₀) : CPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, _, a14, a15, a16, a17, a18, a19⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a14, a15, a16, a17, a18, a19⟩

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

set_option linter.unusedSimpArgs false in
theorem final_setup_wp {s₀ : State} (hp : CPre s₀) : WP isa (.block finalSetup) s₀ (Setup s₀) := by
  have hw : ∀ p ∈ finalSaved, InRegions s₀.wr (s₀.gpr .a6 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [hp.wr]
    have := saved_slots p hp'
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  show WP isa (.block (Spill.saveCode .a6 finalSaved ++ finalMoves)) _ _
  refine Spill.save_ok hp.sv_al saved_fits hw ?_
  unfold finalMoves Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_srl (by decide) fun s₆ u₆ => wp_sll (by decide) fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_sub fun s₉ u₉ => wp_mv fun s₁₀ u₁₀ => WP.block_nil ?_
  exact {
    s1 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s4 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s5 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s2 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; rw [shr4_shl4]
    s3 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; rw [shr4_shl4, sub_shl4]
    s6 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    s7 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a0 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a1 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a2 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a3 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a4 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; rw [shr4]
    a5 := by simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    kept := fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    sp := by rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
    mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
    wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr] }

theorem crypt_noFrames : crypt.noFrames = true := by
  simp only [crypt, Impl.AesCbc.RISCV64.whole, Impl.AesCtr.RISCV64.body, Impl.AesCtr.RISCV64.ctrCall,
    Code.noFrames, Bool.and_self, Bool.and_true, Bool.true_and]
  exact Proof.Aes.RISCV64.ctr32To_noFrames

/-- The whole-block function's contract: `modeRISCV64 ctrMode`, with the
last 32 bits of the counter block public. -/
abbrev wholeK : Contract isa := { modeRISCV64 AesCtr.ctrMode with pub := ctrPub }

theorem whole_pre {s₀ : State} (hp : CPre s₀) {s : State} (h : Setup s₀ s) :
    wholeK.pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, fBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, fBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, fBlk s₀, fScr s₀] s.wr := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
      callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
      callEntry s (by decide : Reg.a4 ∉ linkRegs), callEntry s (by decide : Reg.a5 ∉ linkRegs),
      h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, toNat_n]
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
    WP isa (.call "vg_aes_ctr" crypt) s (Whole AesCtr.ctrMode s₀) := by
  obtain ⟨eW, eIv, eB⟩ := sv_bytes hp
  obtain ⟨hpre, hc, hw⟩ := whole_pre hp h
  refine WP.call (k := wholeK) crypt_correct (rd := [fSch s₀]) (wr := [fIvR s₀, fBlk s₀, fScr s₀]) hpre
    hc hw ?_ crypt_noFrames
  intro s' rd' wr' sp' fr' cs' _ post₂
  rw [h.mem] at fr'
  simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
    callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
    callEntry s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4,
    toNat_n, h.mem, eW, eIv, eB] at post₂
  exact ⟨by rw [cs_of cs' .s1 (by simp), h.s1], by rw [cs_of cs' .s4 (by simp), h.s4],
    by rw [cs_of cs' .s5 (by simp), h.s5], by rw [cs_of cs' .s2 (by simp), h.s2],
    by rw [cs_of cs' .s3 (by simp), h.s3], by rw [cs_of cs' .s6 (by simp), h.s6],
    by rw [cs_of cs' .s7 (by simp), h.s7],
    fun r hr => by rw [cs_of cs' r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp', h.sp], by rw [rd', h.rd], by rw [wr', h.wr], fr', post₂.1, post₂.2⟩

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
  a0 : s.gpr .a0 = fW s₀
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = fIv s₀
  a3 : s.gpr .a3 = cBk s₀
  a4 : s.gpr .a4 = BitVec.ofNat 64 1
  a5 : s.gpr .a5 = fS s₀
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s7 : s.gpr .s7 = fV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
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

set_option linter.unusedSimpArgs false in
theorem tail_args_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.block tailArgs) s (TArgs s₀) := by
  have f₁ := whole_cW1 h
  show WP isa (.block (.li .t0 0 :: (Spill.saveCode .s7 zeroSlots ++ tailMoves))) _ _
  refine wp_li (imm := 0) (by decide) fun s₁ z => ?_
  have h7 : s₁.gpr .s7 = fV s₀ := by rw [z.other _ (by decide), h.s7]
  have hw : ∀ p ∈ zeroSlots, InRegions s₁.wr (s₁.gpr .s7 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [z.wr, h.wr, hp.wr, h7]
    simp only [zeroSlots, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · exact ⟨cSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega)⟩
    · exact ⟨cSv s₀, by simp, Offset.contains_base _ (by decide) (by have := hp.sv_wrap; omega)⟩
  refine Spill.save_ok (by rw [h7]; exact hp.sv_al) (by decide) hw ?_
  unfold tailMoves Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (imm := 64) (by decide) fun s₅ u₅ =>
    wp_li (imm := 1) (by decide) fun s₆ u₆ => wp_mv fun s₇ u₇ => WP.block_nil ?_
  have c (r : Reg) (hr : r = .s0 ∨ r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4 ∨ r = .s5 ∨ r = .s6 ∨ r = .s7 ∨
      r = .s8 ∨ r = .s9 ∨ r = .s10 ∨ r = .s11) : s₇.gpr r = s.gpr r := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq,
        ↓reduceIte] <;> exact z.other _ (by decide)
  have sp : s₇.sp = s.sp := by
    rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, show ({ s₁ with mem := _ } : State).sp = s₁.sp from rfl, z.sp]
  have rd : s₇.rd = s.rd := by
    rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, show ({ s₁ with mem := _ } : State).rd = s₁.rd from rfl, z.rd]
  have wr : s₇.wr = s.wr := by
    rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, show ({ s₁ with mem := _ } : State).wr = s₁.wr from rfl, z.wr]
  have hm : s₇.mem = Spill.saveMem s.mem (fV s₀) s₁.gpr zeroSlots := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, h7]
    show Spill.saveMem s₁.mem _ _ _ = _
    rw [z.mem]
  have fz : Frame [cBlk s₀] s.mem s₇.mem := by rw [hm]; exact zero_frame s₀ _ _
  have ivZ : ∀ r ∈ [cBlk s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv.sub_right (blk_sv_sub s₀)
  have blkZ : ∀ r ∈ [cBlk s₀], (fBlk s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_sv.sub_left (blk_sub s₀)).sub_right (blk_sv_sub s₀)
  have g7 : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr .s7) s₁.gpr zeroSlots } : State).gpr = s₁.gpr := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [c .s2 (by simp), h.s2], by rw [c .s3 (by simp), h.s3],
    by rw [c .s7 (by simp), h.s7],
    fun r hr => by rw [c r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr], ?_, ?_, ?_, ?_⟩
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [z.other _ (by decide), h.s1]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [z.other _ (by decide), h.s4]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [z.other _ (by decide), h.s5]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [h7]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte]
  · simp only [upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, reduceCtorEq, ↓reduceIte,
      g7]
    rw [z.other _ (by decide), h.s6]
  · exact f₁.trans (fz.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr])
  · rw [blocksAt_frame' fz blkZ]; exact h.blocks
  · rw [Proof.Cmac.bytesAt_frame fz ivZ (by decide), h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]
  · rw [hm, show Spill.saveMem s.mem (fV s₀) s₁.gpr zeroSlots =
        ((s.mem.writeW (cBk s₀) (s₁.gpr .t0)).writeW (cBk s₀ + BitVec.ofNat 64 8) (s₁.gpr .t0)) by
      simp only [Spill.saveMem, zeroSlots, Offset.add_add], z.gpr]
    exact zero_bytes _ _

theorem cBk_toNat {s₀ : State} (hp : CPre s₀) : (cBk s₀).toNat = (fV s₀).toNat + 64 := by
  have := hp.sv_wrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega)]

theorem tail_pre {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    wholeK.pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, cBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, cBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, cBlk s₀, fScr s₀] s.wr := by
  have bs := blk_sv_sub s₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
      callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
      callEntry s (by decide : Reg.a4 ∉ linkRegs), callEntry s (by decide : Reg.a5 ∉ linkRegs),
      h.a0, h.a1, h.a2, h.a3, h.a4, h.a5, one_toNat, Nat.mul_one]
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
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s7 : s.gpr .s7 = fV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (cW1 s₀) (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) =
    Spec.Ctr.crypt (Spec.Cbc.aesWith (fR s₀) (fWk s₀)) (fIv0 s₀) (fBlks s₀)
  ctr : bytesAt s.mem (fIv s₀) 16 = Spec.Ctr.next (Spec.Ctr.next (fIv0 s₀) (fN s₀)) 1
  out : bytesAt s.mem (cBk s₀) 16 = Spec.Cbc.aesWith (fR s₀) (fWk s₀) (Spec.Ctr.next (fIv0 s₀) (fN s₀))

theorem tail_call_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TArgs s₀ s) :
    WP isa (.call "vg_aes_ctr" crypt) s (TCall s₀) := by
  obtain ⟨hpre, hc, hw⟩ := tail_pre hp h
  have big := big_of (cW1_cW h.frame)
  have eW : bytesAt s.mem (fW s₀) (16 * (fR s₀ + 1)) = fWk s₀ :=
    Proof.Cmac.bytesAt_frame big hp.sched_big hp.sched_len
  refine WP.call (k := wholeK) crypt_correct (rd := [fSch s₀]) (wr := [fIvR s₀, cBlk s₀, fScr s₀]) hpre
    hc hw ?_ crypt_noFrames
  intro s' rd' wr' sp' fr' cs' _ post₂
  simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry s (by decide : Reg.a0 ∉ linkRegs), callEntry s (by decide : Reg.a1 ∉ linkRegs),
    callEntry s (by decide : Reg.a2 ∉ linkRegs), callEntry s (by decide : Reg.a3 ∉ linkRegs),
    callEntry s (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4,
    one_toNat, eW, h.ctr, AesCtr.ctrMode_out, AesCtr.ctrMode_chain, AesCbc.length_blocksAt] at post₂
  have fc : Frame (cW1 s₀) s.mem s'.mem := fr'.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine ⟨by rw [cs_of cs' .s2 (by simp), h.s2], by rw [cs_of cs' .s3 (by simp), h.s3],
    by rw [cs_of cs' .s7 (by simp), h.s7],
    fun r hr => by rw [cs_of cs' r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp', h.sp], by rw [rd', h.rd], by rw [wr', h.wr], h.frame.trans fc, ?_, post₂.2, ?_⟩
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
  s7 : s.gpr .s7 = fV s₀
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
  ⟨h.s7, h.kept, h.rd, h.wr, cW1_cW (whole_cW1 h), h.blocks, fun q hq => absurd hq (by omega), by
    rw [ite_eq_left hu, h.iv, AesCtr.ctrMode_chain, AesCbc.length_blocksAt]⟩

theorem toNat_tail {s₀ : State} (hp : CPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

open VG.Proof.Modes.RISCV64 (XPre XInv xorLoop_wp xf)

theorem tail_xor_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : TCall s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block tailKey) (.loop (.block Impl.Modes.RISCV64.xorStep) (.nonzero .s3))) s (Done s₀) := by
  refine WP.seq (wp_addi (imm := 64) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hU := u_lt s₀
  have hT := toNat_tail hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hVw := hp.sv_wrap
  have hB := cBk_toNat hp
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have xp : XPre s₁ (cBk s₀) (fT s₀) (fU s₀) := {
    fK := by omega
    fR := by omega
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
  have x0 : XInv s₁ (cBk s₀) (fT s₀) (fU s₀) 0 s₁ := {
    t2 := by rw [u₁.gpr, h.s7]; exact (BitVec.add_zero _).symm
    s2 := by rw [u₁.other _ (by decide), h.s2]; exact (BitVec.add_zero _).symm
    s3 := by rw [u₁.other _ (by decide), h.s3, Nat.sub_zero]
    lt := by omega
    mem := (Proof.Modes.over_zero _ _ _).symm
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (xorLoop_wp xp x0) fun s' d => ?_
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
  have g (r : Reg) (hr : r = .s7 ∨ r = .s0 ∨ r = .s8 ∨ r = .s9 ∨ r = .s10 ∨ r = .s11) : s'.gpr r = s.gpr r := by
    rw [d.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      u₁.other _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have fr : Frame [fTail s₀] s.mem s'.mem := by
    rw [d.mem, u₁.mem]; exact Proof.Modes.over_frame _ _ _ _
  refine ⟨by rw [g .s7 (by simp), h.s7], fun r hr => by
      rw [g r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [d.rd, u₁.rd, h.rd], by rw [d.wr, u₁.wr, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact (cW1_cW h.frame).trans (fr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact h.blocks
  · rw [d.mem, Proof.Modes.over_at hq (by omega), xf, u₁.mem, h.frame.bytes tailD hlen hq,
      (svMem_frame s₀).bytes tailS hlen hq,
      ← bytesAt_getD s.mem (cBk s₀) (show q < 16 by omega), h.out]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame fr ivT (by decide), h.ctr, ← AesCtr.next_add]

theorem final_mid_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Whole AesCtr.ctrMode s₀ s) :
    WP isa (.ite (.zero .s3) (.block []) finalTail) s (Done s₀) := by
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [eval_u h, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [eval_u h, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (tail_args_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (tail_call_wp hp h₁) fun _ h₂ => tail_xor_wp hp h₂ hu))

/-! ## Restoring the registers -/

theorem final_end_wp {s₀ : State} (hp : CPre s₀) {s : State} (h : Done s₀ s) :
    WP isa (.block finalRestore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.mem = s.mem := by
  have hs : Spill.Saved (fV s₀) s₀.gpr finalSaved s.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (fV s₀) s₀.gpr).frame h.frame fun p hp' r hr => by
      have hsub : Region.Sub ⟨fV s₀ + BitVec.ofNat 64 p.2, 8⟩ (cSv s₀) :=
        Offset.sub_base _ (by have := saved_slots p hp'; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.iv_sv.symm.sub_left hsub
      · exact hp.data_sv.symm.sub_left hsub
      · exact hp.scr_sv.symm.sub_left hsub
      · exact slot_blk s₀ p hp'
  show WP isa (.block (Spill.restoreCode .s7 finalSaved)) _ _
  refine WP.mono (Spill.restore_wp hp.sv_al h.s7 saved_fits (by decide) (fun p hp' => ?_) hs)
    fun s' r => ⟨fun q hq => r.gpr_of ?_, r.gpr (.ra, 0) (by decide), r.mem⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨cSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inl (by decide)
      | exact .inr (h.kept _ (by simp))

/-! ## The whole function -/

theorem final_wp {s₀ : State} (hp : CPre s₀) :
    WP isa cryptFinal s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        ∃ s₁, Done s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_mid_wp hp h₂) fun s₃ h₃ => ?_)
  exact WP.mono (final_end_wp hp h₃) fun _ ⟨g, ra, m⟩ => ⟨g, ra, s₃, h₃, m⟩

/-- `Spec.Ctr.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done s₀ s₁) (hm : s'.mem = s₁.mem) : ctrFinalRISCV64.post s₀ s' := by
  show Spec.Ctr.CryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  exact Modes.CtrFinal.cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact h.blocks)
    (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.ctr)

theorem final_correct (s : State) (hs : ctrFinalRISCV64.pre s) :
    ∃ t s', Exec isa cryptFinal s t s' ∧ abiPreserved s s' ∧ ctrFinalRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, s₁, h₁, hm⟩ := final_wp (CPre.of hs)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, final_post h₁ hm⟩

/-! ## Constant time -/

/-- Counter blocks whose last 32 bits agree still do after `k` increments. -/
theorem lo32_next_of {t t' : List Byte} (ht : t.length = 16) (ht' : t'.length = 16)
    (h : AesCtr.lo32 t = AesCtr.lo32 t') (k : Nat) :
    AesCtr.lo32 (Spec.Ctr.next t k) = AesCtr.lo32 (Spec.Ctr.next t' k) := by
  rw [AesCtr.lo32_next ht, AesCtr.lo32_next ht']
  unfold AesCtr.lo32 at h
  omega

theorem setup_taint : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
    (.block finalSetup) h).isSome = true := ⟨_, by taint_decide⟩

theorem tailArgs_taint : ∃ h, (taint.check (Taint.ofRegs [.s1, .s4, .s5, .s6, .s7])
    (.block tailArgs) h).isSome = true := ⟨_, by taint_decide⟩

theorem xor_taint : ∃ h, (taint.check (Taint.ofRegs [.s7, .s2, .s3])
    (.seq (.block tailKey) (.loop (.block Impl.Modes.RISCV64.xorStep) (.nonzero .s3))) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.s7]) (.block finalRestore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem final_rel {s₀ s₀' : State} (h0 : ctrFinalRISCV64.pre s₀) (h0' : ctrFinalRISCV64.pre s₀')
    (hq : ctrFinalRISCV64.pub s₀ s₀') :
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
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of qSp fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) t₁).wp
    (F₁ := Setup s₀) (F₂ := Setup s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨final_setup_wp hp, final_setup_wp hp'⟩
  -- The whole blocks.
  have r₂ := (RelCT.callEx (k := wholeK) (n := "vg_aes_ctr") crypt_correct crypt_ct
    (P := fun a b => Setup s₀ a ∧ Setup s₀' b) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre hp ha
      obtain ⟨pb, cb, wb⟩ := whole_pre hp' hb
      refine ⟨_, _, _, _, pa, pb, ⟨?_, ?_⟩, ca, wa, cb, wb⟩
      · simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
          callEntry a (by decide : Reg.a0 ∉ linkRegs), callEntry a (by decide : Reg.a1 ∉ linkRegs),
          callEntry a (by decide : Reg.a2 ∉ linkRegs), callEntry a (by decide : Reg.a3 ∉ linkRegs),
          callEntry a (by decide : Reg.a4 ∉ linkRegs), callEntry a (by decide : Reg.a5 ∉ linkRegs),
          callEntry b (by decide : Reg.a0 ∉ linkRegs), callEntry b (by decide : Reg.a1 ∉ linkRegs),
          callEntry b (by decide : Reg.a2 ∉ linkRegs), callEntry b (by decide : Reg.a3 ∉ linkRegs),
          callEntry b (by decide : Reg.a4 ∉ linkRegs), callEntry b (by decide : Reg.a5 ∉ linkRegs),
          ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.sp, hb.a0, hb.a1, hb.a2, hb.a3, hb.a4, hb.a5, hb.sp]
        rw [fW, fW, fIv, fIv, fD, fD, fS, fS, qW, qR, qIv, qD, qS, qSp, qN]
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · simp only [AesCbc.RISCV64.iv0, AesCbc.RISCV64.Iv, State.withRegions_gpr, State.withRegions_mem,
          State.callEntry_mem, callEntry a (by decide : Reg.a2 ∉ linkRegs),
          callEntry b (by decide : Reg.a2 ∉ linkRegs), ha.a2, hb.a2, ha.mem, hb.mem]
        rw [(sv_bytes hp).2.1, (sv_bytes hp').2.1]
        exact qLo).wp
    (F₁ := Whole AesCtr.ctrMode s₀) (F₂ := Whole AesCtr.ctrMode s₀')
    fun a b h => ⟨whole_wp hp h.1, whole_wp hp' h.2⟩
  -- The partial last block.
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b)
      finalTail fun a b => Done s₀ a ∧ Done s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    obtain ⟨_, t₃⟩ := tailArgs_taint
    have a₁ := (RelCT.taint (A := taint)
      (P := fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b) _
      (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · rw [h.1.s1, h.2.s1, fW, fW, qW]
        · rw [h.1.s4, h.2.s4, qR]
        · rw [h.1.s5, h.2.s5, fIv, fIv, qIv]
        · rw [h.1.s6, h.2.s6, fS, fS, qS]
        · rw [h.1.s7, h.2.s7, fV, fV, qV]) t₃).wp
      (F₁ := TArgs s₀) (F₂ := TArgs s₀')
      fun a b h => ⟨tail_args_wp hp h.1, tail_args_wp hp' h.2⟩
    have a₂ := (RelCT.callEx (k := wholeK) (n := "vg_aes_ctr") crypt_correct crypt_ct
      (P := fun a b => TArgs s₀ a ∧ TArgs s₀' b) fun a b ⟨ha, hb⟩ => by
        obtain ⟨pa, ca, wa⟩ := tail_pre hp ha
        obtain ⟨pb, cb, wb⟩ := tail_pre hp' hb
        refine ⟨_, _, _, _, pa, pb, ⟨?_, ?_⟩, ca, wa, cb, wb⟩
        · simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
            callEntry a (by decide : Reg.a0 ∉ linkRegs), callEntry a (by decide : Reg.a1 ∉ linkRegs),
            callEntry a (by decide : Reg.a2 ∉ linkRegs), callEntry a (by decide : Reg.a3 ∉ linkRegs),
            callEntry a (by decide : Reg.a4 ∉ linkRegs), callEntry a (by decide : Reg.a5 ∉ linkRegs),
            callEntry b (by decide : Reg.a0 ∉ linkRegs), callEntry b (by decide : Reg.a1 ∉ linkRegs),
            callEntry b (by decide : Reg.a2 ∉ linkRegs), callEntry b (by decide : Reg.a3 ∉ linkRegs),
            callEntry b (by decide : Reg.a4 ∉ linkRegs), callEntry b (by decide : Reg.a5 ∉ linkRegs),
            ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.sp, hb.a0, hb.a1, hb.a2, hb.a3, hb.a4, hb.a5, hb.sp]
          rw [fW, fW, fIv, fIv, cBk, cBk, fV, fV, fS, fS, qW, qR, qIv, qV, qS, qSp]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
        · simp only [AesCbc.RISCV64.iv0, AesCbc.RISCV64.Iv, State.withRegions_gpr, State.withRegions_mem,
            State.callEntry_mem, callEntry a (by decide : Reg.a2 ∉ linkRegs),
            callEntry b (by decide : Reg.a2 ∉ linkRegs), ha.a2, hb.a2]
          rw [ha.ctr, hb.ctr, qN]
          exact lo32_next_of (Proof.Cmac.bytesAt_length _ _ _) (Proof.Cmac.bytesAt_length _ _ _) qLo _).wp
      (F₁ := TCall s₀) (F₂ := TCall s₀') fun a b h => ⟨tail_call_wp hp h.1, tail_call_wp hp' h.2⟩
    obtain ⟨_, t₄⟩ := xor_taint
    have a₃ := (RelCT.taint (A := taint) (P := fun a b => TCall s₀ a ∧ TCall s₀' b) _
      (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.s7, h.2.s7, fV, fV, qV]
        · rw [h.1.s2, h.2.s2, qT]
        · rw [h.1.s3, h.2.s3, qU]) t₄).wp
      (F₁ := Done s₀) (F₂ := Done s₀')
      fun a b h => ⟨tail_xor_wp hp h.1 hu, tail_xor_wp hp' h.2 hu'⟩
    exact (a₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((a₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₃.mono (fun _ _ h => h) fun _ _ h => h.2))
  have r₃ : RelCT isa (fun a b => Whole AesCtr.ctrMode s₀ a ∧ Whole AesCtr.ctrMode s₀' b)
      (.ite (.zero .s3) (.block []) finalTail) (fun a b => Done s₀ a ∧ Done s₀' b) := by
    refine RelCT.ite (fun a b h => by rw [eval_u h.1, eval_u h.2, qU]) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have h0 : fU s₀ = 0 := by
        have := h.2; rw [eval_u h.1.1] at this; simpa using this
      exact ⟨done_of_zero h.1.1 h0, done_of_zero h.1.2 (qU ▸ h0)⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [eval_u h.1.1] at this; simpa using this
  have r₃' := r₃.wp (F₁ := fun (s : State) => s.sp = s₀.sp) (F₂ := fun (s : State) => s.sp = s₀'.sp)
    fun a b h =>
      ⟨WP.mono (AesCbc.RISCV64.wp_sp (final_mid_wp hp h.1)) fun _ x => x.2.trans h.1.sp,
        WP.mono (AesCbc.RISCV64.wp_sp (final_mid_wp hp' h.2)) fun _ x => x.2.trans h.2.sp⟩
  -- The registers restored.
  obtain ⟨_, t₅⟩ := restore_taint
  have r₄ := RelCT.taint (A := taint) (P := fun a b => (Done s₀ a ∧ Done s₀' b) ∧
      a.sp = s₀.sp ∧ b.sp = s₀'.sp) _
    (fun a b h => agree_of (by rw [h.2.1, h.2.2, qSp]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.s7, h.1.2.s7, fV, fV, qV]) t₅
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (r₃'.seq r₄))

theorem final_ct : ConstantTime isa ctrFinalRISCV64.pre ctrFinalRISCV64.pub cryptFinal :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem cryptFinal_verified : Verified RISCV64.target cryptFinal finalScratchContract :=
  Verified.of_correct final_correct final_ct final_implies

/-! ## With `save` on the stack

The final function has six argument words, so `save` is its seventh, in
`a6`: it runs its code in a frame of 80 bytes on the stack
(`withStackScratchWiped`), `save`'s 80 bytes (the registers, then the block
that held the last output block), which it zeroes before returning. The
code's calls use no stack, so 80 in all. -/

theorem frameSat_pre : ∃ s, (finalRoundsContract RISCV64.abi 80).pre s := by
  implies_sat [finalRoundsContract, Spec.Ctr.aesFinalSig, finalPre, finalPost, RISCV64.abi,
    RISCV64.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem cryptFinal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 80 .a6 10 cryptFinal)
      (finalRoundsContract RISCV64.abi 80) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Ctr.aesFinalSig) (nm := "save") (e := .u64) (n := 10)
    (pre := finalPre RISCV64.abi.ptrBits) (post := finalPost RISCV64.abi.ptrBits) (wa := false)
    (leak := some (finalLeak RISCV64.abi.ptrBits))
    (stack := 0) (bytes := 80) (words := 10) cryptFinal_verified (by decide) (by decide) (by decide)
    (finalPost_localOut _) frameSat_pre

end VG.Proof.AesCtr.RISCV64.Final
