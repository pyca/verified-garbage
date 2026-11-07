module

public import VerifiedGarbage.Impl.AesCfb.RISCV64.Final
public import VerifiedGarbage.Proof.AesCfb.Final
public import VerifiedGarbage.Proof.AesCfb.Spec
public import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.AesCfb.RISCV64.Verified
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Impl.AesCfb.RISCV64.Final
meta import VerifiedGarbage.Proof.AesCfb.Final
meta import VerifiedGarbage.Proof.AesCfb.Spec
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.StackScratch.RISCV64
meta import VerifiedGarbage.Proof.AesCfb.RISCV64.Verified
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
meta import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Proof.Modes.Words
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-CFB128 of a message's last piece on RISC-V

`encryptFinal_framed` and `decryptFinal_framed`: `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final` (`Impl/AesCfb/RISCV64/Final.lean`) meet
`Proof.AesCfb.encryptFinalRoundsContract` (and `decrypt…`), from which the
shared contracts follow (`Proof.AesCfb.encryptFinal_keyed`).

The code is proven against `finalRISCV64`, with a seventh argument `save`
(`a6`) for its return address and its caller's registers (`final_implies`:
the shared contract with it, `finalScratchContract`), as a caller of two
verified functions, through their contracts (`WP.call`, `blk_call`):

* `final_setup_wp`: the registers saved in `save`, and the arguments set up
  (`Setup`);
* `whole_wp`: the whole-block function of the same direction on the
  `n = len / 16` whole blocks, from its contract
  (`modeRISCV64 (cfbMode enc)`), with the regions it is given (`whole_pre`):
  the blocks and the chaining value the mode's (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, `vg_aes_encrypt_blocks`
  on the chaining value in place (`final_ivArgs_wp`, `final_ciph_wp`), and
  its first `u` bytes XORed into them by the modes' loop
  (`Modes.RISCV64.xorLoop_wp`, `final_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers restored from `save`, which nothing else
  wrote;
* `final_post`: `Done` gives `Spec.Cfb.EncryptFinal` (or `DecryptFinal`),
  by `Proof.AesCfb.encryptFinal_of`.

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
their contracts' constant time (`RelCT.callEx`, `blk_rel`), every address
and branch from the pointers and `len`, which agree in both runs.
`final_wp` and `final_rel` hold for any mode `M` of the whole-block
function, so AES-OFB's final function (`Proof/AesOfb/RISCV64/Final.lean`)
reuses them. `encryptFinal_framed` runs the code with `save` in a frame of 64 bytes on
the stack (`RISCV64.Verified.stackScratchWiped`), zeroed on return.
-/

@[expose] public section

namespace VG.Proof.AesCfb.RISCV64.Final

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesCfb.RISCV64 (final finalSaved finalMoves finalSetup finalRestore finalTail ivArgs)

/-! ## The code -/

/-- `vg_aes_cfb128_encrypt_final`, calling `vg_aes_cfb128_encrypt`. -/
abbrev encryptCode : Prog isa := Impl.AesCfb.RISCV64.encryptFinal

/-- `vg_aes_cfb128_decrypt_final`, calling `vg_aes_cfb128_decrypt`. -/
abbrev decryptCode : Prog isa := Impl.AesCfb.RISCV64.decryptFinal

/-! ## The contract -/

/-- The code's contract, with the arguments `(schedule = a0, rounds = a1,
iv = a2, data = a3, len = a4, scratch = a5, save = a6)`: in direction `enc`,
the data and the block at `iv` as `Spec.Cfb.EncryptFinal` (or
`DecryptFinal`) says, by AES with the key schedule it is given. -/
def finalRISCV64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let iv : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    let sv : Region := ⟨s.gpr .a6, 64⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr, sv] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint sv ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint sv ∧
      data.Disjoint scr ∧ data.Disjoint sv ∧ scr.Disjoint sv ∧
      (s.gpr .a0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      (s.gpr .a6).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat % 8 = 0 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .a0) (s.gpr .a1).toNat
    if enc then Spec.Cfb.EncryptFinal ciph 16 s.mem s'.mem (s.gpr .a2) (s.gpr .a3) (s.gpr .a4).toNat
    else Spec.Cfb.DecryptFinal ciph 16 s.mem s'.mem (s.gpr .a2) (s.gpr .a3) (s.gpr .a4).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp

/-- The postcondition in direction `enc`. -/
abbrev finalPost (enc : Bool) : Spec.Cfb.aesFinalSig.Post RISCV64.abi.ptrBits :=
  if enc then encryptFinalPost RISCV64.abi.ptrBits else decryptFinalPost RISCV64.abi.ptrBits

/-- The contract the frame needs: the shared one, with `save`, 64 bytes, as
a seventh argument, and no stack (a call keeps its return address in
`ra`). -/
abbrev finalScratchContract (enc : Bool) : Contract isa :=
  Sig.scratchContract RISCV64.abi Spec.Cfb.aesFinalSig "save" .u64 8 (finalPre RISCV64.abi.ptrBits)
    (finalPost enc) false 0

/-- A state satisfying the precondition. -/
def finalSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 0x3000 | .a5 => 0x4000 | .a6 => 0x6000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 64⟩]

theorem final_implies (enc : Bool) : (finalRISCV64 enc).Implies (finalScratchContract enc) := by
  cases enc <;>
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Cfb.aesFinalSig, finalPre, finalPost, encryptFinalPost, decryptFinalPost, finalRISCV64, RISCV64.abi,
    RISCV64.argRegs] [finalSat] using finalSat

/-! ## The arguments, by name -/

section
variable (s₀ : State)

abbrev fW : Addr := s₀.gpr .a0
abbrev fR : Nat := (s₀.gpr .a1).toNat
abbrev fIv : Addr := s₀.gpr .a2
abbrev fD : Addr := s₀.gpr .a3
abbrev fL : Nat := (s₀.gpr .a4).toNat
abbrev fS : Addr := s₀.gpr .a5
abbrev fV : Addr := s₀.gpr .a6
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
abbrev fSv : Region := ⟨fV s₀, 64⟩

/-- The key schedule, the chaining value and the whole blocks on entry. -/
abbrev fWk : List Byte := bytesAt s₀.mem (fW s₀) (16 * (fR s₀ + 1))
abbrev fIv0 : List Byte := bytesAt s₀.mem (fIv s₀) 16
abbrev fBlks : List (List Byte) := Spec.Cbc.blocksAt s₀.mem (fD s₀) (fN s₀)

/-- The memory once the registers are saved. -/
abbrev svMem : Mem := Spill.saveMem s₀.mem (fV s₀) s₀.gpr finalSaved

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [fSch s₀]
  wr : s₀.wr = [fIvR s₀, fData s₀, fScr s₀, fSv s₀]
  sch_iv : (fSch s₀).Disjoint (fIvR s₀)
  sch_data : (fSch s₀).Disjoint (fData s₀)
  sch_scr : (fSch s₀).Disjoint (fScr s₀)
  sch_sv : (fSch s₀).Disjoint (fSv s₀)
  iv_data : (fIvR s₀).Disjoint (fData s₀)
  iv_scr : (fIvR s₀).Disjoint (fScr s₀)
  iv_sv : (fIvR s₀).Disjoint (fSv s₀)
  data_scr : (fData s₀).Disjoint (fScr s₀)
  data_sv : (fData s₀).Disjoint (fSv s₀)
  scr_sv : (fScr s₀).Disjoint (fSv s₀)
  sch_wrap : (fW s₀).toNat + 240 ≤ 2 ^ 64
  iv_wrap : (fIv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (fD s₀).toNat + fL s₀ ≤ 2 ^ 64
  scr_wrap : (fS s₀).toNat + 2176 ≤ 2 ^ 64
  sv_wrap : (fV s₀).toNat + 64 ≤ 2 ^ 64
  sv_al : (fV s₀).toNat % 8 = 0
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem FPre.of {enc : Bool} {s₀ : State} (h : (finalRISCV64 enc).pre s₀) : FPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19⟩

/-! ## Regions -/

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)

theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl

theorem n_lt (s₀ : State) : fN s₀ < 2 ^ 64 := by
  have := (s₀.gpr .a4).isLt; have : fL s₀ = (s₀.gpr .a4).toNat := rfl; rw [fN_eq]; omega

theorem u_lt (s₀ : State) : fU s₀ < 16 := Nat.mod_lt _ (by decide)

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.blk_tail : (fBlk s₀).Disjoint (fTail s₀) := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  exact Offset.base_disjoint _ (Nat.le_refl _) (by rw [fN_eq, fU_eq]; omega)

theorem FPre.blk_wrap : (fD s₀).toNat + 16 * fN s₀ ≤ 2 ^ 64 := by
  have := hp.data_wrap; have := Nat.mul_div_le (fL s₀) 16; rw [fN_eq]; omega

theorem FPre.sched_sub : Region.Sub ⟨fW s₀, 16 * (fR s₀ + 1)⟩ (fSch s₀) :=
  Region.sub_prefix (by rcases hp.rounds with h | h | h <;> omega)

theorem FPre.sched_len : 16 * (fR s₀ + 1) ≤ 2 ^ 64 := by
  rcases hp.rounds with h | h | h <;> omega

end

/-- The `n` blocks at `D` are unchanged outside a frame that misses them. -/
theorem blocksAt_frame' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {D : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨D, 16 * n⟩ : Region).Disjoint r) :
    Spec.Cbc.blocksAt m' D n = Spec.Cbc.blocksAt m D n :=
  List.map_congr_left fun j hj => Proof.Cmac.bytesAt_frame hf
    (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by have := List.mem_range.mp hj; omega))) (by decide)

/-- The save changes only `save`. -/
theorem svMem_frame (s₀ : State) : Frame [fSv s₀] s₀.mem (svMem s₀) :=
  Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem saved_slots : ∀ p ∈ finalSaved, p.2 + 8 ≤ 64 := by decide
theorem saved_fits : ∀ p ∈ finalSaved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

/-! ## Saving the registers -/

open VG.RISCV64.Steps

/-- A register after an update, as a case on the register. -/
theorem upd_gpr {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) (r : Reg) :
    s'.gpr r = if r = d then v else s.gpr r := by
  by_cases h : r = d
  · subst h; rw [ite_eq_left rfl, u.gpr]
  · rw [ite_eq_right h, u.other r h]

theorem shr4 (x : BitVec 64) : x >>> 4 = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem shr4_shl4 (x : BitVec 64) : x >>> 4 <<< 4 = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem sub_shl4 (x : BitVec 64) : x - BitVec.ofNat 64 (16 * (x.toNat / 16)) = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The callee-saved registers kept for the caller that this code neither
saves nor uses. -/
abbrev Kept (s₀ s : State) : Prop :=
  ∀ r, r = .s0 ∨ r = .s8 ∨ r = .s9 ∨ r = .s10 ∨ r = .s11 → s.gpr r = s₀.gpr r

/-- What saving the registers and setting up the arguments leaves. -/
structure Setup (s₀ s : State) : Prop where
  s1 : s.gpr .s1 = fW s₀
  s4 : s.gpr .s4 = s₀.gpr .a1
  s5 : s.gpr .s5 = fIv s₀
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s6 : s.gpr .s6 = fS s₀
  s7 : s.gpr .s7 = fV s₀
  a0 : s.gpr .a0 = fW s₀
  a1 : s.gpr .a1 = s₀.gpr .a1
  a2 : s.gpr .a2 = fIv s₀
  a3 : s.gpr .a3 = fD s₀
  a4 : s.gpr .a4 = BitVec.ofNat 64 (fN s₀)
  a5 : s.gpr .a5 = fS s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  mem : s.mem = svMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

set_option linter.unusedSimpArgs false in
theorem final_setup_wp {s₀ : State} (hp : FPre s₀) : WP isa (.block finalSetup) s₀ (Setup s₀) := by
  have hw : ∀ p ∈ finalSaved, InRegions s₀.wr (s₀.gpr .a6 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [hp.wr]
    have := saved_slots p hp'
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
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

/-! ## The call of the whole-block function -/

open VG.Proof.AesCbc (Mode cts aesWith_state)
open VG.Proof.AesCbc.RISCV64 (modeRISCV64 CallPre CallPost blk_call)

theorem callEntry (s : State) {r : Reg} (h : r ∉ linkRegs) : s.callEntry.gpr r = s.gpr r :=
  s.callEntry_gpr h

/-- The registers that hold their values across a call. -/
theorem cs_of {s s' : State} (h : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (r : Reg)
    (hr : r = .s0 ∨ r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4 ∨ r = .s5 ∨ r = .s6 ∨ r = .s7 ∨ r = .s8 ∨
      r = .s9 ∨ r = .s10 ∨ r = .s11) : s'.gpr r = s.gpr r :=
  h r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- What the call of the whole-block function leaves, for the mode `M`. -/
structure Whole (M : Mode) (s₀ s : State) : Prop where
  s1 : s.gpr .s1 = fW s₀
  s4 : s.gpr .s4 = s₀.gpr .a1
  s5 : s.gpr .s5 = fIv s₀
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s6 : s.gpr .s6 = fS s₀
  s7 : s.gpr .s7 = fV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fBlk s₀, fScr s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  iv : bytesAt s.mem (fIv s₀) 16 = M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)

theorem toNat_n (s₀ : State) : (BitVec.ofNat 64 (fN s₀)).toNat = fN s₀ := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (n_lt s₀)]

/-- The whole-block function's precondition at the call, with the regions it
is given, which ours cover. -/
theorem whole_pre {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Setup s₀ s) :
    (modeRISCV64 M).pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, fBlk s₀, fScr s₀]) ∧
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

theorem whole_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeRISCV64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 M).post s s')
    (nf : whole.noFrames = true) {s₀ : State} (hp : FPre s₀) {s : State} (h : Setup s₀ s) :
    WP isa (.call name whole) s (Whole M s₀) := by
  have ef := svMem_frame s₀
  have eW : bytesAt (svMem s₀) (fW s₀) (16 * (fR s₀ + 1)) = fWk s₀ :=
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.sch_sv.sub_left hp.sched_sub) hp.sched_len
  have eIv : bytesAt (svMem s₀) (fIv s₀) 16 = fIv0 s₀ :=
    Proof.Cmac.bytesAt_frame ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_sv) (by decide)
  have eB : Spec.Cbc.blocksAt (svMem s₀) (fD s₀) (fN s₀) = fBlks s₀ :=
    blocksAt_frame' ef (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.data_sv.sub_left (blk_sub s₀))
  obtain ⟨hpre, hc, hw⟩ := whole_pre (M := M) hp h
  refine WP.call (k := modeRISCV64 M) hv (rd := [fSch s₀]) (wr := [fIvR s₀, fBlk s₀, fScr s₀]) hpre hc hw ?_ nf
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

/-! ## The partial last segment -/

theorem eval_u {M : Mode} {s₀ s : State} (h : Whole M s₀ s) :
    isa.eval (.zero .s3) s = some (decide (fU s₀ = 0)) :=
  eval_zero_ofNat s .s3 (by have := u_lt s₀; omega) h.s3

theorem bytesAt_getD (m : Mem) (p : Addr) {n q : Nat} (hq : q < n) :
    (bytesAt m p n).getD q 0 = m (p + BitVec.ofNat 64 q) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hq]

/-- What the function leaves before restoring the registers. -/
structure Done (M : Mode) (s₀ s : State) : Prop where
  s7 : s.gpr .s7 = fV s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tail : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q) ^^^
    (Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))).getD q 0
  iv : bytesAt s.mem (fIv s₀) 16 = if fU s₀ = 0 then M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
    else Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))

theorem Whole.frame' {M : Mode} {s₀ s : State} (h : Whole M s₀ s) :
    Frame [fIvR s₀, fData s₀, fScr s₀] (svMem s₀) s.mem :=
  h.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨fData s₀, by simp, blk_sub s₀⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem done_of_zero {M : Mode} {s₀ s : State} (h : Whole M s₀ s) (hu : fU s₀ = 0) : Done M s₀ s :=
  ⟨h.s7, h.kept, h.rd, h.wr, h.frame', h.blocks, fun q hq => absurd hq (by omega),
    by rw [ite_eq_left hu]; exact h.iv⟩

/-- Everything the function writes, from entry. -/
theorem big_frame {s₀ : State} {m : Mem} (hf : Frame [fIvR s₀, fData s₀, fScr s₀] (svMem s₀) m) :
    Frame [fIvR s₀, fData s₀, fScr s₀, fSv s₀] s₀.mem m :=
  ((svMem_frame s₀).mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
    (hf.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h <;> simp [h])

theorem FPre.sched_big {s₀ : State} (hp : FPre s₀) :
    ∀ r ∈ [fIvR s₀, fData s₀, fScr s₀, fSv s₀], (⟨fW s₀, 16 * (fR s₀ + 1)⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.sch_iv.sub_left hp.sched_sub
  · exact hp.sch_data.sub_left hp.sched_sub
  · exact hp.sch_scr.sub_left hp.sched_sub
  · exact hp.sch_sv.sub_left hp.sched_sub

theorem a1_ofNat (s₀ : State) : s₀.gpr .a1 = BitVec.ofNat 64 (fR s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [fR]

/-- What the arguments of the call of the block function leave. -/
structure IvA (M : Mode) (s₀ s : State) : Prop where
  whole : Whole M s₀ s
  pre : CallPre s (fW s₀) (fIv s₀) (fS s₀) (fR s₀)

set_option linter.unusedSimpArgs false in
theorem final_ivArgs_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.block ivArgs) s (IvA M s₀) := by
  unfold ivArgs Impl.AesCbc.RISCV64.mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_li (imm := 1) (by decide) fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ?_
  have c (r : Reg) (hr : r = .s0 ∨ r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4 ∨ r = .s5 ∨ r = .s6 ∨ r = .s7 ∨
      r = .s8 ∨ r = .s9 ∨ r = .s10 ∨ r = .s11) : s₅.gpr r = s.gpr r := by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
  have sp : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have mem : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨⟨by rw [c .s1 (by simp), h.s1], by rw [c .s4 (by simp), h.s4],
    by rw [c .s5 (by simp), h.s5], by rw [c .s2 (by simp), h.s2], by rw [c .s3 (by simp), h.s3],
    by rw [c .s6 (by simp), h.s6], by rw [c .s7 (by simp), h.s7],
    fun r hr => by rw [c r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem]; exact h.frame, by rw [mem]; exact h.blocks,
    by rw [mem]; exact h.iv⟩, ?_⟩
  exact {
    a0 := by simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; exact h.s1
    a1 := by simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; rw [h.s4, a1_ofNat]
    a2 := by simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; exact h.s5
    a3 := by simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte] <;> rfl
    a4 := by simp only [upd_gpr u₅, upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; exact h.s6
    rounds := hp.rounds
    wd := hp.sch_iv
    ws := hp.sch_scr.sub_right (Region.sub_prefix (by decide))
    ds := hp.iv_scr.sub_right (Region.sub_prefix (by decide))
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
  s5 : s.gpr .s5 = fIv s₀
  s2 : s.gpr .s2 = fT s₀
  s3 : s.gpr .s3 = BitVec.ofNat 64 (fU s₀)
  s7 : s.gpr .s7 = fV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tailb : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q)
  iv : bytesAt s.mem (fIv s₀) 16 =
    Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))

theorem final_ciph_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State}
    (h : IvA M s₀ s) :
    WP isa (.call "vg_aes_encrypt_blocks" Impl.Aes.RISCV64.encryptBlocks) s (Ciph M s₀) := by
  obtain ⟨hw, hc⟩ := h
  refine WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct AesCbc.RISCV64.encryptBlocks_noFrames hc)
    fun s' c => ?_
  have cs := cs_of c.saved
  have fc : Frame [fIvR s₀, fData s₀, fScr s₀] s.mem s'.mem :=
    c.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨fScr s₀, by simp, Region.sub_prefix (by decide)⟩
  have big := big_frame hw.frame'
  have tailD : ∀ r ∈ [fIvR s₀, (⟨fS s₀, 2048⟩ : Region)], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
    · exact (hp.data_scr.sub_left (tail_sub s₀)).sub_right (Region.sub_prefix (by decide))
  have tailW : ∀ r ∈ [fIvR s₀, fBlk s₀, fScr s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.iv_data.sub_right (tail_sub s₀)).symm
    · exact hp.blk_tail.symm
    · exact hp.data_scr.sub_left (tail_sub s₀)
  have tailS : ∀ r ∈ [fSv s₀], (fTail s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.data_sv.sub_left (tail_sub s₀)
  have hlen : (fTail s₀).len ≤ 2 ^ 64 := by
    show fU s₀ ≤ 2 ^ 64; have := u_lt s₀; omega
  refine ⟨by rw [cs .s5 (by simp), hw.s5], by rw [cs .s2 (by simp), hw.s2],
    by rw [cs .s3 (by simp), hw.s3], by rw [cs .s7 (by simp), hw.s7],
    fun r hr => by rw [cs r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp), hw.kept r hr],
    by rw [c.sp, hw.sp], by rw [c.rd, hw.rd], by rw [c.wr, hw.wr], hw.frame'.trans fc, ?_, fun q hq => ?_, ?_⟩
  · rw [blocksAt_frame' c.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.iv_data.symm.sub_left (blk_sub s₀)
      · exact (hp.data_scr.sub_left (blk_sub s₀)).sub_right (Region.sub_prefix (by decide))]
    exact hw.blocks
  · rw [c.frame.bytes tailD hlen hq, hw.frame.bytes tailW hlen hq, (svMem_frame s₀).bytes tailS hlen hq]
  · rw [c.out, ← aesWith_state, Proof.Cmac.bytesAt_frame big hp.sched_big hp.sched_len, hw.iv]

theorem toNat_tail {s₀ : State} (hp : FPre s₀) (hu : fU s₀ ≠ 0) : (fT s₀).toNat = (fD s₀).toNat + 16 * fN s₀ := by
  have := hp.data_wrap
  have := Nat.div_add_mod (fL s₀) 16
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * fN s₀) (by omega),
    Nat.mod_eq_of_lt (by omega)]

open VG.Proof.Modes.RISCV64 (XPre XInv xorLoop_wp xf)

theorem final_xor_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Ciph M s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block [Impl.AesCbc.RISCV64.mov .t2 .s5])
      (.loop (.block Impl.Modes.RISCV64.xorStep) (.nonzero .s3))) s (Done M s₀) := by
  unfold Impl.AesCbc.RISCV64.mov
  refine WP.seq (wp_mv fun s₁ u₁ => WP.block_nil ?_)
  have hU := u_lt s₀
  have hT := toNat_tail hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hIw := hp.iv_wrap
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have xp : XPre s₁ (fIv s₀) (fT s₀) (fU s₀) := {
    pos := by omega
    fK := by omega
    fR := by omega
    disj := (hp.iv_data.sub_left (Region.sub_prefix (by omega))).sub_right (tail_sub s₀)
    rdK := fun q hq => by
      rw [u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]
      exact ⟨fIvR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    wrR := fun q hq => by
      rw [u₁.wr, h.wr, hp.wr]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show fT s₀ + BitVec.ofNat 64 q = fD s₀ + BitVec.ofNat 64 (16 * fN s₀ + q) from Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega) }
  have x0 : XInv s₁ (fIv s₀) (fT s₀) (fU s₀) 0 s₁ := {
    t2 := by rw [u₁.gpr, h.s5]; exact (BitVec.add_zero _).symm
    s2 := by rw [u₁.other _ (by decide), h.s2]; exact (BitVec.add_zero _).symm
    s3 := by rw [u₁.other _ (by decide), h.s3, Nat.sub_zero]
    lt := by omega
    mem := (Proof.Modes.over_zero _ _ _).symm
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (xorLoop_wp xp x0) fun s' d => ?_
  have ivT : ∀ r ∈ [fTail s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.sub_right (tail_sub s₀)
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
  · exact h.frame.trans (fr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact h.blocks
  · rw [d.mem, Proof.Modes.over_at hq (by omega), xf, u₁.mem, h.tailb q hq,
      ← bytesAt_getD s.mem (fIv s₀) (show q < 16 by omega), h.iv]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame fr ivT (by decide), h.iv]

theorem final_mid_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.ite (.zero .s3) (.block []) finalTail) s (Done M s₀) := by
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [eval_u h, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [eval_u h, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (final_ivArgs_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (final_ciph_wp hp h₁) fun _ h₂ => final_xor_wp hp h₂ hu))

/-! ## Restoring the registers -/

theorem final_end_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Done M s₀ s) :
    WP isa (.block finalRestore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧ s'.mem = s.mem := by
  have hs : Spill.Saved (fV s₀) s₀.gpr finalSaved s.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (fV s₀) s₀.gpr).frame h.frame fun p hp' r hr => by
      have hsub : Region.Sub ⟨fV s₀ + BitVec.ofNat 64 p.2, 8⟩ (fSv s₀) := Offset.sub_base _ (saved_slots p hp')
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_sv.symm.sub_left hsub
      · exact hp.data_sv.symm.sub_left hsub
      · exact hp.scr_sv.symm.sub_left hsub
  show WP isa (.block (Spill.restoreCode .s7 finalSaved)) _ _
  refine WP.mono (Spill.restore_wp hp.sv_al h.s7 saved_fits (by decide) (fun p hp' => ?_) hs)
    fun s' r => ⟨fun q hq => r.gpr_of ?_, r.gpr (.ra, 0) (by decide), r.mem⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inl (by decide)
      | exact .inr (h.kept _ (by simp))

/-! ## The whole function -/

theorem final_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeRISCV64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 M).post s s')
    (nf : whole.noFrames = true) {s₀ : State} (hp : FPre s₀) :
    WP isa (final name whole) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        ∃ s₁, Done M s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hv nf hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_mid_wp hp h₂) fun s₃ h₃ => ?_)
  exact WP.mono (final_end_wp hp h₃) fun _ ⟨g, ra, m⟩ => ⟨g, ra, s₃, h₃, m⟩

/-- The specification's results, from what the function leaves. -/
theorem final_post {enc : Bool} {s₀ s₁ s' : State} (h : Done (cfbMode enc) s₀ s₁) (hm : s'.mem = s₁.mem) :
    (finalRISCV64 enc).post s₀ s' := by
  cases enc
  · show Spec.Cfb.DecryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
    exact decryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)
  · show Spec.Cfb.EncryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
    exact encryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)

theorem final_correct {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeRISCV64 (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 (cfbMode enc)).post s s')
    (nf : whole.noFrames = true) (s : State) (hs : (finalRISCV64 enc).pre s) :
    ∃ t s', Exec isa (final name whole) s t s' ∧ abiPreserved s s' ∧ (finalRISCV64 enc).post s s' := by
  obtain ⟨t, s', he, hg, hra, s₁, h₁, hm⟩ := final_wp hv nf (FPre.of hs)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, final_post h₁ hm⟩

/-! ## The code's properties -/

theorem encrypt_noFrames : Impl.AesCfb.RISCV64.encrypt.noFrames = true := rfl

theorem decrypt_noFrames : Impl.AesCfb.RISCV64.decrypt.noFrames = true := rfl

/-! ## Constant time -/

theorem agree_of {s₁ s₂ : State} {rs : List Reg} (hsp : s₁.sp = s₂.sp) (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (Taint.mem_ofRegs.mp hr)⟩

theorem final_rel {enc : Bool} {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeRISCV64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 M).post s s')
    (hct : ConstantTime isa (modeRISCV64 M).pre (modeRISCV64 M).pub whole)
    (nf : whole.noFrames = true) {s₀ s₀' : State}
    (h0 : (finalRISCV64 enc).pre s₀) (h0' : (finalRISCV64 enc).pre s₀') (hq : (finalRISCV64 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (final name whole) fun _ _ => True := by
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  obtain ⟨qW, qR, qIv, qD, qL, qS, qV, qSp⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, fD, qD, qN]
  -- The registers saved and the arguments set up.
  obtain ⟨_, t₁⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5, .a6])
      (.block finalSetup) h).isSome = true := ⟨_, by taint_decide⟩
  have r₁ := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine agree_of qSp fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) t₁).wp
    (F₁ := Setup s₀) (F₂ := Setup s₀')
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨final_setup_wp hp, final_setup_wp hp'⟩
  -- The whole blocks.
  have r₂ := (RelCT.callEx (k := modeRISCV64 M) (n := name) hv hct
    (P := fun a b => Setup s₀ a ∧ Setup s₀' b) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre (M := M) hp ha
      obtain ⟨pb, cb, wb⟩ := whole_pre (M := M) hp' hb
      refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb⟩
      simp only [modeRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        callEntry a (by decide : Reg.a0 ∉ linkRegs), callEntry a (by decide : Reg.a1 ∉ linkRegs),
        callEntry a (by decide : Reg.a2 ∉ linkRegs), callEntry a (by decide : Reg.a3 ∉ linkRegs),
        callEntry a (by decide : Reg.a4 ∉ linkRegs), callEntry a (by decide : Reg.a5 ∉ linkRegs),
        callEntry b (by decide : Reg.a0 ∉ linkRegs), callEntry b (by decide : Reg.a1 ∉ linkRegs),
        callEntry b (by decide : Reg.a2 ∉ linkRegs), callEntry b (by decide : Reg.a3 ∉ linkRegs),
        callEntry b (by decide : Reg.a4 ∉ linkRegs), callEntry b (by decide : Reg.a5 ∉ linkRegs),
        ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.sp, hb.a0, hb.a1, hb.a2, hb.a3, hb.a4, hb.a5, hb.sp]
      rw [fW, fW, fIv, fIv, fD, fD, fS, fS, qW, qR, qIv, qD, qS, qSp, qN]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).wp
    (F₁ := Whole M s₀) (F₂ := Whole M s₀')
    fun a b h => ⟨whole_wp hv nf hp h.1, whole_wp hv nf hp' h.2⟩
  -- The partial last segment.
  obtain ⟨_, t₃⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s4, .s5, .s6])
      (.block ivArgs) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, t₄⟩ : ∃ h, (taint.check (Taint.ofRegs [.s5, .s2, .s3])
      (.seq (.block [Impl.AesCbc.RISCV64.mov .t2 .s5])
        (.loop (.block Impl.Modes.RISCV64.xorStep) (.nonzero .s3))) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole M s₀ a ∧ Whole M s₀' b)
      finalTail fun a b => Done M s₀ a ∧ Done M s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₃ := (RelCT.taint (A := taint)
      (P := fun a b => Whole M s₀ a ∧ Whole M s₀' b) _
      (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.1.s1, h.2.s1, fW, fW, qW]
        · rw [h.1.s4, h.2.s4, qR]
        · rw [h.1.s5, h.2.s5, fIv, fIv, qIv]
        · rw [h.1.s6, h.2.s6, fS, fS, qS]) t₃).wp
      (F₁ := IvA M s₀) (F₂ := IvA M s₀')
      fun a b h => ⟨final_ivArgs_wp hp h.1, final_ivArgs_wp hp' h.2⟩
    have a₄ := (AesCbc.RISCV64.blk_rel (name := "vg_aes_encrypt_blocks")
      Proof.Aes.RISCV64.encryptBlocks_correct Proof.Aes.RISCV64.encryptBlocks_ct
      (P := fun a b => IvA M s₀ a ∧ IvA M s₀' b)
      fun a b h => by
        have e₂ := h.2.pre
        have eW : fW s₀' = fW s₀ := qW.symm
        have eIv : fIv s₀' = fIv s₀ := qIv.symm
        have eS : fS s₀' = fS s₀ := qS.symm
        have eR : fR s₀' = fR s₀ := by simp only [fR, qR]
        rw [eW, eIv, eS, eR] at e₂
        exact ⟨h.1.pre, e₂, by rw [h.1.whole.sp, h.2.whole.sp, qSp]⟩).wp
      (F₁ := Ciph M s₀) (F₂ := Ciph M s₀')
      fun a b h => ⟨final_ciph_wp hp h.1, final_ciph_wp hp' h.2⟩
    have a₅ := (RelCT.taint (A := taint)
      (P := fun a b => Ciph M s₀ a ∧ Ciph M s₀' b) _
      (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.s5, h.2.s5, fIv, fIv, qIv]
        · rw [h.1.s2, h.2.s2, qT]
        · rw [h.1.s3, h.2.s3, qU]) t₄).wp
      (F₁ := Done M s₀) (F₂ := Done M s₀')
      fun a b h => ⟨final_xor_wp hp h.1 hu, final_xor_wp hp' h.2 hu'⟩
    exact (a₃.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((a₄.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₅.mono (fun _ _ h => h) fun _ _ h => h.2))
  have r₃ : RelCT isa (fun a b => Whole M s₀ a ∧ Whole M s₀' b)
      (.ite (.zero .s3) (.block []) finalTail)
      (fun a b => Done M s₀ a ∧ Done M s₀' b) := by
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
  obtain ⟨_, t₅⟩ : ∃ h, (taint.check (Taint.ofRegs [.s7]) (.block finalRestore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have r₄ := RelCT.taint (A := taint) (P := fun a b => (Done M s₀ a ∧ Done M s₀' b) ∧
      a.sp = s₀.sp ∧ b.sp = s₀'.sp) _
    (fun a b h => agree_of (by rw [h.2.1, h.2.2, qSp]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.s7, h.1.2.s7, fV, fV, qV]) t₅
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (r₃'.seq r₄))

theorem final_ct {enc : Bool} {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeRISCV64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeRISCV64 M).post s s')
    (hct : ConstantTime isa (modeRISCV64 M).pre (modeRISCV64 M).pub whole)
    (nf : whole.noFrames = true) :
    ConstantTime isa (finalRISCV64 enc).pre (finalRISCV64 enc).pub (final name whole) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel hv hct nf h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem encryptFinal_verified : Verified RISCV64.target encryptCode (finalScratchContract true) :=
  Verified.of_correct (final_correct encrypt_correct encrypt_noFrames)
    (final_ct (enc := true) encrypt_correct encrypt_ct encrypt_noFrames) (final_implies true)

theorem decryptFinal_verified : Verified RISCV64.target decryptCode (finalScratchContract false) :=
  Verified.of_correct (final_correct decrypt_correct decrypt_noFrames)
    (final_ct (enc := false) decrypt_correct decrypt_ct decrypt_noFrames) (final_implies false)

/-! ## With `save` on the stack

The final functions have six argument words, so `save` is their seventh,
in `a6`: they run their code in a frame of 64 bytes on the stack
(`withStackScratchWiped`), `save`'s 64 bytes, which it zeroes before
returning. The code's calls use no stack, so 64 in all. -/

/-- A state satisfying the shared contracts' precondition. -/
def finalFrameSat : State := { finalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩] }

theorem encFrameSat_pre : ∃ s, (encryptFinalRoundsContract RISCV64.abi 64).pre s := by
  implies_sat [encryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, encryptFinalPost, RISCV64.abi,
    RISCV64.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem decFrameSat_pre : ∃ s, (decryptFinalRoundsContract RISCV64.abi 64).pre s := by
  implies_sat [decryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, decryptFinalPost, RISCV64.abi,
    RISCV64.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem encryptFinal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 encryptCode)
      (encryptFinalRoundsContract RISCV64.abi 64) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre RISCV64.abi.ptrBits) (post := encryptFinalPost RISCV64.abi.ptrBits) (wa := false)
    (stack := 0) (bytes := 64) (words := 8) encryptFinal_verified (by decide) (by decide) (by decide)
    (encryptFinalPost_localOut _) encFrameSat_pre

theorem decryptFinal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchWiped 64 .a6 8 decryptCode)
      (decryptFinalRoundsContract RISCV64.abi 64) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre RISCV64.abi.ptrBits) (post := decryptFinalPost RISCV64.abi.ptrBits) (wa := false)
    (stack := 0) (bytes := 64) (words := 8) decryptFinal_verified (by decide) (by decide) (by decide)
    (decryptFinalPost_localOut _) decFrameSat_pre

end VG.Proof.AesCfb.RISCV64.Final
