module

public import VerifiedGarbage.Impl.AesCfb.AArch64.Final
public import VerifiedGarbage.Proof.AesCfb.Final
public import VerifiedGarbage.Proof.AesCfb.AArch64.Verified
public import VerifiedGarbage.Proof.AesCfb.AArch64.Caller
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.StackScratch.AArch64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesOfb.AArch64.Body
import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.AArch64.Xor
import VerifiedGarbage.Proof.AesCfb.AArch64.Body
import VerifiedGarbage.Proof.AesCbc.AArch64.Block
import VerifiedGarbage.Proof.AesCbc.AArch64.CT
import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Verified
import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Lit
meta import VerifiedGarbage.Impl.AesCfb.AArch64.Final
meta import VerifiedGarbage.Proof.AesCfb.Final
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Verified
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Caller
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Impl.StackScratch.AArch64
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesOfb.AArch64.Body
meta import VerifiedGarbage.Proof.Modes.AArch64.FbFinal
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.Xor
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Body
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Block
meta import VerifiedGarbage.Proof.AesCbc.AArch64.CT
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Verified
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# AES-CFB128 of a message's last piece on AArch64

`encryptFinal_framed` and `decryptFinal_framed`: `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final` (`Impl/AesCfb/AArch64/Final.lean`), for any
implementation `v` of the block functions (`BlocksImpl`), meet
`Proof.AesCfb.encryptFinalRoundsContract` (and `decrypt…`), from which the
shared contracts follow (`Proof.AesCfb.encryptFinal_keyed`). Decryption calls
the whole-block code its registration emits for `v` (`Caller.decrypt`,
`decryptCode`).

The code is proven against `finalAArch64`, with a seventh argument `save`
(`x6`) for its caller's registers and its return address (`final_implies`:
the shared contract with it, `finalScratchContract`), as a caller of two
verified functions, through their contracts (`WP.call`, `blk_call`):

* `final_setup_wp`: the registers saved in `save`, and the arguments set up
  (`Setup`);
* `whole_wp`: the whole-block function of the same direction and variant on
  the `n = len / 16` whole blocks, from its contract
  (`modeAArch64 (cfbMode enc)`), with the regions it is given (`whole_pre`):
  the blocks and the chaining value the mode's (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, the block function on
  the chaining value in place (`final_ivArgs_wp`, `final_ciph_wp`), and its
  first `u` bytes XORed into them by the modes' loop
  (`Modes.AArch64.xorLoop_wp`, `final_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers restored from `save`, which nothing else
  wrote;
* `final_post`: `Done` gives `Spec.Cfb.EncryptFinal` (or `DecryptFinal`),
  by `Proof.AesCfb.encryptFinal_of`.

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
their contracts' constant time (`RelCT.callEx`, `blk_rel`), every address
and branch from the pointers and `len`, which agree in both runs.
`encryptFinal_framed` runs the code with `save` in a frame of 64 bytes on
the stack (`AArch64.Verified.stackScratchWiped`), zeroed on return.
-/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Final

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Impl.AesCfb.AArch64 (final finalSaved finalMoves finalSetup finalRestore finalTail)

/-! ## The code -/

/-- `vg_aes_cfb128_encrypt_final` for the implementation `v`, calling
`vg_aes_cfb128_encrypt` of the same suffix. -/
def encryptCode (v : BlocksImpl) : Prog isa := Impl.AesCfb.AArch64.encryptFinal v.enc v.suffix

/-- `vg_aes_cfb128_decrypt_final` for the implementation `v`, calling
`vg_aes_cfb128_decrypt` of the same suffix, whose code is the one its
registration emits (`Caller.decrypt`). -/
def decryptCode (v : BlocksImpl) : Prog isa :=
  final ("vg_aes_cfb128_decrypt" ++ v.suffix) (Caller.decrypt v) v.enc

/-! ## The contract -/

/-- The code's contract, with the arguments `(schedule = x0, rounds = x1,
iv = x2, data = x3, len = x4, scratch = x5, save = x6)`: in direction `enc`,
the data and the block at `iv` as `Spec.Cfb.EncryptFinal` (or
`DecryptFinal`) says, by AES with the key schedule it is given. -/
def finalAArch64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let iv : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2176⟩
    let sv : Region := ⟨s.gpr .x6, 64⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr, sv] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint sv ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint sv ∧
      data.Disjoint scr ∧ data.Disjoint sv ∧ scr.Disjoint sv ∧
      (s.gpr .x0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 2176 ≤ 2 ^ 64 ∧
      (s.gpr .x6).toNat + 64 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .x0) (s.gpr .x1).toNat
    if enc then Spec.Cfb.EncryptFinal ciph 16 s.mem s'.mem (s.gpr .x2) (s.gpr .x3) (s.gpr .x4).toNat
    else Spec.Cfb.DecryptFinal ciph 16 s.mem s'.mem (s.gpr .x2) (s.gpr .x3) (s.gpr .x4).toNat
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
      s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp

/-- The postcondition in direction `enc`. -/
abbrev finalPost (enc : Bool) : Spec.Cfb.aesFinalSig.Post AArch64.abi.ptrBits :=
  if enc then encryptFinalPost AArch64.abi.ptrBits else decryptFinalPost AArch64.abi.ptrBits

/-- The contract the frame needs: the shared one, with `save`, 64 bytes, as
a seventh argument, and no stack (a call keeps its return address in
`x30`). -/
abbrev finalScratchContract (enc : Bool) : Contract isa :=
  Sig.scratchContract AArch64.abi Spec.Cfb.aesFinalSig "save" .u64 8 (finalPre AArch64.abi.ptrBits)
    (finalPost enc) false 0

/-- A state satisfying the precondition. -/
def finalSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 0x3000 | .x5 => 0x4000 | .x6 => 0x6000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 64⟩]

theorem final_implies (enc : Bool) : (finalAArch64 enc).Implies (finalScratchContract enc) := by
  cases enc <;>
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Cfb.aesFinalSig, finalPre, finalPost, encryptFinalPost, decryptFinalPost, finalAArch64, AArch64.abi,
    AArch64.argRegs] [finalSat] using finalSat

/-! ## The arguments, by name -/

section
variable (s₀ : State)

abbrev fW : Addr := s₀.gpr .x0
abbrev fR : Nat := (s₀.gpr .x1).toNat
abbrev fIv : Addr := s₀.gpr .x2
abbrev fD : Addr := s₀.gpr .x3
abbrev fL : Nat := (s₀.gpr .x4).toNat
abbrev fS : Addr := s₀.gpr .x5
abbrev fV : Addr := s₀.gpr .x6
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
  iv_wrap : (fIv s₀).toNat + 16 ≤ 2 ^ 64
  data_wrap : (fD s₀).toNat + fL s₀ ≤ 2 ^ 64
  scr_wrap : (fS s₀).toNat + 2176 ≤ 2 ^ 64
  sv_wrap : (fV s₀).toNat + 64 ≤ 2 ^ 64
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem FPre.of {enc : Bool} {s₀ : State} (h : (finalAArch64 enc).pre s₀) : FPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, _, a14, a15, a16, a17, a18⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a14, a15, a16, a17, a18⟩

/-! ## Regions -/

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)

theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl

theorem n_lt (s₀ : State) : fN s₀ < 2 ^ 64 := by
  have := (s₀.gpr .x4).isLt; have : fL s₀ = (s₀.gpr .x4).toNat := rfl; rw [fN_eq]; omega

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
theorem saved_fits : ∀ p ∈ finalSaved, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

/-! ## Saving the registers -/

open VG.AArch64.RegUpd

theorem moves_ok (s : State) :
    ∃ s', runBlock isa finalMoves s = some s' ∧
      s'.gpr .x19 = s.gpr .x0 ∧ s'.gpr .x20 = s.gpr .x1 ∧ s'.gpr .x21 = s.gpr .x2 ∧
      s'.gpr .x24 = s.gpr .x5 ∧ s'.gpr .x25 = s.gpr .x6 ∧
      s'.gpr .x22 = s.gpr .x3 + (s.gpr .x4 >>> 4 <<< 4) ∧ s'.gpr .x23 = s.gpr .x4 - (s.gpr .x4 >>> 4 <<< 4) ∧
      s'.gpr .x4 = s.gpr .x4 >>> 4 ∧
      (∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → r ≠ .x25 → r ≠ .x4 →
        r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [finalMoves, Impl.AesCbc.AArch64.mov], ?_⟩
  refine ⟨by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    by simp [gpr_write], by simp [gpr_write], by simp [gpr_write], by simp [gpr_write],
    fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ => ?_, rfl, rfl, rfl, rfl⟩
  simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀]

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

/-- The registers kept for the caller that this code neither saves nor uses. -/
abbrev Kept (s₀ s : State) : Prop := ∀ r, r = .x26 ∨ r = .x27 ∨ r = .x28 → s.gpr r = s₀.gpr r

/-- What saving the registers and setting up the arguments leaves. -/
structure Setup (s₀ s : State) : Prop where
  x19 : s.gpr .x19 = fW s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = fIv s₀
  x22 : s.gpr .x22 = fT s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (fU s₀)
  x24 : s.gpr .x24 = fS s₀
  x25 : s.gpr .x25 = fV s₀
  x0 : s.gpr .x0 = fW s₀
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = fIv s₀
  x3 : s.gpr .x3 = fD s₀
  x4 : s.gpr .x4 = BitVec.ofNat 64 (fN s₀)
  x5 : s.gpr .x5 = fS s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  mem : s.mem = svMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem final_setup_wp {s₀ : State} (hp : FPre s₀) : WP isa (.block finalSetup) s₀ (Setup s₀) := by
  have hw : ∀ p ∈ finalSaved, InRegions s₀.wr (s₀.gpr .x6 + BitVec.ofNat 64 p.2) 8 := by
    intro p hp'
    rw [hp.wr]
    have := saved_slots p hp'
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  show WP isa (.block (Spill.saveCode .x6 finalSaved ++ finalMoves)) _ _
  refine Spill.save_ok saved_fits hw ?_
  refine WP.mono (WP.of_runBlock (moves_ok _))
    fun s' ⟨x19, x20, x21, x24, x25, x22, x23, x4, keep, sp, mem, rd, wr⟩ => ?_
  have k (r : Reg) (h₁ : r ≠ .x19) (h₂ : r ≠ .x20) (h₃ : r ≠ .x21) (h₄ : r ≠ .x22) (h₅ : r ≠ .x23)
      (h₆ : r ≠ .x24) (h₇ : r ≠ .x25) (h₈ : r ≠ .x4) (h₉ : r ≠ .x9) (h₁₀ : r ≠ .x10) :
      s'.gpr r = s₀.gpr r := keep r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀
  exact ⟨x19, x20, x21, by rw [x22, shr4_shl4], by rw [x23, shr4_shl4, sub_shl4], x24, x25,
    k .x0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    k .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    k .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    k .x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    by rw [x4, shr4],
    k .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    fun r hr => by
      rcases hr with rfl | rfl | rfl <;>
        exact k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide),
    sp, mem, rd, wr⟩

/-! ## The call of the whole-block function -/

open VG.Proof.AesCbc (Mode cts aesWith_state)
open VG.Proof.AesCbc.AArch64 (modeAArch64 CallPre CallPost blk_call callEntry_x0 callEntry_x1 callEntry_x2
  callEntry_x3 callEntry_x4)

theorem callEntry_x5 (s : State) : s.callEntry.gpr .x5 = s.gpr .x5 := s.callEntry_gpr (by decide)

/-- The registers that hold their values across a call. -/
theorem cs_of {s s' : State} (h : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (r : Reg)
    (hr : r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24 ∨ r = .x25 ∨ r = .x26 ∨ r = .x27 ∨
      r = .x28) : s'.gpr r = s.gpr r :=
  h r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- What the call of the whole-block function leaves, for the mode `M`. -/
structure Whole (M : Mode) (s₀ s : State) : Prop where
  x19 : s.gpr .x19 = fW s₀
  x20 : s.gpr .x20 = s₀.gpr .x1
  x21 : s.gpr .x21 = fIv s₀
  x22 : s.gpr .x22 = fT s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (fU s₀)
  x24 : s.gpr .x24 = fS s₀
  x25 : s.gpr .x25 = fV s₀
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
    (modeAArch64 M).pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, fBlk s₀, fScr s₀]) ∧
      Covers ([fSch s₀] ++ [fIvR s₀, fBlk s₀, fScr s₀]) (s.rd ++ s.wr) ∧
      Covers [fIvR s₀, fBlk s₀, fScr s₀] s.wr := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [modeAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5, h.x0, h.x1, h.x2,
      h.x3, h.x4, h.x5, toNat_n]
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
    (hv : ∀ s, (modeAArch64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeAArch64 M).post s s')
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
  refine WP.call (k := modeAArch64 M) hv (rd := [fSch s₀]) (wr := [fIvR s₀, fBlk s₀, fScr s₀]) hpre hc hw ?_ nf
  intro s' rd' wr' sp' fr' cs' _ post₂
  rw [h.mem] at fr'
  simp only [modeAArch64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, h.x0, h.x1, h.x2, h.x3, h.x4,
    toNat_n, h.mem, eW, eIv, eB] at post₂
  exact ⟨by rw [cs_of cs' .x19 (by simp), h.x19], by rw [cs_of cs' .x20 (by simp), h.x20],
    by rw [cs_of cs' .x21 (by simp), h.x21], by rw [cs_of cs' .x22 (by simp), h.x22],
    by rw [cs_of cs' .x23 (by simp), h.x23], by rw [cs_of cs' .x24 (by simp), h.x24],
    by rw [cs_of cs' .x25 (by simp), h.x25],
    fun r hr => by rw [cs_of cs' r (by rcases hr with rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp', h.sp], by rw [rd', h.rd], by rw [wr', h.wr], fr', post₂.1, post₂.2⟩

/-! ## The partial last segment -/

theorem eval_u {M : Mode} {s₀ s : State} (h : Whole M s₀ s) :
    isa.eval (.zero .x .x23) s = some (decide (fU s₀ = 0)) := by
  rw [Proof.Modes.AArch64.eval_zero, h.x23, Proof.Modes.AArch64.ofNat_beq_zero (by have := u_lt s₀; omega)]

theorem bytesAt_getD (m : Mem) (p : Addr) {n q : Nat} (hq : q < n) :
    (bytesAt m p n).getD q 0 = m (p + BitVec.ofNat 64 q) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hq]

/-- What the function leaves before restoring the registers. -/
structure Done (M : Mode) (s₀ s : State) : Prop where
  x25 : s.gpr .x25 = fV s₀
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
  ⟨h.x25, h.kept, h.rd, h.wr, h.frame', h.blocks, fun q hq => absurd hq (by omega),
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

theorem x1_ofNat (s₀ : State) : s₀.gpr .x1 = BitVec.ofNat 64 (fR s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [fR]

/-- What the arguments of the call of the block function leave. -/
structure IvA (M : Mode) (s₀ s : State) : Prop where
  whole : Whole M s₀ s
  pre : CallPre s (fW s₀) (fIv s₀) (fS s₀) (fR s₀)

theorem final_ivArgs_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.block Impl.AesOfb.AArch64.ivArgs) s (IvA M s₀) := by
  obtain ⟨s', run, x0, x1, x2, x3, x4, cs, sp, mem, rd, wr⟩ := AesOfb.AArch64.ivArgs_ok s
  have c (r : Reg) (hr : r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x22 ∨ r = .x23 ∨ r = .x24 ∨ r = .x25 ∨
      r = .x26 ∨ r = .x27 ∨ r = .x28) : s'.gpr r = s.gpr r :=
    cs r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.of_runBlock ⟨s', run, ⟨⟨by rw [c .x19 (by simp), h.x19], by rw [c .x20 (by simp), h.x20],
    by rw [c .x21 (by simp), h.x21], by rw [c .x22 (by simp), h.x22], by rw [c .x23 (by simp), h.x23],
    by rw [c .x24 (by simp), h.x24], by rw [c .x25 (by simp), h.x25],
    fun r hr => by rw [c r (by rcases hr with rfl | rfl | rfl <;> simp), h.kept r hr],
    by rw [sp, h.sp], by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem]; exact h.frame, by rw [mem]; exact h.blocks,
    by rw [mem]; exact h.iv⟩, ?_⟩⟩
  exact {
    x0 := by rw [x0, h.x19]
    x1 := by rw [x1, h.x20, x1_ofNat]
    x2 := by rw [x2, h.x21]
    x3 := x3
    x4 := by rw [x4, h.x24]
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
  x21 : s.gpr .x21 = fIv s₀
  x22 : s.gpr .x22 = fT s₀
  x23 : s.gpr .x23 = BitVec.ofNat 64 (fU s₀)
  x25 : s.gpr .x25 = fV s₀
  kept : Kept s₀ s
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tailb : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q)
  iv : bytesAt s.mem (fIv s₀) 16 =
    Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))

theorem final_ciph_wp (v : BlocksImpl) {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State}
    (h : IvA M s₀ s) : WP isa (.call v.enc.name v.enc.code) s (Ciph M s₀) := by
  obtain ⟨hw, hc⟩ := h
  refine WP.mono (blk_call v.encOk v.encNoFrames hc) fun s' c => ?_
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
  refine ⟨by rw [cs .x21 (by simp), hw.x21], by rw [cs .x22 (by simp), hw.x22],
    by rw [cs .x23 (by simp), hw.x23], by rw [cs .x25 (by simp), hw.x25],
    fun r hr => by rw [cs r (by rcases hr with rfl | rfl | rfl <;> simp), hw.kept r hr],
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

theorem final_xor_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Ciph M s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa (.seq (.block [Impl.AesCbc.AArch64.mov .x9 .x21])
      (.loop (.block (Impl.Modes.AArch64.xorByte .x22 .x23)) (.nonzero .x .x23))) s (Done M s₀) := by
  obtain ⟨s₁, run₁, x9₁, o₁, mem₁, rd₁, wr₁⟩ := Proof.Modes.AArch64.addImm_ok s .x9 .x21 (v := 0) (by decide)
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hU := u_lt s₀
  have hT := toNat_tail hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have xp : Proof.Modes.AArch64.XPre s₁ (fIv s₀) (fT s₀) (fU s₀) .x22 .x23 := {
    small := by omega
    disj := (hp.iv_data.sub_left (Region.sub_prefix (by omega))).sub_right (tail_sub s₀)
    rdK := fun q hq => by
      rw [rd₁, wr₁, h.rd, h.wr, hp.rd, hp.wr]
      exact ⟨fIvR s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.iv_wrap; omega)⟩
    wrR := fun q hq => by
      rw [wr₁, h.wr, hp.wr]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show fT s₀ + BitVec.ofNat 64 q = fD s₀ + BitVec.ofNat 64 (16 * fN s₀ + q) from Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega)
    dl := by decide
    d9 := by decide
    d6 := by decide
    d7 := by decide }
  have x0 : Proof.Modes.AArch64.XInv s₁ (fIv s₀) (fT s₀) (fU s₀) .x22 .x23 0 s₁ := {
    x9 := by rw [x9₁, h.x21]
    dat := by rw [o₁ _ (by decide), h.x22]; exact (BitVec.add_zero _).symm
    left := by rw [o₁ _ (by decide), h.x23, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Proof.Modes.AArch64.xorLoop_wp xp x0) fun s' d => ?_
  have ivT : ∀ r ∈ [fTail s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.sub_right (tail_sub s₀)
  have g (r : Reg) (hr : r = .x25 ∨ r = .x26 ∨ r = .x27 ∨ r = .x28) : s'.gpr r = s.gpr r := by
    rw [d.gpr r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      o₁ _ (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  refine ⟨by rw [g .x25 (by simp), h.x25], fun r hr => by rw [g r (by rcases hr with rfl | rfl | rfl <;> simp),
      h.kept r hr], by rw [d.rd, rd₁, h.rd], by rw [d.wr, wr₁, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · exact h.frame.trans ((mem₁ ▸ d.frame).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' d.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail, mem₁]
    exact h.blocks
  · rw [d.data q hq, mem₁, h.tailb q hq, ← bytesAt_getD s.mem (fIv s₀) (show q < 16 by omega), h.iv]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame d.frame ivT (by decide), mem₁, h.iv]

theorem final_mid_wp (v : BlocksImpl) {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.ite (.zero .x .x23) (.block []) (finalTail v.enc)) s (Done M s₀) := by
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [eval_u h, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · refine WP.ite false (by rw [eval_u h, decide_eq_false hu]) (fun h => by cases h) fun _ => ?_
    exact WP.seq (WP.mono (final_ivArgs_wp hp h) fun _ h₁ =>
      WP.seq (WP.mono (final_ciph_wp v hp h₁) fun _ h₂ => final_xor_wp hp h₂ hu))

/-! ## Restoring the registers -/

theorem final_end_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Done M s₀ s) :
    WP isa (.block finalRestore) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  have hs : Spill.Saved (fV s₀) s₀.gpr finalSaved s.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (fV s₀) s₀.gpr).frame h.frame fun p hp' r hr => by
      have hsub : Region.Sub ⟨fV s₀ + BitVec.ofNat 64 p.2, 8⟩ (fSv s₀) := Offset.sub_base _ (saved_slots p hp')
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_sv.symm.sub_left hsub
      · exact hp.data_sv.symm.sub_left hsub
      · exact hp.scr_sv.symm.sub_left hsub
  show WP isa (.block (Spill.restoreCode .x25 finalSaved)) _ _
  refine WP.mono (Spill.restore_wp h.x25 saved_fits (by decide) (fun p hp' => ?_) hs)
    fun s' r => ⟨fun q hq => r.gpr_of ?_, r.mem⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inl (by decide)
      | exact .inr (h.kept _ (by simp))

/-! ## The whole function -/

theorem final_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeAArch64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeAArch64 M).post s s')
    (nf : whole.noFrames = true) (v : BlocksImpl) {s₀ : State} (hp : FPre s₀) :
    WP isa (final name whole v.enc) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ ∃ s₁, Done M s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hv nf hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_mid_wp v hp h₂) fun s₃ h₃ => ?_)
  exact WP.mono (final_end_wp hp h₃) fun _ ⟨g, m⟩ => ⟨g, s₃, h₃, m⟩

/-- The specification's results, from what the function leaves. -/
theorem final_post {enc : Bool} {s₀ s₁ s' : State} (h : Done (cfbMode enc) s₀ s₁) (hm : s'.mem = s₁.mem) :
    (finalAArch64 enc).post s₀ s' := by
  cases enc
  · show Spec.Cfb.DecryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
    exact decryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)
  · show Spec.Cfb.EncryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
    exact encryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)

theorem final_correct {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeAArch64 (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (cfbMode enc)).post s s')
    (nf : whole.noFrames = true) (v : BlocksImpl) (hk : (final name whole v.enc).allInstrs keepsV = true)
    (s : State) (hs : (finalAArch64 enc).pre s) :
    ∃ t s', Exec isa (final name whole v.enc) s t s' ∧ abiPreserved s s' ∧ (finalAArch64 enc).post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp hv nf v (FPre.of hs)
  exact ⟨t, s', he, ⟨hg, AArch64.Exec.sp he, Exec.preservedV he hk⟩, final_post h₁ hm⟩

/-! ## The code's properties -/

theorem encrypt_noFrames (v : BlocksImpl) : (Impl.AesCfb.AArch64.encrypt v.enc).noFrames = true := by
  simp only [Impl.AesCfb.AArch64.encrypt, Impl.AesCbc.AArch64.whole, Impl.AesCfb.AArch64.body, Code.noFrames,
    v.encNoFrames, Bool.and_self]

theorem decrypt_noFrames (v : BlocksImpl) : (Caller.decrypt v).noFrames = true := by
  unfold Caller.decrypt
  split
  · lit_decide
  · simp only [Impl.AesCfb.AArch64.decrypt, Impl.AesCbc.AArch64.whole, Impl.AesCfb.AArch64.body,
      Code.noFrames, v.encNoFrames, Bool.and_self]

theorem decrypt_keepsV' (v : BlocksImpl) : (Caller.decrypt v).allInstrs keepsV = true := by
  unfold Caller.decrypt
  split
  · lit_decide
  · exact decrypt_keepsV v

theorem final_keepsV {name : String} {whole : Prog isa} (v : BlocksImpl) (hw : whole.allInstrs keepsV = true) :
    (final name whole v.enc).allInstrs keepsV = true := by
  simp only [final, finalTail, Code.allInstrs, hw, v.encKeepsV, Bool.and_true, Bool.true_and]
  decide

/-- Decryption's whole-block code, as its registration emits it, is correct
and constant time under `modeAArch64`. -/
theorem decrypt_correct' (v : BlocksImpl) (s : State) (hs : (modeAArch64 (cfbMode false)).pre s) :
    ∃ t s', Exec isa (Caller.decrypt v) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (cfbMode false)).post s s' := by
  unfold Caller.decrypt
  split
  · exact Decrypt.correct s hs
  · exact decrypt_correct v s hs

theorem decrypt_ct' (v : BlocksImpl) :
    ConstantTime isa (modeAArch64 (cfbMode false)).pre (modeAArch64 (cfbMode false)).pub (Caller.decrypt v) := by
  unfold Caller.decrypt
  split
  · exact Decrypt.ct
  · exact AesCbc.AArch64.whole_ct (decBody_ok v) (decBody_ct v)

/-! ## Constant time -/

/-- No code changes `sp` (but frames, which restore it). -/
theorem WP.sp_eq {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp :=
  let ⟨t, s', he, hq⟩ := h
  ⟨t, s', he, hq, AArch64.Exec.sp he⟩

theorem agree_of {s₁ s₂ : State} {rs : List Reg} (hsp : s₁.sp = s₂.sp) (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (Taint.mem_ofRegs.mp hr)⟩

theorem final_rel {enc : Bool} {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeAArch64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeAArch64 M).post s s')
    (hct : ConstantTime isa (modeAArch64 M).pre (modeAArch64 M).pub whole)
    (nf : whole.noFrames = true) (v : BlocksImpl) {s₀ s₀' : State}
    (h0 : (finalAArch64 enc).pre s₀) (h0' : (finalAArch64 enc).pre s₀') (hq : (finalAArch64 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (final name whole v.enc) fun _ _ => True := by
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  obtain ⟨qW, qR, qIv, qD, qL, qS, qV, qSp⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, fD, qD, qN]
  -- The registers saved and the arguments set up.
  obtain ⟨_, t₁⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6])
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
  have r₂ := (RelCT.callEx (k := modeAArch64 M) (n := name) hv hct
    (P := fun a b => Setup s₀ a ∧ Setup s₀' b) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre (M := cfbMode enc) hp ha
      obtain ⟨pb, cb, wb⟩ := whole_pre (M := cfbMode enc) hp' hb
      refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb⟩
      simp only [modeAArch64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        callEntry_x0, callEntry_x1, callEntry_x2, callEntry_x3, callEntry_x4, callEntry_x5,
        ha.x0, ha.x1, ha.x2, ha.x3, ha.x4, ha.x5, ha.sp, hb.x0, hb.x1, hb.x2, hb.x3, hb.x4, hb.x5, hb.sp]
      rw [fW, fW, fIv, fIv, fD, fD, fS, fS, qW, qR, qIv, qD, qS, qSp, qN]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).wp
    (F₁ := Whole M s₀) (F₂ := Whole M s₀')
    fun a b h => ⟨whole_wp hv nf hp h.1, whole_wp hv nf hp' h.2⟩
  -- The partial last segment.
  obtain ⟨_, t₃⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x24])
      (.block Impl.AesOfb.AArch64.ivArgs) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, t₄⟩ : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23])
      (.seq (.block [Impl.AesCbc.AArch64.mov .x9 .x21])
        (.loop (.block (Impl.Modes.AArch64.xorByte .x22 .x23)) (.nonzero .x .x23))) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have tail (hu : fU s₀ ≠ 0) : RelCT isa (fun a b => Whole M s₀ a ∧ Whole M s₀' b)
      (finalTail v.enc) fun a b => Done M s₀ a ∧ Done M s₀' b := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₃ := (RelCT.taint (A := taint)
      (P := fun a b => Whole M s₀ a ∧ Whole M s₀' b) _
      (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.1.x19, h.2.x19, fW, fW, qW]
        · rw [h.1.x20, h.2.x20, qR]
        · rw [h.1.x21, h.2.x21, fIv, fIv, qIv]
        · rw [h.1.x24, h.2.x24, fS, fS, qS]) t₃).wp
      (F₁ := IvA M s₀) (F₂ := IvA M s₀')
      fun a b h => ⟨final_ivArgs_wp hp h.1, final_ivArgs_wp hp' h.2⟩
    have a₄ := (AesCbc.AArch64.blk_rel (b := v.enc) v.encOk v.encCt
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
      fun a b h => ⟨final_ciph_wp v hp h.1, final_ciph_wp v hp' h.2⟩
    have a₅ := (RelCT.taint (A := taint)
      (P := fun a b => Ciph M s₀ a ∧ Ciph M s₀' b) _
      (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, qSp]) fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.x21, h.2.x21, fIv, fIv, qIv]
        · rw [h.1.x22, h.2.x22, qT]
        · rw [h.1.x23, h.2.x23, qU]) t₄).wp
      (F₁ := Done M s₀) (F₂ := Done M s₀')
      fun a b h => ⟨final_xor_wp hp h.1 hu, final_xor_wp hp' h.2 hu'⟩
    exact (a₃.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((a₄.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₅.mono (fun _ _ h => h) fun _ _ h => h.2))
  have r₃ : RelCT isa (fun a b => Whole M s₀ a ∧ Whole M s₀' b)
      (.ite (.zero .x .x23) (.block []) (finalTail v.enc))
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
      ⟨WP.mono (WP.sp_eq (final_mid_wp v hp h.1)) fun _ x => x.2.trans h.1.sp,
        WP.mono (WP.sp_eq (final_mid_wp v hp' h.2)) fun _ x => x.2.trans h.2.sp⟩
  -- The registers restored.
  obtain ⟨_, t₅⟩ : ∃ h, (taint.check (Taint.ofRegs [.x25]) (.block finalRestore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have r₄ := RelCT.taint (A := taint) (P := fun a b => (Done M s₀ a ∧ Done M s₀' b) ∧
      a.sp = s₀.sp ∧ b.sp = s₀'.sp) _
    (fun a b h => agree_of (by rw [h.2.1, h.2.2, qSp]) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.x25, h.1.2.x25, fV, fV, qV]) t₅
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (r₃'.seq r₄))

theorem final_ct {enc : Bool} {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modeAArch64 M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modeAArch64 M).post s s')
    (hct : ConstantTime isa (modeAArch64 M).pre (modeAArch64 M).pub whole)
    (nf : whole.noFrames = true) (v : BlocksImpl) :
    ConstantTime isa (finalAArch64 enc).pre (finalAArch64 enc).pub (final name whole v.enc) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel hv hct nf v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem encryptFinal_verified (v : BlocksImpl) :
    Verified AArch64.target (encryptCode v) (finalScratchContract true) :=
  Verified.of_correct
    (final_correct (encrypt_correct v) (encrypt_noFrames v) v (final_keepsV v (encrypt_keepsV v)))
    (final_ct (encrypt_correct v) (AesCbc.AArch64.whole_ct (encBody_ok v) (encBody_ct v)) (encrypt_noFrames v) v)
    (final_implies true)

theorem decryptFinal_verified (v : BlocksImpl) :
    Verified AArch64.target (decryptCode v) (finalScratchContract false) :=
  Verified.of_correct
    (final_correct (decrypt_correct' v) (decrypt_noFrames v) v (final_keepsV v (decrypt_keepsV' v)))
    (final_ct (decrypt_correct' v) (decrypt_ct' v) (decrypt_noFrames v) v)
    (final_implies false)

/-! ## With `save` on the stack

The final functions have six argument words, so `save` is their seventh,
in `x6`: they run their code in a frame of 64 bytes on the stack
(`withStackScratchWiped`), `save`'s 64 bytes, which it zeroes before
returning. The code's calls use no stack, so 64 in all. -/

/-- A state satisfying the shared contracts' precondition. -/
def finalFrameSat : State := { finalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩] }

theorem encFrameSat_pre : ∃ s, (encryptFinalRoundsContract AArch64.abi 64).pre s := by
  implies_sat [encryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, encryptFinalPost, AArch64.abi,
    AArch64.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem decFrameSat_pre : ∃ s, (decryptFinalRoundsContract AArch64.abi 64).pre s := by
  implies_sat [decryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, decryptFinalPost, AArch64.abi,
    AArch64.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem encryptFinal_framed (v : BlocksImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (encryptCode v))
      (encryptFinalRoundsContract AArch64.abi 64) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre AArch64.abi.ptrBits) (post := encryptFinalPost AArch64.abi.ptrBits) (wa := false)
    (stack := 0) (bytes := 64) (words := 8) (encryptFinal_verified v) (by decide) (by decide) (by decide)
    (encryptFinalPost_localOut _) encFrameSat_pre

theorem decryptFinal_framed (v : BlocksImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (decryptCode v))
      (decryptFinalRoundsContract AArch64.abi 64) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre AArch64.abi.ptrBits) (post := decryptFinalPost AArch64.abi.ptrBits) (wa := false)
    (stack := 0) (bytes := 64) (words := 8) (decryptFinal_verified v) (by decide) (by decide) (by decide)
    (decryptFinalPost_localOut _) decFrameSat_pre

end VG.Proof.AesCfb.AArch64.Final
