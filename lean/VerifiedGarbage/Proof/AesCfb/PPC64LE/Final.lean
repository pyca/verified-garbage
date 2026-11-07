module

public import VerifiedGarbage.Impl.AesCfb.PPC64LE.Final
public import VerifiedGarbage.Proof.AesCfb.Final
public import VerifiedGarbage.Proof.AesCfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
import VerifiedGarbage.Proof.AesCfb.PPC64LE.Body
import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
meta import VerifiedGarbage.Impl.AesCfb.PPC64LE.Final
meta import VerifiedGarbage.Proof.AesCfb.Final
meta import VerifiedGarbage.Proof.AesCfb.PPC64LE.Verified
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.AesCfb.PPC64LE.Body
meta import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal

/-!
# AES-CFB128 of a message's last piece on PPC64LE

`encryptFinal_framed` and `decryptFinal_framed`: `vg_aes_cfb128_encrypt_final`
and `vg_aes_cfb128_decrypt_final` (`Impl/AesCfb/PPC64LE/Final.lean`) meet
`Proof.AesCfb.encryptFinalRoundsContract` (and `decrypt…`), from which the
shared contracts follow (`Proof.AesCfb.encryptFinal_keyed`).

The code is proven against `finalPPC64LE`, with a seventh argument `save`
(`r9`) for its return address and its caller's registers (`final_implies`:
the shared contract with it, `finalScratchContract`), as a caller of two
verified functions, through their contracts (`WP.call`, `blk_call`):

* `final_setup_wp`: the return address and the registers saved in `save`,
  and the arguments set up (`Setup`);
* `whole_wp`: the whole-block function of the same direction on the
  `n = len / 16` whole blocks, from its contract
  (`modePPC64LE (cfbMode enc)`), with the regions it is given (`whole_pre`):
  the blocks and the chaining value the mode's (`Whole`);
* `final_mid_wp`: if `u = len % 16` bytes are left, the block function on
  the chaining value in place (`final_ivArgs_wp`, `final_ciph_wp`), and its
  first `u` bytes XORed into them by the modes' loop
  (`Modes.PPC64LE.tailLoop_wp`, `final_xor_wp`); what is left before the
  registers are restored is `Done`;
* `final_end_wp`: the registers and the return address restored from
  `save`, which nothing else wrote;
* `final_post`: `Done` gives `Spec.Cfb.EncryptFinal` (or `DecryptFinal`),
  by `Proof.AesCfb.encryptFinal_of`.

Constant time (`final_rel`): the blocks by the taint analysis, the calls by
their contracts' constant time (`RelCT.callEx`, `blk_rel`), every address
and branch from the pointers and `len`, which agree in both runs.
`encryptFinal_framed` runs the code with `save` in a frame of 96 bytes on
the stack (`PPC64LE.Verified.stackScratchWiped`: its 32-byte header and
`save`'s 64 bytes), `save` zeroed on return.
-/

@[expose] public section

namespace VG.Proof.AesCfb.PPC64LE.Final

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesCfb.PPC64LE (final finalSaved finalMoves finalSetup finalRestore finalTail)

/-! ## The contract -/

/-- The code's contract, with the arguments `(schedule = r3, rounds = r4,
iv = r5, data = r6, len = r7, scratch = r8, save = r9)`: in direction `enc`,
the data and the block at `iv` as `Spec.Cfb.EncryptFinal` (or
`DecryptFinal`) says, by AES with the key schedule it is given. -/
def finalPPC64LE (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let iv : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 2176⟩
    let sv : Region := ⟨s.gpr .r9, 64⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr, sv] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ sched.Disjoint sv ∧
      iv.Disjoint data ∧ iv.Disjoint scr ∧ iv.Disjoint sv ∧
      data.Disjoint scr ∧ data.Disjoint sv ∧ scr.Disjoint sv ∧
      (s.gpr .r3).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 2176 ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 64 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .r3) (s.gpr .r4).toNat
    if enc then Spec.Cfb.EncryptFinal ciph 16 s.mem s'.mem (s.gpr .r5) (s.gpr .r6) (s.gpr .r7).toNat
    else Spec.Cfb.DecryptFinal ciph 16 s.mem s'.mem (s.gpr .r5) (s.gpr .r6) (s.gpr .r7).toNat
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.sp = s₂.sp

/-- The postcondition in direction `enc`. -/
abbrev finalPost (enc : Bool) : Spec.Cfb.aesFinalSig.Post PPC64LE.abi.ptrBits :=
  if enc then encryptFinalPost PPC64LE.abi.ptrBits else decryptFinalPost PPC64LE.abi.ptrBits

/-- The contract the frame needs: the shared one, with `save`, 64 bytes, as
a seventh argument, and no stack (a call stores nothing in memory). -/
abbrev finalScratchContract (enc : Bool) : Contract isa :=
  Sig.scratchContract PPC64LE.abi Spec.Cfb.aesFinalSig "save" .u64 8 (finalPre PPC64LE.abi.ptrBits)
    (finalPost enc) false 0

/-- A state satisfying the precondition. -/
def finalSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r8 => 0x4000 | .r9 => 0x6000
    | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩, ⟨0x6000, 64⟩]

theorem final_implies (enc : Bool) : (finalPPC64LE enc).Implies (finalScratchContract enc) := by
  cases enc <;>
  sig_implies [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Cfb.aesFinalSig, finalPre, finalPost, encryptFinalPost, decryptFinalPost, finalPPC64LE, PPC64LE.abi,
    PPC64LE.argRegs] [finalSat] using finalSat

/-! ## The arguments, by name -/

section
variable (s₀ : State)

abbrev fW : Addr := s₀.gpr .r3
abbrev fR : Nat := (s₀.gpr .r4).toNat
abbrev fIv : Addr := s₀.gpr .r5
abbrev fD : Addr := s₀.gpr .r6
abbrev fL : Nat := (s₀.gpr .r7).toNat
abbrev fS : Addr := s₀.gpr .r8
abbrev fV : Addr := s₀.gpr .r9
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

/-- The values saved: `r0` holds the return address. -/
abbrev saveG : Reg → BitVec 64 := (s₀.write .r0 s₀.lr).gpr

/-- The memory once the return address and the registers are saved. -/
abbrev svMem : Mem := Spill.saveMem s₀.mem (fV s₀) (saveG s₀) finalSaved

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
  rounds : fR s₀ = 10 ∨ fR s₀ = 12 ∨ fR s₀ = 14

theorem FPre.of {enc : Bool} {s₀ : State} (h : (finalPPC64LE enc).pre s₀) : FPre s₀ :=
  let ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
  ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩

/-! ## Regions -/

theorem blk_sub (s₀ : State) : Region.Sub (fBlk s₀) (fData s₀) := Region.sub_prefix (Nat.mul_div_le _ _)

theorem tail_sub (s₀ : State) : Region.Sub (fTail s₀) (fData s₀) :=
  Offset.sub_base _ (by rw [Nat.div_add_mod])

theorem fN_eq (s₀ : State) : fN s₀ = fL s₀ / 16 := rfl
theorem fU_eq (s₀ : State) : fU s₀ = fL s₀ % 16 := rfl

theorem n_lt (s₀ : State) : fN s₀ < 2 ^ 64 := by
  have := (s₀.gpr .r7).isLt; have : fL s₀ = (s₀.gpr .r7).toNat := rfl; rw [fN_eq]; omega

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

/-- A register after a write, as an `if`. -/
theorem upd_gpr {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) (r : Reg) :
    s'.gpr r = if r = d then v else s.gpr r := by
  by_cases h : r = d
  · subst h; simp only [↓reduceIte]; exact u.gpr
  · simp only [h, ↓reduceIte]; exact u.other r h

theorem moves_wp {s : State} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r14 = s.gpr .r3 → s'.gpr .r15 = s.gpr .r4 → s'.gpr .r16 = s.gpr .r5 →
      s'.gpr .r19 = s.gpr .r8 → s'.gpr .r20 = s.gpr .r9 →
      s'.gpr .r31 = s.gpr .r6 + (s.gpr .r7 >>> 4 <<< 4) →
      s'.gpr .r30 = s.gpr .r7 - (s.gpr .r7 >>> 4 <<< 4) → s'.gpr .r7 = s.gpr .r7 >>> 4 →
      (∀ r, r ≠ .r14 → r ≠ .r15 → r ≠ .r16 → r ≠ .r19 → r ≠ .r20 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .r31 → r ≠ .r30 → r ≠ .r7 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block finalMoves) s Φ := by
  unfold finalMoves Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_mr fun s₄ u₄ => wp_mr fun s₅ u₅ =>
    wp_lsr (by decide) fun s₆ u₆ => wp_lsl (by decide) fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_sub fun s₉ u₉ => wp_mr fun s₁₀ u₁₀ => wp_nil ?_
  refine k s₁₀ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun r h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ => ?_) ?_ ?_ ?_
  all_goals try (simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅,
    upd_gpr u₄, upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, reduceCtorEq, ↓reduceIte]; done)
  · simp only [upd_gpr u₁₀, upd_gpr u₉, upd_gpr u₈, upd_gpr u₇, upd_gpr u₆, upd_gpr u₅, upd_gpr u₄,
      upd_gpr u₃, upd_gpr u₂, upd_gpr u₁, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, ↓reduceIte]
  · rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

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

/-- The registers holding our variables, saved and restored. -/
abbrev vars : List Reg := [.r14, .r15, .r16, .r19, .r20, .r30, .r31]

/-- The callee-saved registers this code neither saves nor uses. -/
abbrev Kept (s₀ s : State) : Prop := ∀ r ∈ preserved, r ∉ vars → s.gpr r = s₀.gpr r

/-- What saving the registers and setting up the arguments leaves. -/
structure Setup (s₀ s : State) : Prop where
  r14 : s.gpr .r14 = fW s₀
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = fIv s₀
  r19 : s.gpr .r19 = fS s₀
  r20 : s.gpr .r20 = fV s₀
  r30 : s.gpr .r30 = BitVec.ofNat 64 (fU s₀)
  r31 : s.gpr .r31 = fT s₀
  r3 : s.gpr .r3 = fW s₀
  r4 : s.gpr .r4 = s₀.gpr .r4
  r5 : s.gpr .r5 = fIv s₀
  r6 : s.gpr .r6 = fD s₀
  r7 : s.gpr .r7 = BitVec.ofNat 64 (fN s₀)
  r8 : s.gpr .r8 = fS s₀
  kept : Kept s₀ s
  mem : s.mem = svMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem preserved_ne_r0 : ∀ r ∈ preserved, r ≠ .r0 := by decide

theorem preserved_ne' {r : Reg} (hr : r ∈ preserved) (hv : r ∉ vars) :
    r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .r14 ∧ r ≠ .r15 ∧ r ≠ .r16 ∧ r ≠ .r19 ∧
      r ≠ .r20 ∧ r ≠ .r30 ∧ r ≠ .r31 := by
  revert hr hv; cases r <;> decide

theorem final_setup_wp {s₀ : State} (hp : FPre s₀) : WP isa (.block finalSetup) s₀ (Setup s₀) := by
  show WP isa (.block (.mflr .r0 :: (Spill.saveCode .r9 finalSaved ++ finalMoves))) _ _
  refine WP.cons exec_mflr (Spill.save_ok (b := .r9) (l := finalSaved) (by decide) saved_fits
    (fun p hp' => ?_) ?_)
  · show InRegions s₀.wr (fV s₀ + BitVec.ofNat 64 p.2) 8
    rw [hp.wr]
    have := saved_slots p hp'
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
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
      obtain ⟨h7, -, -, h10, h11, h14, h15, h16, h19, h20, h30, h31⟩ := preserved_ne' hr hv
      exact k r h14 h15 h16 h19 h20 h10 h11 h31 h30 h7 (preserved_ne_r0 r hr)
    mem := mem
    rd := rd
    wr := wr }

/-! ## The call of the whole-block function -/

open VG.Proof.AesCbc (Mode cts aesWith_state)
open VG.Proof.AesCbc.PPC64LE (modePPC64LE CallPre CallPost blk_call blk_rel callEntry_gpr' taintRegs wp_sp)

/-- What the call of the whole-block function leaves, for the mode `M`. -/
structure Whole (M : Mode) (s₀ s : State) : Prop where
  r14 : s.gpr .r14 = fW s₀
  r15 : s.gpr .r15 = s₀.gpr .r4
  r16 : s.gpr .r16 = fIv s₀
  r19 : s.gpr .r19 = fS s₀
  r20 : s.gpr .r20 = fV s₀
  r30 : s.gpr .r30 = BitVec.ofNat 64 (fU s₀)
  r31 : s.gpr .r31 = fT s₀
  kept : Kept s₀ s
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
    (modePPC64LE M).pre (s.callEntry.withRegions [fSch s₀] [fIvR s₀, fBlk s₀, fScr s₀]) ∧
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

theorem whole_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modePPC64LE M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modePPC64LE M).post s s')
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
  refine WP.call (k := modePPC64LE M) hv (rd := [fSch s₀]) (wr := [fIvR s₀, fBlk s₀, fScr s₀]) hpre hc hw ?_ nf
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

/-! ## The partial last segment -/

theorem eval_u {M : Mode} {s₀ s : State} (h : Whole M s₀ s) :
    isa.eval (.zero .d .r30) s = some (decide (fU s₀ = 0)) := by
  rw [eval_zero, h.r30, ofNat_beq_zero (by have := u_lt s₀; omega)]

theorem bytesAt_getD (m : Mem) (p : Addr) {n q : Nat} (hq : q < n) :
    (bytesAt m p n).getD q 0 = m (p + BitVec.ofNat 64 q) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hq]

/-- What the function leaves before restoring the registers. -/
structure Done (M : Mode) (s₀ s : State) : Prop where
  r20 : s.gpr .r20 = fV s₀
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
  ⟨h.r20, h.kept, h.rd, h.wr, h.frame', h.blocks, fun q hq => absurd hq (by omega),
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

theorem r4_ofNat (s₀ : State) : s₀.gpr .r4 = BitVec.ofNat 64 (fR s₀) := by
  apply BitVec.eq_of_toNat_eq; simp [fR]

/-- The arguments of the block function for the block at `r16`. -/
theorem ivArgs_wp {s : State} {Φ : State → Prop}
    (k : ∀ s', s'.gpr .r3 = s.gpr .r14 → s'.gpr .r4 = s.gpr .r15 → s'.gpr .r5 = s.gpr .r16 →
      s'.gpr .r6 = BitVec.ofNat 64 1 → s'.gpr .r7 = s.gpr .r19 →
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Φ s') :
    WP isa (.block Impl.AesOfb.PPC64LE.ivArgs) s Φ := by
  unfold Impl.AesOfb.PPC64LE.ivArgs Impl.AesCbc.PPC64LE.mov
  refine wp_mr fun s₁ u₁ => wp_mr fun s₂ u₂ => wp_mr fun s₃ u₃ => wp_li (by decide) fun s₄ u₄ =>
    wp_mr fun s₅ u₅ => wp_nil ?_
  refine k s₅ ?_ ?_ ?_ ?_ ?_ (fun r h3 h4 h5 h6 h7 => ?_) ?_ ?_ ?_
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.gpr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-- What the arguments of the call of the block function leave. -/
structure IvA (M : Mode) (s₀ s : State) : Prop where
  whole : Whole M s₀ s
  pre : CallPre s (fW s₀) (fIv s₀) (fS s₀) (fR s₀)

theorem final_ivArgs_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.block Impl.AesOfb.PPC64LE.ivArgs) s (IvA M s₀) := by
  refine ivArgs_wp fun s' r3 r4 r5 r6 r7 o mem rd wr => ?_
  have c (r : Reg) (hr : r ∈ preserved) : s'.gpr r = s.gpr r := by
    obtain ⟨h3, h4, h5, h6, h7, -⟩ := Proof.AesCbc.PPC64LE.preserved_ne hr
    exact o r h3 h4 h5 h6 h7
  refine ⟨⟨by rw [c .r14 (by decide), h.r14], by rw [c .r15 (by decide), h.r15],
    by rw [c .r16 (by decide), h.r16], by rw [c .r19 (by decide), h.r19], by rw [c .r20 (by decide), h.r20],
    by rw [c .r30 (by decide), h.r30], by rw [c .r31 (by decide), h.r31],
    fun r hr hv => by rw [c r hr, h.kept r hr hv],
    by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem]; exact h.frame, by rw [mem]; exact h.blocks,
    by rw [mem]; exact h.iv⟩, ?_⟩
  exact {
    r3 := by rw [r3, h.r14]
    r4 := by rw [r4, h.r15, r4_ofNat]
    r5 := by rw [r5, h.r16]
    r6 := r6
    r7 := by rw [r7, h.r19]
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
  r16 : s.gpr .r16 = fIv s₀
  r20 : s.gpr .r20 = fV s₀
  r30 : s.gpr .r30 = BitVec.ofNat 64 (fU s₀)
  r31 : s.gpr .r31 = fT s₀
  kept : Kept s₀ s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [fIvR s₀, fData s₀, fScr s₀] (svMem s₀) s.mem
  blocks : Spec.Cbc.blocksAt s.mem (fD s₀) (fN s₀) = M.out (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀)
  tailb : ∀ q < fU s₀, s.mem (fT s₀ + BitVec.ofNat 64 q) = s₀.mem (fT s₀ + BitVec.ofNat 64 q)
  iv : bytesAt s.mem (fIv s₀) 16 =
    Spec.Cbc.aesWith (fR s₀) (fWk s₀) (M.chain (fR s₀) (fWk s₀) (fIv0 s₀) (fBlks s₀))

theorem final_ciph_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State}
    (h : IvA M s₀ s) : WP isa Impl.AesCbc.PPC64LE.encCall s (Ciph M s₀) := by
  obtain ⟨hw, hc⟩ := h
  refine WP.mono (blk_call Proof.Aes.PPC64LE.encryptBlocks_correct
    Proof.AesCbc.PPC64LE.encryptBlocks_noFrames hc) fun s' c => ?_
  have cs := c.saved
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
  refine ⟨by rw [cs .r16 (by decide), hw.r16], by rw [cs .r20 (by decide), hw.r20],
    by rw [cs .r30 (by decide), hw.r30], by rw [cs .r31 (by decide), hw.r31],
    fun r hr hv => by rw [cs r hr, hw.kept r hr hv],
    by rw [c.rd, hw.rd], by rw [c.wr, hw.wr], hw.frame'.trans fc, ?_, fun q hq => ?_, ?_⟩
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

/-- The XOR of the partial last segment. -/
abbrev xorCode : Prog isa :=
  .seq (.block [Impl.AesCbc.PPC64LE.mov .r8 .r16])
    (.loop (.block Impl.Modes.PPC64LE.tailByte) (.nonzero .d .r30))

theorem final_xor_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Ciph M s₀ s) (hu : fU s₀ ≠ 0) :
    WP isa xorCode s (Done M s₀) := by
  refine WP.seq (wp_mr fun s₁ u₁ => wp_nil ?_)
  have hU := u_lt s₀
  have hT := toNat_tail hp hu
  have hL := Nat.div_add_mod (fL s₀) 16
  have hDw := hp.data_wrap
  have hIw := hp.iv_wrap
  have eN := fN_eq s₀
  have eU := fU_eq s₀
  have xp : Proof.Modes.PPC64LE.XPre s₁ (fIv s₀) (fT s₀) (fU s₀) := {
    pos := by omega
    fitK := by omega
    fitR := by omega
    disj := (hp.iv_data.sub_left (Region.sub_prefix (by omega))).sub_right (tail_sub s₀)
    rdK := fun q hq => by
      rw [u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]
      exact ⟨fIvR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
    wrR := fun q hq => by
      rw [u₁.wr, h.wr, hp.wr]
      refine ⟨fData s₀, by simp, ?_⟩
      rw [show fT s₀ + BitVec.ofNat 64 q = fD s₀ + BitVec.ofNat 64 (16 * fN s₀ + q) from Offset.add_add _ _ _]
      exact Offset.contains_base _ (by omega) (by omega) }
  have x0 : Proof.Modes.PPC64LE.XInv s₁ (fIv s₀) (fT s₀) (fU s₀) 0 s₁ := {
    r8 := by rw [u₁.gpr, h.r16]; exact (BitVec.add_zero _).symm
    r31 := by rw [u₁.other _ (by decide), h.r31]; exact (BitVec.add_zero _).symm
    r30 := by rw [u₁.other _ (by decide), h.r30, Nat.sub_zero]
    lt := by omega
    data := fun q _ => by rw [ite_eq_right (Nat.not_lt_zero q)]
    frame := Frame.refl _ _
    rd := rfl
    wr := rfl
    gpr := fun _ _ _ _ _ _ => rfl }
  refine WP.mono (Proof.Modes.PPC64LE.tailLoop_wp xp x0) fun s' d => ?_
  have ivT : ∀ r ∈ [fTail s₀], (fIvR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hp.iv_data.sub_right (tail_sub s₀)
  have df : Frame [fTail s₀] s.mem s'.mem := by rw [← u₁.mem]; exact d.frame
  have g (r : Reg) (h8 : r ≠ .r8) (h9 : r ≠ .r9) (h10 : r ≠ .r10) (h30 : r ≠ .r30) (h31 : r ≠ .r31) :
      s'.gpr r = s.gpr r := by
    rw [d.gpr r h8 h9 h10 h30 h31, u₁.other r h8]
  refine ⟨by rw [g .r20 (by decide) (by decide) (by decide) (by decide) (by decide), h.r20],
    fun r hr hv => ?_, by rw [d.rd, u₁.rd, h.rd], by rw [d.wr, u₁.wr, h.wr], ?_, ?_, fun q hq => ?_, ?_⟩
  · obtain ⟨-, h8, h9, h10, -, -, -, -, -, -, h30, h31⟩ := preserved_ne' hr hv
    rw [g r h8 h9 h10 h30 h31, h.kept r hr hv]
  · exact h.frame.trans (df.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨fData s₀, by simp, tail_sub s₀⟩)
  · rw [blocksAt_frame' df fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.blk_tail]
    exact h.blocks
  · rw [d.data q hq, u₁.mem, h.tailb q hq, ← bytesAt_getD s.mem (fIv s₀) (show q < 16 by omega), h.iv]
  · rw [ite_eq_right hu, Proof.Cmac.bytesAt_frame df ivT (by decide), h.iv]

theorem final_tail_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s)
    (hu : fU s₀ ≠ 0) : WP isa finalTail s (Done M s₀) :=
  WP.seq (WP.mono (final_ivArgs_wp hp h) fun _ h₁ =>
    WP.seq (WP.mono (final_ciph_wp hp h₁) fun _ h₂ => final_xor_wp hp h₂ hu))

theorem final_mid_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Whole M s₀ s) :
    WP isa (.ite (.zero .d .r30) (.block []) finalTail) s (Done M s₀) := by
  by_cases hu : fU s₀ = 0
  · exact WP.ite true (by rw [eval_u h, decide_eq_true hu]) (fun _ => WP.block_nil (done_of_zero h hu))
      (fun h => by cases h)
  · exact WP.ite false (by rw [eval_u h, decide_eq_false hu]) (fun h => by cases h)
      fun _ => final_tail_wp hp h hu

/-! ## Restoring the registers -/

theorem restore_eq : finalRestore = Spill.restoreCode .r20 finalSaved ++ ([.mtlr .r0] : List Instr) := rfl

theorem final_end_wp {M : Mode} {s₀ : State} (hp : FPre s₀) {s : State} (h : Done M s₀ s) :
    WP isa (.block finalRestore) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ s'.mem = s.mem := by
  have hs : Spill.Saved (fV s₀) (saveG s₀) finalSaved s.mem :=
    (Spill.saveMem_saved (by decide) s₀.mem (fV s₀) (saveG s₀)).frame h.frame fun p hp' r hr => by
      have hsub : Region.Sub ⟨fV s₀ + BitVec.ofNat 64 p.2, 8⟩ (fSv s₀) := Offset.sub_base _ (saved_slots p hp')
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.iv_sv.symm.sub_left hsub
      · exact hp.data_sv.symm.sub_left hsub
      · exact hp.scr_sv.symm.sub_left hsub
  rw [restore_eq]
  refine Spill.restore_ok (b := .r20) (l := finalSaved) (by decide) h.r20 saved_fits (by decide)
    (fun p hp' => ?_) hs fun s₃ r₃ => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    have := saved_slots p hp'
    exact ⟨fSv s₀, by simp, Offset.contains_base _ (by omega) (by have := hp.sv_wrap; omega)⟩
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

theorem final_wp {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modePPC64LE M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modePPC64LE M).post s s')
    (nf : whole.noFrames = true) {s₀ : State} (hp : FPre s₀) :
    WP isa (final name whole) s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧ ∃ s₁, Done M s₀ s₁ ∧ s'.mem = s₁.mem := by
  refine WP.seq (WP.mono (final_setup_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (whole_wp hv nf hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (final_mid_wp hp h₂) fun s₃ h₃ => ?_)
  exact WP.mono (final_end_wp hp h₃) fun _ ⟨g, l, m⟩ => ⟨g, l, s₃, h₃, m⟩

/-- The specification's results, from what the function leaves. -/
theorem final_post {enc : Bool} {s₀ s₁ s' : State} (h : Done (cfbMode enc) s₀ s₁) (hm : s'.mem = s₁.mem) :
    (finalPPC64LE enc).post s₀ s' := by
  cases enc
  · show Spec.Cfb.DecryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
    exact decryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)
  · show Spec.Cfb.EncryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
    exact encryptFinal_of (aesWith_length _ _) (by decide) (by rw [hm]; exact h.blocks)
      (fun q hq => by rw [hm]; exact h.tail q hq) (by rw [hm]; exact h.iv)

theorem final_correct {enc : Bool} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modePPC64LE (cfbMode enc)).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (cfbMode enc)).post s s')
    (nf : whole.noFrames = true) (s : State) (hs : (finalPPC64LE enc).pre s) :
    ∃ t s', Exec isa (final name whole) s t s' ∧ abiPreserved s s' ∧ (finalPPC64LE enc).post s s' := by
  obtain ⟨t, s', he, hg, hl, s₁, h₁, hm⟩ := final_wp hv nf (FPre.of hs)
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hl⟩, final_post h₁ hm⟩

/-! ## The code's properties -/

theorem encrypt_noFrames : Impl.AesCfb.PPC64LE.encrypt.noFrames = true := by
  simp only [Impl.AesCfb.PPC64LE.encrypt, Impl.AesCbc.PPC64LE.whole, Impl.AesCfb.PPC64LE.body,
    Impl.AesCbc.PPC64LE.encCall, Code.noFrames, Bool.true_and, Bool.and_true]
  exact Proof.AesCbc.PPC64LE.encryptBlocks_noFrames

theorem decrypt_noFrames : Impl.AesCfb.PPC64LE.decrypt.noFrames = true := by
  simp only [Impl.AesCfb.PPC64LE.decrypt, Impl.AesCbc.PPC64LE.whole, Impl.AesCfb.PPC64LE.body,
    Impl.AesCbc.PPC64LE.encCall, Code.noFrames, Bool.true_and, Bool.and_true]
  exact Proof.AesCbc.PPC64LE.encryptBlocks_noFrames

/-! ## Constant time -/

theorem final_rel {enc : Bool} {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modePPC64LE M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modePPC64LE M).post s s')
    (hct : ConstantTime isa (modePPC64LE M).pre (modePPC64LE M).pub whole)
    (nf : whole.noFrames = true) {s₀ s₀' : State}
    (h0 : (finalPPC64LE enc).pre s₀) (h0' : (finalPPC64LE enc).pre s₀') (hq : (finalPPC64LE enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (final name whole) fun _ _ => True := by
  have hp := FPre.of h0
  have hp' := FPre.of h0'
  obtain ⟨qW, qR, qIv, qD, qL, qS, qV, qSp⟩ := hq
  have qU : fU s₀ = fU s₀' := by simp only [fU, fL, qL]
  have qN : fN s₀ = fN s₀' := by simp only [fN, fL, qL]
  have qT : fT s₀ = fT s₀' := by simp only [fT, fD, qD, qN]
  -- The registers saved and the arguments set up.
  obtain ⟨_, t₁⟩ : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
      (.block finalSetup) h).isSome = true := ⟨_, by taint_decide⟩
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
  have r₂ := (RelCT.callEx (k := modePPC64LE M) (n := name) hv hct
    (P := fun a b => (Setup s₀ a ∧ a.sp = s₀.sp) ∧ (Setup s₀' b ∧ b.sp = s₀'.sp)) fun a b ⟨ha, hb⟩ => by
      obtain ⟨pa, ca, wa⟩ := whole_pre (M := cfbMode enc) hp ha.1
      obtain ⟨pb, cb, wb⟩ := whole_pre (M := cfbMode enc) hp' hb.1
      refine ⟨_, _, _, _, pa, pb, ?_, ca, wa, cb, wb⟩
      simp only [modePPC64LE, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        callEntry_gpr' _ (by decide : Reg.r3 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r4 ∉ linkRegs),
        callEntry_gpr' _ (by decide : Reg.r5 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r6 ∉ linkRegs),
        callEntry_gpr' _ (by decide : Reg.r7 ∉ linkRegs), callEntry_gpr' _ (by decide : Reg.r8 ∉ linkRegs),
        ha.1.r3, ha.1.r4, ha.1.r5, ha.1.r6, ha.1.r7, ha.1.r8, ha.2,
        hb.1.r3, hb.1.r4, hb.1.r5, hb.1.r6, hb.1.r7, hb.1.r8, hb.2]
      rw [fW, fW, fIv, fIv, fD, fD, fS, fS, qW, qR, qIv, qD, qS, qSp, qN]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩).wp
    (F₁ := fun (s : State) => Whole M s₀ s ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => Whole M s₀' s ∧ s.sp = s₀'.sp)
    fun a b h => ⟨WP.mono (wp_sp (whole_wp hv nf hp h.1.1)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
      WP.mono (wp_sp (whole_wp hv nf hp' h.2.1)) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
  -- The partial last segment.
  obtain ⟨_, t₃⟩ : ∃ h, (taint.check (Taint.ofRegs [.r14, .r15, .r16, .r19])
      (.block Impl.AesOfb.PPC64LE.ivArgs) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, t₄⟩ : ∃ h, (taint.check (Taint.ofRegs [.r16, .r30, .r31]) xorCode h).isSome = true :=
    ⟨_, by taint_decide⟩
  have tail (hu : fU s₀ ≠ 0) : RelCT isa
      (fun a b => (Whole M s₀ a ∧ a.sp = s₀.sp) ∧ (Whole M s₀' b ∧ b.sp = s₀'.sp))
      finalTail fun a b => (Done M s₀ a ∧ a.sp = s₀.sp) ∧ (Done M s₀' b ∧ b.sp = s₀'.sp) := by
    have hu' : fU s₀' ≠ 0 := qU ▸ hu
    have a₃ := (taintRegs
      (P := fun a b => (Whole M s₀ a ∧ a.sp = s₀.sp) ∧ (Whole M s₀' b ∧ b.sp = s₀'.sp)) _
      (fun a b h => ⟨by rw [h.1.2, h.2.2, qSp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [h.1.1.r14, h.2.1.r14, fW, fW, qW]
        · rw [h.1.1.r15, h.2.1.r15, qR]
        · rw [h.1.1.r16, h.2.1.r16, fIv, fIv, qIv]
        · rw [h.1.1.r19, h.2.1.r19, fS, fS, qS]⟩) t₃).wp
      (F₁ := fun (s : State) => IvA M s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => IvA M s₀' s ∧ s.sp = s₀'.sp)
      fun a b h => ⟨WP.mono (wp_sp (final_ivArgs_wp hp h.1.1)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
        WP.mono (wp_sp (final_ivArgs_wp hp' h.2.1)) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
    have a₄ := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
      Proof.Aes.PPC64LE.encryptBlocks_ct
      (P := fun a b => (IvA M s₀ a ∧ a.sp = s₀.sp) ∧ (IvA M s₀' b ∧ b.sp = s₀'.sp))
      fun a b h => by
        have e₂ := h.2.1.pre
        have eW : fW s₀' = fW s₀ := qW.symm
        have eIv : fIv s₀' = fIv s₀ := qIv.symm
        have eS : fS s₀' = fS s₀ := qS.symm
        have eR : fR s₀' = fR s₀ := by simp only [fR, qR]
        rw [eW, eIv, eS, eR] at e₂
        exact ⟨h.1.1.pre, e₂, by rw [h.1.2, h.2.2, qSp]⟩).wp
      (F₁ := fun (s : State) => Ciph M s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => Ciph M s₀' s ∧ s.sp = s₀'.sp)
      fun a b h => ⟨WP.mono (wp_sp (final_ciph_wp hp h.1.1)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
        WP.mono (wp_sp (final_ciph_wp hp' h.2.1)) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
    have a₅ := (taintRegs
      (P := fun a b => (Ciph M s₀ a ∧ a.sp = s₀.sp) ∧ (Ciph M s₀' b ∧ b.sp = s₀'.sp)) _
      (fun a b h => ⟨by rw [h.1.2, h.2.2, qSp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.1.1.r16, h.2.1.r16, fIv, fIv, qIv]
        · rw [h.1.1.r30, h.2.1.r30, qU]
        · rw [h.1.1.r31, h.2.1.r31, qT]⟩) t₄).wp
      (F₁ := fun (s : State) => Done M s₀ s ∧ s.sp = s₀.sp) (F₂ := fun (s : State) => Done M s₀' s ∧ s.sp = s₀'.sp)
      fun a b h => ⟨WP.mono (wp_sp (final_xor_wp hp h.1.1 hu)) fun _ x => ⟨x.1, x.2.trans h.1.2⟩,
        WP.mono (wp_sp (final_xor_wp hp' h.2.1 hu')) fun _ x => ⟨x.1, x.2.trans h.2.2⟩⟩
    exact (a₃.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((a₄.mono (fun _ _ h => h) fun _ _ h => h.2).seq (a₅.mono (fun _ _ h => h) fun _ _ h => h.2))
  have r₃ : RelCT isa
      (fun a b => (Whole M s₀ a ∧ a.sp = s₀.sp) ∧ (Whole M s₀' b ∧ b.sp = s₀'.sp))
      (.ite (.zero .d .r30) (.block []) finalTail)
      (fun a b => (Done M s₀ a ∧ a.sp = s₀.sp) ∧ (Done M s₀' b ∧ b.sp = s₀'.sp)) := by
    refine RelCT.ite (fun a b h => by rw [eval_u h.1.1, eval_u h.2.1, qU]) ?_ ?_
    · refine RelCT.block_nil fun a b h => ?_
      have h0 : fU s₀ = 0 := by
        have := h.2; rw [eval_u h.1.1.1] at this; simpa using this
      exact ⟨⟨done_of_zero h.1.1.1 h0, h.1.1.2⟩, ⟨done_of_zero h.1.2.1 (qU ▸ h0), h.1.2.2⟩⟩
    · refine (RelCT.exists_ fun (hu : fU s₀ ≠ 0) => tail hu).mono
        (fun a b h => ⟨?_, h.1⟩) fun _ _ h => h
      have := h.2; rw [eval_u h.1.1.1] at this; simpa using this
  -- The registers restored.
  obtain ⟨_, t₅⟩ : ∃ h, (taint.check (Taint.ofRegs [.r20]) (.block finalRestore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have r₄ := taintRegs
    (P := fun a b => (Done M s₀ a ∧ a.sp = s₀.sp) ∧ (Done M s₀' b ∧ b.sp = s₀'.sp)) _
    (fun a b h => ⟨by rw [h.1.2, h.2.2, qSp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.r20, h.2.1.r20, fV, fV, qV]⟩) t₅
  exact (r₁.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((r₂.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    (r₃.seq r₄))

theorem final_ct {enc : Bool} {M : Mode} {name : String} {whole : Prog isa}
    (hv : ∀ s, (modePPC64LE M).pre s →
      ∃ t s', Exec isa whole s t s' ∧ abiPreserved s s' ∧ (modePPC64LE M).post s s')
    (hct : ConstantTime isa (modePPC64LE M).pre (modePPC64LE M).pub whole)
    (nf : whole.noFrames = true) :
    ConstantTime isa (finalPPC64LE enc).pre (finalPPC64LE enc).pub (final name whole) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (final_rel hv hct nf h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## Verified -/

theorem encryptFinal_verified :
    Verified PPC64LE.target Impl.AesCfb.PPC64LE.encryptFinal (finalScratchContract true) :=
  Verified.of_correct (final_correct encrypt_correct encrypt_noFrames)
    (final_ct encrypt_correct (Proof.AesCbc.PPC64LE.whole_ct encBody_ok encBody_ct) encrypt_noFrames)
    (final_implies true)

theorem decryptFinal_verified :
    Verified PPC64LE.target Impl.AesCfb.PPC64LE.decryptFinal (finalScratchContract false) :=
  Verified.of_correct (final_correct decrypt_correct decrypt_noFrames)
    (final_ct decrypt_correct (Proof.AesCbc.PPC64LE.whole_ct decBody_ok decBody_ct) decrypt_noFrames)
    (final_implies false)

/-! ## With `save` on the stack

The final functions have six argument words, so `save` is their seventh,
in `r9`: they run their code in a frame of 96 bytes on the stack
(`withStackScratchWiped`), its 32-byte header and `save`'s 64 bytes, which
it zeroes before returning. The code's calls use no stack, so 96 in all. -/

/-- A state satisfying the shared contracts' precondition. -/
def finalFrameSat : State := { finalSat with wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2176⟩] }

theorem encFrameSat_pre : ∃ s, (encryptFinalRoundsContract PPC64LE.abi (0 + 96)).pre s := by
  implies_sat [encryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, encryptFinalPost, PPC64LE.abi,
    PPC64LE.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem decFrameSat_pre : ∃ s, (decryptFinalRoundsContract PPC64LE.abi (0 + 96)).pre s := by
  implies_sat [decryptFinalRoundsContract, Spec.Cfb.aesFinalSig, finalPre, decryptFinalPost, PPC64LE.abi,
    PPC64LE.argRegs] [finalFrameSat, finalSat] using finalFrameSat

theorem encryptFinal_framed :
    Verified PPC64LE.target
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r9 8 Impl.AesCfb.PPC64LE.encryptFinal)
      (encryptFinalRoundsContract PPC64LE.abi 96) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre PPC64LE.abi.ptrBits) (post := encryptFinalPost PPC64LE.abi.ptrBits) (wa := false)
    (stack := 0) (bytes := 96) (words := 8) encryptFinal_verified (by decide) (by decide) (by decide)
    (finalPre_local _) (encryptFinalPost_local _) (encryptFinalPost_localOut _) encFrameSat_pre

theorem decryptFinal_framed :
    Verified PPC64LE.target
      (Impl.StackScratch.PPC64LE.withStackScratchWiped 96 .r9 8 Impl.AesCfb.PPC64LE.decryptFinal)
      (decryptFinalRoundsContract PPC64LE.abi 96) :=
  PPC64LE.Verified.stackScratchWiped (sig := Spec.Cfb.aesFinalSig) (nm := "save") (e := .u64) (n := 8)
    (pre := finalPre PPC64LE.abi.ptrBits) (post := decryptFinalPost PPC64LE.abi.ptrBits) (wa := false)
    (stack := 0) (bytes := 96) (words := 8) decryptFinal_verified (by decide) (by decide) (by decide)
    (finalPre_local _) (decryptFinalPost_local _) (decryptFinalPost_localOut _) decFrameSat_pre

end VG.Proof.AesCfb.PPC64LE.Final
