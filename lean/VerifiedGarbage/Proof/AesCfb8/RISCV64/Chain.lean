module

public import VerifiedGarbage.Proof.Aes.RISCV64.ChainModes
public import VerifiedGarbage.Proof.Aes.RISCV64.ChainFrame
public import VerifiedGarbage.Proof.AesCfb8.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCfb8.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Aes.RISCV64.ChainModes
meta import VerifiedGarbage.Proof.Aes.RISCV64.ChainFrame
meta import VerifiedGarbage.Proof.AesCfb8.Spec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.AesCbc.Spec
meta import VerifiedGarbage.Proof.AesCfb8.Mem
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-CFB8 on RISC-V: the chain

`cfb8Chain enc` (`Impl/Aes/RISCV64/Chain.lean`) runs `chain`'s frame
(`ChainFrame.lean`) over the `n` bytes at `data`, with the input block in
two slots of the scratch buffer (58 and 63, `slotQ`), stored there from
the registers of block 0 before the loop and loaded back after it. Each
byte loads it into those registers, enciphers it (`encrypt4`), XORs its
first byte into the data byte, and shifts the input block left by a byte
with the ciphertext byte shifted in. After `k` bytes (`BAt`) the input
block is CFB8's after the first `k` bytes (`inK`), and those bytes are
CFB8's of them.

Its contract (`cfb8KRISCV64 enc`) is the functions' (`cfb8RISCV64 enc`),
with the first 2048 bytes of the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.AesCfb8.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes VG.Proof.Aes.RISCV64
open VG.Spec.Aes (bytesAt)

/-- `vg_aes_cfb8_encrypt` (`enc`) or `vg_aes_cfb8_decrypt`, with the
arguments `(schedule = a0, rounds = a1, iv = a2, data = a3, len = a4, scratch = a5)`. -/
def cfb8RISCV64 (enc : Bool) : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .a0, 240⟩
    let iv : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scr : Region := ⟨s.gpr .a5, 2176⟩
    s.rd = [sched] ∧ s.wr = [iv, data, scr] ∧
      sched.Disjoint iv ∧ sched.Disjoint data ∧ sched.Disjoint scr ∧ iv.Disjoint data ∧
      iv.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .a2).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14)
  post s s' :=
    let ciph := Spec.Cbc.aesWith (s.gpr .a1).toNat (bytesAt s.mem (s.gpr .a0) (16 * ((s.gpr .a1).toNat + 1)))
    let iv := bytesAt s.mem (s.gpr .a2) 16
    let xs := bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
    bytesAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat = cfb8 enc ciph iv xs ∧
      bytesAt s'.mem (s.gpr .a2) 16 = inK enc ciph iv xs
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.sp = s₂.sp

/-- The chain's contract: `cfb8RISCV64 enc`'s postcondition, with
`chain`'s precondition over `len` bytes (a scratch buffer of 2048 bytes). -/
def cfb8KRISCV64 (enc : Bool) : Contract isa where
  pre := framePre true id
  post := (cfb8RISCV64 enc).post
  pub := (cfb8RISCV64 enc).pub

/-! ## The input block -/

/-- The input block's two slots, as the registers of block 0. -/
abbrev slotQ (m : Mem) (b : Addr) : Nat → BitVec 64 :=
  fun i => if i = 0 then m.readW (b + BitVec.ofNat 64 464) 64 else m.readW (b + BitVec.ofNat 64 504) 64

/-- The input block shifted left by a byte, with the low byte of `c` shifted in. -/
theorem regBlock_shift (lo hi c : BitVec 64) :
    (regBlock (fun i => if i = 0 then lo >>> 8 ||| hi <<< 56 else hi >>> 8 ||| c <<< 56) 0).toList =
      (regBlock (fun i => if i = 0 then lo else hi) 0).toList.tail ++ [c.setWidth 8] := by
  apply List.ext_getElem (by simp)
  intro t h₁ h₂
  have ht : t < 16 := by simpa using h₁
  rw [Vector.getElem_toList]
  by_cases h15 : t < 15
  · rw [List.getElem_append_left (by simpa using h15), List.getElem_tail, Vector.getElem_toList]
    simp only [regBlock, Vector.getElem_ofFn, Nat.zero_add]
    refine byte_ext fun j hj => ?_
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    by_cases h8 : t < 7
    · rw [show t / 8 = 0 by omega, show (t + 1) / 8 = 0 by omega]
      simp only [Nat.mul_zero, ↓reduceIte, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_shiftLeft]
      rw [show 8 + (8 * (t % 8) + j) = 8 * ((t + 1) % 8) + j by omega]
      have : 8 * (t % 8) + j < 56 := by omega
      simp [this]
    · by_cases h7 : t = 7
      · subst h7
        simp only [show 7 / 8 = 0 from rfl, show (7 + 1) / 8 = 1 from rfl, Nat.mul_zero, Nat.mul_one,
          ↓reduceIte, show (4 = 0) = False by decide, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
          BitVec.getLsbD_shiftLeft]
        rw [show (7 + 1) % 8 = 0 from rfl, show 7 % 8 = 7 from rfl]
        have e1 : (lo.getLsbD (8 + (8 * 7 + j))) = false := BitVec.getLsbD_of_ge _ _ (by omega)
        rw [e1]
        simp [show ¬ (8 * 7 + j < 56) by omega, show 8 * 7 + j < 64 by omega, show 8 * 7 + j - 56 = j by omega]
      · rw [show t / 8 = 1 by omega, show (t + 1) / 8 = 1 by omega]
        simp only [Nat.mul_one, show (4 = 0) = False by decide, ↓reduceIte, BitVec.getLsbD_or,
          BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
        rw [show 8 + (8 * (t % 8) + j) = 8 * ((t + 1) % 8) + j by omega]
        have : 8 * (t % 8) + j < 56 := by omega
        simp [this]
  · have e : t = 15 := by omega
    subst e
    rw [List.getElem_append_right (by simp)]
    simp only [regBlock, Vector.getElem_ofFn, Nat.zero_add]
    refine byte_ext fun j hj => ?_
    simp only [show 15 / 8 = 1 from rfl, show 15 % 8 = 7 from rfl, Nat.mul_one,
      show (4 = 0) = False by decide, ↓reduceIte, BitVec.getLsbD_extractLsb', hj, decide_true,
      Bool.true_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    have e1 : (hi.getLsbD (8 + (8 * 7 + j))) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    rw [e1]
    simp [show ¬ (8 * 7 + j < 56) by omega, show 8 * 7 + j < 64 by omega, show 8 * 7 + j - 56 = j by omega, hj]

/-- The first byte of the registers of block 0. -/
theorem regBlock_zero (Q : Nat → BitVec 64) : (regBlock Q 0)[0] = (Q 0).setWidth 8 := by
  simp only [regBlock, Vector.getElem_ofFn]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [hj]

/-- A data byte XORed with the low byte of a register. -/
theorem xor_low (x : Byte) (y : BitVec 64) :
    ((x.setWidth 64) ^^^ (y &&& BitVec.ofInt 64 255)).setWidth 8 = x ^^^ y.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_and, hj, decide_true, Bool.true_and,
    show j < 64 by omega]
  rw [show BitVec.ofInt 64 255 = BitVec.allOnes 64 >>> 56 by decide, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes]
  simp [show 56 + j < 64 by omega]

/-! ## The slots -/

section Slots

variable {s : State} {X b : Addr} (hscr : Scr s X 2048) (hb : s.gpr sb = b)
include hscr hb

theorem slot_in (d : Nat) (hd : d + 8 + 7 ≤ 2048) : (⟨X, 2048⟩ : Region).Contains (b + BitVec.ofNat 64 d) 8 := by
  rw [← hb]; exact hscr.contains hd (by decide)

theorem slot_al (d : Nat) (hd : d % 8 = 0) : (b + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [← hb]; exact Align.al_add (k := 8) hscr.al (by decide) (by omega)

/-- The input block from its slots into the registers of block 0. -/
theorem slots_load {Φ : State → Prop}
    (k : ∀ s', regBlock (Q s') 0 = regBlock (slotQ s.mem b) 0 →
      (∀ r, r ≠ q 0 → r ≠ q 4 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → Φ s') :
    WP isa (.block [ldS (q 0) iLo, ldS (q 4) iHi]) s Φ := by
  refine wp_ld (t := q 0) (n := sb) (off := 8 * iLo) (a := b + BitVec.ofNat 64 464) (by decide)
    (by rw [hb]; rfl) (slot_al hscr hb 464 (by decide))
    ⟨_, List.mem_append_right _ hscr.wr, slot_in hscr hb 464 (by decide)⟩ fun s₁ u₁ => ?_
  refine wp_ld (t := q 4) (n := sb) (off := 8 * iHi) (a := b + BitVec.ofNat 64 504) (by decide)
    (by rw [u₁.other _ (by decide), hb]; rfl) (slot_al hscr hb 504 (by decide))
    ⟨_, by rw [u₁.rd, u₁.wr]; exact List.mem_append_right _ hscr.wr, slot_in hscr hb 504 (by decide)⟩
    fun s₂ u₂ => WP.block_nil ?_
  refine k s₂ (regBlock_congr ?_ ?_) (fun r h0 h4 => by rw [u₂.other _ h4, u₁.other _ h0])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  · show s₂.gpr (q 0) = _
    rw [u₂.other _ (by decide), u₁.gpr]; rfl
  · show s₂.gpr (q 4) = _
    rw [u₂.gpr, u₁.mem]; rfl

/-- The registers of block 0 into the input block's slots. -/
theorem slots_store {Φ : State → Prop}
    (k : ∀ s', regBlock (slotQ s'.mem b) 0 = regBlock (Q s) 0 → (∀ r, s'.gpr r = s.gpr r) →
      s'.mem = (s.mem.writeW (b + BitVec.ofNat 64 464) (s.gpr (q 0))).writeW (b + BitVec.ofNat 64 504)
        (s.gpr (q 4)) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Φ s') :
    WP isa (.block [stS iLo (q 0), stS iHi (q 4)]) s Φ := by
  refine wp_sd (t := q 0) (n := sb) (off := 8 * iLo) (a := b + BitVec.ofNat 64 464) (by decide)
    (by rw [hb]; rfl) (slot_al hscr hb 464 (by decide)) ⟨_, hscr.wr, slot_in hscr hb 464 (by decide)⟩
    fun s₁ u₁ => ?_
  refine wp_sd (t := q 4) (n := sb) (off := 8 * iHi) (a := b + BitVec.ofNat 64 504) (by decide)
    (by rw [u₁.gpr, hb]; rfl) (slot_al hscr hb 504 (by decide))
    ⟨_, by rw [u₁.wr]; exact hscr.wr, slot_in hscr hb 504 (by decide)⟩ fun s₂ u₂ => WP.block_nil ?_
  have hm : s₂.mem = (s.mem.writeW (b + BitVec.ofNat 64 464) (s.gpr (q 0))).writeW (b + BitVec.ofNat 64 504)
      (s.gpr (q 4)) := by rw [u₂.mem, u₁.mem, u₁.gpr]
  refine k s₂ (regBlock_congr ?_ ?_) (fun r => by rw [u₂.gpr, u₁.gpr]) hm (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  · show s₂.mem.readW (b + BitVec.ofNat 64 464) 64 = s.gpr (q 0)
    rw [hm, Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · show s₂.mem.readW (b + BitVec.ofNat 64 504) 64 = s.gpr (q 4)
    rw [hm, Mem.readW_writeW_self64]

/-- The input block in its slots shifted left by a byte, with the low byte of
`t2` shifted in; on to the next byte. -/
theorem shift_ok {Φ : State → Prop}
    (k : ∀ s', (regBlock (slotQ s'.mem b) 0).toList =
        (regBlock (slotQ s.mem b) 0).toList.tail ++ [(s.gpr .t2).setWidth 8] →
      Frame [⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩] s.mem s'.mem →
      s'.gpr .a3 = s.gpr .a3 + BitVec.ofNat 64 1 → s'.gpr .a4 = s.gpr .a4 - BitVec.ofNat 64 1 →
      (∀ r, r ≠ t0 → r ≠ t1 → r ≠ .t3 → r ≠ .a3 → r ≠ .a4 → s'.gpr r = s.gpr r) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Φ s') :
    WP isa (.block cfb8Shift) s Φ := by
  unfold cfb8Shift
  refine wp_ld (t := t0) (n := sb) (off := 8 * iLo) (a := b + BitVec.ofNat 64 464) (by decide)
    (by rw [hb]; rfl) (slot_al hscr hb 464 (by decide))
    ⟨_, List.mem_append_right _ hscr.wr, slot_in hscr hb 464 (by decide)⟩ fun s₁ u₁ => ?_
  refine wp_ld (t := t1) (n := sb) (off := 8 * iHi) (a := b + BitVec.ofNat 64 504) (by decide)
    (by rw [u₁.other _ (by decide), hb]; rfl) (slot_al hscr hb 504 (by decide))
    ⟨_, by rw [u₁.rd, u₁.wr]; exact List.mem_append_right _ hscr.wr, slot_in hscr hb 504 (by decide)⟩
    fun s₂ u₂ => ?_
  refine wp_srl (by decide) fun s₃ u₃ => wp_sll (by decide) fun s₄ u₄ => wp_or fun s₅ u₅ => ?_
  refine wp_srl (by decide) fun s₆ u₆ => wp_sll (by decide) fun s₇ u₇ => wp_or fun s₈ u₈ => ?_
  have o₈ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ .t3 → s₈.gpr r = s.gpr r := fun r h0 h1 h3 => by
    rw [u₈.other _ h1, u₇.other _ h3, u₆.other _ h1, u₅.other _ h0, u₄.other _ h3, u₃.other _ h0,
      u₂.other _ h1, u₁.other _ h0]
  have m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have sp₈ : s₈.sp = s.sp := by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  let lo := s.mem.readW (b + BitVec.ofNat 64 464) 64
  let hi := s.mem.readW (b + BitVec.ofNat 64 504) 64
  have t0₈ : s₈.gpr t0 = lo >>> 8 ||| hi <<< 56 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
  have t1₈ : s₈.gpr t1 = hi >>> 8 ||| s.gpr .t2 <<< 56 := by
    rw [u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine wp_sd (t := t0) (n := sb) (off := 8 * iLo) (a := b + BitVec.ofNat 64 464) (by decide)
    (by rw [o₈ _ (by decide) (by decide) (by decide), hb]; rfl) (slot_al hscr hb 464 (by decide))
    ⟨_, by rw [wr₈]; exact hscr.wr, slot_in hscr hb 464 (by decide)⟩ fun s₉ u₉ => ?_
  refine wp_sd (t := t1) (n := sb) (off := 8 * iHi) (a := b + BitVec.ofNat 64 504) (by decide)
    (by rw [u₉.gpr, o₈ _ (by decide) (by decide) (by decide), hb]; rfl) (slot_al hscr hb 504 (by decide))
    ⟨_, by rw [u₉.wr, wr₈]; exact hscr.wr, slot_in hscr hb 504 (by decide)⟩ fun s₁₀ u₁₀ => ?_
  refine wp_addi (imm := 1) (by decide) fun s₁₁ u₁₁ => wp_subi (imm := 1) (by decide)
    fun s₁₂ u₁₂ => WP.block_nil ?_
  have hm : s₁₂.mem = (s.mem.writeW (b + BitVec.ofNat 64 464) (lo >>> 8 ||| hi <<< 56)).writeW
      (b + BitVec.ofNat 64 504) (hi >>> 8 ||| s.gpr .t2 <<< 56) := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₉.gpr, m₈, t0₈, t1₈]
  refine k s₁₂ ?_ ?_ ?_ ?_ (fun r h0 h1 h3 h3' h4 => ?_) (by rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, rd₈])
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈]) (by rw [u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, sp₈])
  · rw [← regBlock_shift lo hi (s.gpr .t2)]
    congr 1
    refine regBlock_congr ?_ ?_
    · show s₁₂.mem.readW (b + BitVec.ofNat 64 464) 64 = _
      rw [hm, Mem.readW_writeW_sep (Offset.sep b (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]; rfl
    · show s₁₂.mem.readW (b + BitVec.ofNat 64 504) 64 = _
      rw [hm, Mem.readW_writeW_self64]; rfl
  · rw [hm]
    exact ((Frame.refl _ _).writeW (r := ⟨b + BitVec.ofNat 64 464, 8⟩) (by simp) _
      (Region.contains_self _ 8)).writeW (r := ⟨b + BitVec.ofNat 64 504, 8⟩) (by simp) _
      (Region.contains_self _ 8)
  · rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, o₈ _ (by decide) (by decide) (by decide)]
  · rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, o₈ _ (by decide) (by decide) (by decide)]
  · rw [u₁₂.other _ h4, u₁₁.other _ h3', u₁₀.gpr, u₉.gpr, o₈ r h0 h1 h3]

end Slots

/-- `C#ⱼ` (if `enc`) or `P#ⱼ` (else) over the data byte at `a3`: the byte XORed
with the first byte of the registers of block 0, the ciphertext byte left
in `t2`. -/
theorem byte_ok (enc : Bool) {s : State} {P : Addr} (hP : s.gpr .a3 = P)
    (hin : InRegions s.wr P 1) {Φ : State → Prop}
    (k : ∀ s', s'.mem = s.mem.writeW P (s.mem P ^^^ (s.gpr (q 0)).setWidth 8) →
      (s'.gpr .t2).setWidth 8 = (if enc then s.mem P ^^^ (s.gpr (q 0)).setWidth 8 else s.mem P) →
      (∀ r, r ≠ t1 → r ≠ .t2 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Φ s') :
    WP isa (.block (if enc then cfb8Enc else cfb8Dec)) s Φ := by
  have hrw : InRegions (s.rd ++ s.wr) P 1 := by
    obtain ⟨r, hr, hc⟩ := hin; exact ⟨r, List.mem_append_right _ hr, hc⟩
  cases enc
  · unfold cfb8Dec
    refine wp_lbu (a := P) (by decide) (by rw [hP]; simp) hrw fun s₁ u₁ => ?_
    refine wp_andi (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
    refine wp_sb (a := P) (by decide)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hP]; simp)
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hin) fun s₄ u₄ => WP.block_nil ?_
    have t1₃ : s₃.gpr t1 = (s.gpr (q 0) &&& BitVec.ofInt 64 255) ^^^ (s.mem P).setWidth 64 := by
      rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.gpr, u₁.other _ (by decide)]
    refine k s₄ ?_ ?_ (fun r h1 h2 => ?_) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp])
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, t1₃, BitVec.xor_comm, xor_low]
    · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      simp [hj]
    · rw [u₄.gpr, u₃.other _ h1, u₂.other _ h1, u₁.other _ h2]
  · unfold cfb8Enc
    refine wp_lbu (a := P) (by decide) (by rw [hP]; simp) hrw fun s₁ u₁ => ?_
    refine wp_andi (by decide) fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
    refine wp_sb (a := P) (by decide)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hP]; simp)
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hin) fun s₄ u₄ => WP.block_nil ?_
    have t2₃ : s₃.gpr .t2 = (s.mem P).setWidth 64 ^^^ (s.gpr (q 0) &&& BitVec.ofInt 64 255) := by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.other _ (by decide)]
    refine k s₄ ?_ ?_ (fun r h1 h2 => ?_) (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
      (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp])
    · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, t2₃, xor_low]
    · rw [u₄.gpr, t2₃, xor_low]; rfl
    · rw [u₄.gpr, u₃.other _ h2, u₂.other _ h1, u₁.other _ h2]

/-! ## The loop -/

theorem writeW8_self (m : Mem) (p : Addr) (v : Byte) : m.writeW p v p = v := by
  rw [AesCfb8.writeW8_apply, BitVec.sub_self]; simp

/-- Byte `D + j` after a byte store at `D + k`. -/
theorem writeW8_ne (m : Mem) (D : Addr) {j k : Nat} (hj : j < 2 ^ 64) (hk : k < 2 ^ 64) (h : j ≠ k)
    (v : Byte) : m.writeW (D + BitVec.ofNat 64 k) v (D + BitVec.ofNat 64 j) = m (D + BitVec.ofNat 64 j) := by
  rw [AesCfb8.writeW8_apply]
  have : ¬ ((D + BitVec.ofNat 64 j) - (D + BitVec.ofNat 64 k)).toNat < 1 := fun hc =>
    Offset.disjoint D (d := k) (n := 1) (e := j) (k := 1) (by omega) (by omega) (by omega) _
      (by simp only [Region.Contains]; omega) (Region.contains_self _ _)
  simp only [this, ↓reduceIte]

theorem headD_toList (v : Spec.Aes.State) : v.toList.headD 0 = v[0] := by
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, Vector.getElem?_toList]; rfl

/-- What the loop runs with: `s₂` is the state after the input block is
stored in its slots, `X` the scratch buffer (rounded to `b`), `D` the data
(`n` bytes). -/
structure B8Setup (s₂ : State) (X b D : Addr) (n R : Nat) (w : List Byte) : Prop where
  scr : Scr s₂ X 2048
  base : s₂.gpr sb = b
  masks : MasksAt s₂.mem b allKs
  dat : (⟨D, n⟩ : Region) ∈ s₂.wr
  hn : n < 2 ^ 64
  sep : Region.Disjoint ⟨D, n⟩ ⟨X, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w
  a0 : s₂.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R)

section Loop

variable {m₀ : Mem} {s₂ : State} {X b D : Addr} {n R : Nat} {w iv : List Byte}

/-- The scratch buffer's regions `fRegions` has, within it. -/
theorem B8Setup.sub (hs : B8Setup s₂ X b D n R w) {d l : Nat} (h : d + l + 7 ≤ 2048) :
    Region.Sub ⟨b + BitVec.ofNat 64 d, l⟩ ⟨X, 2048⟩ := by
  rw [← hs.base]; exact hs.scr.sub h

theorem B8Setup.dX (hs : B8Setup s₂ X b D n R w) :
    ∀ r ∈ [(⟨b, 320⟩ : Region), ⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩],
      Region.Disjoint ⟨D, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine hs.sep.sub_right ?_
    have := hs.sub (d := 0) (l := 320) (by omega)
    simpa using this
  · exact hs.sep.sub_right (hs.sub (by omega))
  · exact hs.sep.sub_right (hs.sub (by omega))

theorem B8Setup.masks_disj (hs : B8Setup s₂ X b D n R w) : ∀ r ∈ fRegions b D n,
    Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧
      Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨Offset.disjoint_base b (by omega) (by omega), Offset.disjoint_base b (by omega) (by omega)⟩
  · exact ⟨Offset.disjoint b (by omega) (by omega) (by omega), Offset.disjoint b (by omega) (by omega) (by omega)⟩
  · exact ⟨Offset.disjoint b (by omega) (by omega) (by omega), Offset.disjoint b (by omega) (by omega) (by omega)⟩
  · exact ⟨(hs.sep.sub_right (hs.sub (by omega))).symm, (hs.sep.sub_right (hs.sub (by omega))).symm⟩

theorem B8Setup.keys_disj (hs : B8Setup s₂ X b D n R w) :
    ∀ r ∈ fRegions b D n, Region.Disjoint ⟨b + 1024, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact keys_disjoint b
  · exact Offset.disjoint b (d := 1024) (by omega) (by omega) (by omega)
  · exact Offset.disjoint b (d := 1024) (by omega) (by omega) (by omega)
  · exact (hs.sep.sub_right (hs.sub (d := 1024) (l := 960) (by omega))).symm

/-- The input block enciphered in the registers of block 0. -/
theorem enc8_ok (hs : B8Setup s₂ X b D n R w) {s : State}
    (keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₂.gpr r)
    (hwr : s.wr = s₂.wr) (hf : Frame (fRegions b D n) s₂.mem s.mem) :
    WP isa encrypt4 s fun s₅ => regBlock (Q s₅) 0 = Spec.Aes.cipher R w (regBlock (Q s) 0) ∧
      (∀ r, r ∉ sboxWrites → r ≠ kp → s₅.gpr r = s.gpr r) ∧ Frame [⟨b, 320⟩] s.mem s₅.mem ∧
      s₅.rd = s.rd ∧ s₅.wr = s.wr ∧ s₅.sp = s.sp := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hb : s.gpr sb = b := by rw [keep sb (by decide) (by decide) (by decide) (by decide), hs.base]
  have a0 : s.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
    rw [keep .a0 (by decide) (by decide) (by decide) (by decide)]; exact hs.a0
  have hp : EncPre s X R w :=
    ⟨hs.scr.congr hwr (by rw [hb, hs.base]), by rw [hb]; exact masks_frame hf hs.masks_disj hs.masks,
      hs.rounds, by rw [a0, hb], by rw [a0]; exact keysAt_frame hR hf hs.keys_disj hs.keys⟩
  refine WP.mono (encrypt4_ok hp (inRel_regBlock (Q s))) fun s₅ ⟨hc₅, hin₅⟩ =>
    ⟨regBlock_of_inRel hin₅ (by decide), hc₅.keep, by have := hc₅.frame; rw [hb] at this; exact this,
      hc₅.rd, hc₅.wr, hc₅.sp⟩

/-- After `k` bytes: the input block CFB8's after the first `k` bytes, which
are CFB8's of them, and the other bytes `m₀`'s. -/
structure BAt (enc : Bool) (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w iv : List Byte) (k : Nat)
    (s : State) : Prop where
  hk : k ≤ n
  a3 : s.gpr .a3 = D + BitVec.ofNat 64 k
  a4 : s.gpr .a4 = BitVec.ofNat 64 (n - k)
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s.gpr r = s₂.gpr r
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  frame : Frame (fRegions b D n) s₂.mem s.mem
  inb : (regBlock (slotQ s.mem b) 0).toList = inK enc (Spec.Cbc.aesWith R w) iv ((bytesAt m₀ D n).take k)
  done : bytesAt s.mem D k = cfb8 enc (Spec.Cbc.aesWith R w) iv ((bytesAt m₀ D n).take k)
  rest : ∀ j, k ≤ j → j < n → s.mem (D + BitVec.ofNat 64 j) = m₀ (D + BitVec.ofNat 64 j)

theorem take_bytesAt (m : Mem) (D : Addr) {n k : Nat} (hk : k < n) :
    (bytesAt m D n).take (k + 1) = (bytesAt m D n).take k ++ [m (D + BitVec.ofNat 64 k)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [bytesAt]; omega)]
  simp [bytesAt]

theorem bytesAt_succ (m : Mem) (D : Addr) (k : Nat) :
    bytesAt m D (k + 1) = bytesAt m D k ++ [m (D + BitVec.ofNat 64 k)] := by
  simp only [bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- One byte: from after `k` bytes to after `k + 1`. -/
theorem body8_ok (enc : Bool) (hs : B8Setup s₂ X b D n R w) (hiv : iv ≠ []) {k : Nat} (hkn : k < n)
    {s : State} (hi : BAt enc m₀ s₂ b D n R w iv k s) :
    WP isa (cfb8Body enc) s fun s' => isa.eval (.nonzero .a4) s' = some (decide (n - (k + 1) ≠ 0)) ∧
      BAt enc m₀ s₂ b D n R w iv (k + 1) s' := by
  have hn := hs.hn
  have hb : s.gpr sb = b := (hi.keep sb (by decide) (by decide) (by decide) (by decide)).trans hs.base
  have hscr : Scr s X 2048 := hs.scr.congr hi.wr (by rw [hb, hs.base])
  have dX := hs.dX
  unfold cfb8Body
  refine WP.seq (slots_load hscr hb fun s₁ st₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_)
  have keep₁ : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a3 → r ≠ .a4 → s₁.gpr r = s₂.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [o₁ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide))]; exact hi.keep r h1 h2 h3 h4
  refine WP.seq (WP.mono (enc8_ok hs keep₁ (by rw [wr₁, hi.wr]) (by rw [m₁]; exact hi.frame))
    fun s₅ ⟨st₅, keep₅, fr₅, rd₅, wr₅, sp₅⟩ => ?_)
  rw [WP.block_append_iff (M := isa)]
  have a3₅ : s₅.gpr .a3 = D + BitVec.ofNat 64 k := by
    rw [keep₅ _ (by decide) (by decide), o₁ _ (by decide) (by decide)]; exact hi.a3
  have hDw : (⟨D, n⟩ : Region) ∈ s₅.wr := by rw [wr₅, wr₁, hi.wr]; exact hs.dat
  refine byte_ok enc a3₅ (in_off hDw (by omega) hn) fun s₆ m₆ t2₆ o₆ rd₆ wr₆ sp₆ => ?_
  have hb₆ : s₆.gpr sb = b := by
    rw [o₆ _ (by decide) (by decide), keep₅ _ (by decide) (by decide), o₁ _ (by decide) (by decide), hb]
  have hscr₆ : Scr s₆ X 2048 := hscr.congr (by rw [wr₆, wr₅, wr₁]) (by rw [hb₆, hb])
  refine shift_ok hscr₆ hb₆ fun s₇ inb₇ fr₇ a3₇ a4₇ o₇ rd₇ wr₇ sp₇ => ?_
  -- The data byte, and the first byte of the enciphered input block.
  let P := D + BitVec.ofNat 64 k
  let ciph := Spec.Cbc.aesWith R w
  let xs := (bytesAt m₀ D n).take k
  have x₅ : s₅.mem P = m₀ P := by
    have e := fr₅.bytes (R := ⟨D, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dX _ (by simp)) (by simp only; omega) hkn
    rw [e, m₁]; exact hi.rest k (Nat.le_refl _) hkn
  have c₅ : (s₅.gpr (q 0)).setWidth 8 = (ciph (inK enc ciph iv xs)).headD 0 := by
    rw [← hi.inb, show ciph = Spec.Cbc.aesWith R w from rfl, aesWith_toList, headD_toList, ← st₁, ← st₅,
      regBlock_zero]
  -- The slots, unchanged until the shift.
  have sl₆ : regBlock (slotQ s₆.mem b) 0 = regBlock (slotQ s.mem b) 0 := by
    have hd : ∀ d, d = 464 ∨ d = 504 → s₆.mem.readW (b + BitVec.ofNat 64 d) 64 =
        s.mem.readW (b + BitVec.ofNat 64 d) 64 := fun d hd => by
      have hsl : Region.Disjoint ⟨b + BitVec.ofNat 64 d, 8⟩ ⟨D, n⟩ := (dX _ (by rcases hd with rfl | rfl <;> simp)).symm
      have hsP : Region.Disjoint ⟨b + BitVec.ofNat 64 d, 8⟩ ⟨P, 1⟩ :=
        hsl.sub_right (Offset.sub_base D (by omega))
      rw [m₆, Mem.readW_writeW_sep (fun x h₁ h₂ => hsP x h₁ h₂) (by decide),
        fr₅.readW (r := ⟨b + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rcases hd with rfl | rfl
          · exact Offset.disjoint_base b (by omega) (by omega)
          · exact Offset.disjoint_base b (by omega) (by omega)) (by decide), m₁]
    exact regBlock_congr (hd 464 (.inl rfl)) (hd 504 (.inr rfl))
  -- Bytes other than `P`, unchanged.
  have other : ∀ j < n, j ≠ k → s₇.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) := by
    intro j hj hjk
    have e₇ := fr₇.bytes (R := ⟨D, n⟩) (fun r hr => dX r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) (by simp only; omega) hj
    have e₅ := fr₅.bytes (R := ⟨D, n⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dX _ (by simp)) (by simp only; omega) hj
    simp only at e₇ e₅
    rw [e₇, m₆, writeW8_ne _ D (by omega) (by omega) hjk, e₅, m₁]
  have self₇ : s₇.mem P = m₀ P ^^^ (ciph (inK enc ciph iv xs)).headD 0 := by
    have e₇ := fr₇.bytes (R := ⟨D, n⟩) (fun r hr => dX r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp)) (by simp only; omega) hkn
    simp only at e₇
    rw [e₇, m₆, writeW8_self, x₅, c₅]
  have tk := take_bytesAt m₀ D hkn
  have x₀ : (bytesAt m₀ D n).take (k + 1) = xs ++ [m₀ P] := tk
  refine ⟨Steps.eval_nonzero_ofNat s₇ .a4 (by omega) ?a4, ?_⟩
  case a4 =>
    rw [a4₇, o₆ _ (by decide) (by decide), keep₅ _ (by decide) (by decide), o₁ _ (by decide) (by decide),
      hi.a4, ofNat_sub_ofNat' (by omega), show n - k - 1 = n - (k + 1) by omega]
  refine ⟨by omega, ?_, ?_, fun r h1 h2 h3 h4 => ?_, by rw [rd₇, rd₆, rd₅, rd₁, hi.rd],
    by rw [wr₇, wr₆, wr₅, wr₁, hi.wr], by rw [sp₇, sp₆, sp₅, sp₁, hi.sp], ?_, ?_, ?_, ?_⟩
  · rw [a3₇, o₆ _ (by decide) (by decide), a3₅, Offset.add_add]
  · rw [a4₇, o₆ _ (by decide) (by decide), keep₅ _ (by decide) (by decide), o₁ _ (by decide) (by decide),
      hi.a4, ofNat_sub_ofNat' (by omega), show n - k - 1 = n - (k + 1) by omega]
  · rw [o₇ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)) h3 h4,
      o₆ r (fun e => h1 (e ▸ by decide)) (fun e => h1 (e ▸ by decide)), keep₅ r h1 h2]
    exact keep₁ r h1 h2 h3 h4
  · -- The frame.
    have f₆ : Frame (fRegions b D n) s₂.mem s₆.mem := by
      rw [m₆]
      refine ((hi.frame.trans (m₁ ▸ fr₅.mono fun r hr => by simp at hr; simp [hr]))).writeW
        (r := ⟨D, n⟩) (by simp) _ ?_
      show Region.Contains _ (D + BitVec.ofNat 64 k) 1
      exact Offset.contains_base D (by omega) (by omega)
    exact f₆.trans (fr₇.mono fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp)
  · rw [inb₇, sl₆, hi.inb, x₀, inK_snoc enc ciph hiv]
    congr 2
    rw [t2₆, x₅, c₅]
  · rw [bytesAt_succ, x₀, cfb8_snoc enc ciph hiv, ← hi.done, self₇]
    congr 1
    simp only [bytesAt]
    refine List.map_congr_left fun j hj => other j (by simp at hj; omega) (by simp at hj; omega)
  · intro j hj hjn
    rw [other j hjn (by omega)]; exact hi.rest j (by omega) hjn

/-- The loop over the bytes. -/
theorem loop8_ok (enc : Bool) (hs : B8Setup s₂ X b D n R w) (hiv : iv ≠ []) (hn0 : 0 < n) {s : State}
    (hi : BAt enc m₀ s₂ b D n R w iv 0 s) :
    WP isa (.loop (cfb8Body enc) (.nonzero .a4)) s (BAt enc m₀ s₂ b D n R w iv n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ BAt enc m₀ s₂ b D n R w iv k s)
    (fun m s ⟨k, hm, hk, h⟩ => WP.mono (body8_ok enc hs hiv hk h) fun s' ⟨ev, h'⟩ => ?_) n s
    ⟨0, by omega, hn0, hi⟩
  by_cases hl : n - (k + 1) = 0
  · have e : k + 1 = n := by omega
    exact .inl ⟨by rw [ev]; simp [hl], e ▸ h'⟩
  · exact .inr ⟨by rw [ev]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

end Loop

/-! ## The whole function -/

/-- The input block's slots, outside the masks and the round keys. -/
theorem slots_disj (b : Addr) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 464, 8⟩ : Region), ⟨b + BitVec.ofNat 64 504, 8⟩],
      (Region.Disjoint ⟨b + BitVec.ofNat 64 416, 48⟩ r ∧ Region.Disjoint ⟨b + BitVec.ofNat 64 512, 96⟩ r) ∧
        Region.Disjoint ⟨b + 1024, 960⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨⟨Offset.disjoint b (by omega) (by omega) (by omega), Offset.disjoint b (by omega) (by omega) (by omega)⟩,
      Offset.disjoint b (d := 1024) (by omega) (by omega) (by omega)⟩
  · exact ⟨⟨Offset.disjoint b (by omega) (by omega) (by omega), Offset.disjoint b (by omega) (by omega) (by omega)⟩,
      Offset.disjoint b (d := 1024) (by omega) (by omega) (by omega)⟩

theorem frame_slots (m : Mem) (b : Addr) (v₁ v₂ : BitVec 64) :
    Frame [⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩] m
      ((m.writeW (b + BitVec.ofNat 64 464) v₁).writeW (b + BitVec.ofNat 64 504) v₂) :=
  ((Frame.refl _ _).writeW (r := ⟨b + BitVec.ofNat 64 464, 8⟩) (by simp) _
    (Region.contains_self _ 8)).writeW (r := ⟨b + BitVec.ofNat 64 504, 8⟩) (by simp) _
    (Region.contains_self _ 8)

theorem cfb8Chain_correct (enc : Bool) {s₀ : State} (hp : (cfb8KRISCV64 enc).pre s₀) :
    WP isa (cfb8Chain enc) s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        (cfb8KRISCV64 enc).post s₀ s' := by
  let n := (s₀.gpr .a4).toNat
  let R := (s₀.gpr .a1).toNat
  let St := s₀.gpr .a2
  let D := s₀.gpr .a3
  let w := bytesAt s₀.mem (s₀.gpr .a0) (16 * (R + 1))
  let iv := bytesAt s₀.mem St 16
  have hp' : framePre true id s₀ := hp
  have dDSt : Region.Disjoint ⟨D, n⟩ ⟨St, 16⟩ := hp.2.2.2.1
  have hiv : iv ≠ [] := fun h => by simpa [iv, bytesAt] using congrArg List.length h
  have hn : n < 2 ^ 64 := (s₀.gpr .a4).isLt
  let Res : State → Prop := fun s =>
    (regBlock (Q s) 0).toList = inK enc (Spec.Cbc.aesWith R w) iv (bytesAt s₀.mem D n) ∧
      bytesAt s.mem D n = cfb8 enc (Spec.Cbc.aesWith R w) iv (bytesAt s₀.mem D n)
  have hlen : (bytesAt s₀.mem D n).length ≤ n := by simp [bytesAt]
  unfold cfb8Chain
  refine WP.mono (frame_wp (Res := Res) hp' fun s₉ X b hsF => ?_) fun s' ⟨hg, hra, hm⟩ => ⟨hg, hra, ?_⟩
  · have hR : R ≤ 14 := by rcases hsF.rounds with h | h | h <;> omega
    refine slots_store hsF.scr hsF.base fun s₂ sl₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
    have f₂ : Frame [⟨b + BitVec.ofNat 64 464, 8⟩, ⟨b + BitVec.ofNat 64 504, 8⟩] s₉.mem s₂.mem := by
      rw [m₂]; exact frame_slots _ _ _ _
    have sd := slots_disj b
    have hs : B8Setup s₂ X b D n R w :=
      { scr := hsF.scr.congr wr₂ (by rw [g₂])
        base := by rw [g₂]; exact hsF.base
        masks := masks_frame f₂ (fun r hr => (sd r hr).1) hsF.masks
        dat := by rw [wr₂]; exact hsF.dat rfl
        hn := hn
        sep := hsF.sep
        rounds := hsF.rounds
        keys := keysAt_frame hR f₂ (fun r hr => (sd r hr).2) hsF.keys
        a0 := by rw [g₂]; exact hsF.a0 }
    have dX := hs.dX
    have bi₀ : BAt enc s₀.mem s₂ b D n R w iv 0 s₂ :=
      { hk := Nat.zero_le _
        a3 := by rw [g₂, hsF.a3]; simp [D]
        a4 := by rw [g₂, hsF.a4]; simp [n]
        keep := fun _ _ _ _ _ => rfl
        rd := rfl
        wr := rfl
        sp := rfl
        frame := Frame.refl _ _
        inb := by
          rw [List.take_zero, inK_nil, sl₂, hsF.st, ← AesCbc.bytesAt_toList]
        done := by rw [List.take_zero, cfb8_nil]; rfl
        rest := fun j _ hj => by
          have e₂ := f₂.bytes (R := ⟨D, n⟩) (fun r hr => dX r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp))
            (by simp only; omega) hj
          have e₀ := hsF.f₀.bytes (R := ⟨D, n⟩) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact hsF.sep) (by simp only; omega) hj
          simp only at e₂ e₀
          rw [e₂, e₀] }
    refine WP.mono (loop8_ok enc hs hiv hsF.hn0 bi₀) fun s₃ c => ?_
    have hb₃ : s₃.gpr sb = b := (c.keep sb (by decide) (by decide) (by decide) (by decide)).trans hs.base
    refine slots_load (hs.scr.congr c.wr (by rw [hb₃, hs.base])) hb₃ fun s₄ st₄ o₄ m₄ rd₄ wr₄ sp₄ => ?_
    exact { base := by rw [o₄ _ (by decide) (by decide)]; exact hb₃
            ra := by
              rw [o₄ _ (by decide) (by decide), c.keep .ra (by decide) (by decide) (by decide) (by decide), g₂]
            rd := by rw [rd₄, c.rd, rd₂]
            wr := by rw [wr₄, c.wr, wr₂]
            sp := by rw [sp₄, c.sp, sp₂]
            frame := by
              rw [m₄]
              refine (f₂.mono fun r hr => ?_).trans c.frame
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with rfl | rfl <;> simp
            res := ⟨by rw [st₄, c.inb, List.take_of_length_le hlen],
              by rw [m₄, c.done, List.take_of_length_le hlen]⟩ }
  · show bytesAt s'.mem D n = cfb8 enc (Spec.Cbc.aesWith R w) iv (bytesAt s₀.mem D n) ∧
      bytesAt s'.mem St 16 = inK enc (Spec.Cbc.aesWith R w) iv (bytesAt s₀.mem D n)
    rcases hm with ⟨hn0, hmem⟩ | ⟨s, ⟨hst, hdat⟩, hmem⟩
    · rw [hmem, show n = 0 from hn0, show bytesAt s₀.mem D 0 = [] from rfl, cfb8_nil, inK_nil]
      exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hmem, AesCbc.RISCV64.bytesAt_frame (frame_writeW2 _ _ _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dDSt) (by omega), hdat]
    · rw [hmem, bytesAt_writeW2 _ _ _ _ (regBlock_bytes (Q := Q s) rfl), hst]

/-! ## Constant time, and the call -/

theorem cfb8_agree (enc : Bool) :
    ∀ s₁ s₂, (cfb8KRISCV64 enc).pre s₁ → (cfb8KRISCV64 enc).pre s₂ → (cfb8KRISCV64 enc).pub s₁ s₂ →
      taint.Agree (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5]) s₁ s₂ := by
  rintro s₁ s₂ - - ⟨h0, h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3, h4, h5]

theorem cfb8Chain_ct (enc : Bool) :
    ConstantTime isa (cfb8KRISCV64 enc).pre (cfb8KRISCV64 enc).pub (cfb8Chain enc) := by
  cases enc
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
      (cfb8_agree _) (by taint_decide)
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
      (cfb8_agree _) (by taint_decide)

/-- The chain, as a chain to call. -/
theorem cfb8Chain_k (enc : Bool) : AesCbc.RISCV64.ChainK true id (cfb8KRISCV64 enc) (cfb8Chain enc) where
  pre _ h := h
  pub_of _ _ h := h
  correct s hs := by
    obtain ⟨t, s', he, hg, hra, hp⟩ := cfb8Chain_correct enc hs
    exact ⟨t, s', he, ⟨hg, Exec.sp he, hra⟩, hp⟩
  ct := cfb8Chain_ct enc
  noFrames := by cases enc <;> rfl
  post {s₀ s t t'} h hg hm ht hp := by
    have g0 := hg .a0 (by simp)
    have g1 := hg .a1 (by simp)
    have g2 := hg .a2 (by simp)
    have g3 := hg .a3 (by simp)
    have g4 := hg .a4 (by simp)
    have edata : bytesAt (AesCbc.RISCV64.chMem s₀) (s₀.gpr .a3) (s₀.gpr .a4).toNat =
        bytesAt s₀.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat := h.data_eq
    simp only [cfb8KRISCV64, cfb8RISCV64, g0, g1, g2, g3, g4, hm, ht] at hp ⊢
    rw [h.sch_eq, h.iv_eq, edata] at hp
    exact hp

end VG.Proof.AesCfb8.RISCV64
