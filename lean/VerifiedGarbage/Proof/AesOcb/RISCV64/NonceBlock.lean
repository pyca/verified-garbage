module

-- separate module: its proofs (about 3 s) build in parallel with `Offset0`'s, which `Nonce` also imports

public import VerifiedGarbage.Proof.Ocb.Nonce
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Env
import VerifiedGarbage.Proof.AesOcb.RISCV64.PadTo
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-OCB on RISC-V: the block `Nonce` (`nonceBlock`)

Untrusted: everything here is checked by Lean. `nonceBlock` writes `Nonce`
(§4.2) with its last 6 bits cleared to `W + tmpO`, and `bottom` to
`W + botO` (`nonceBlock_ok`): zeros, the 1 before where the nonce goes, the
nonce copied to the end (`copyLoop`), `TAGLEN mod 128` ORed into the first
byte, and the last byte split into `bottom` and the rest. The 16 bytes are
followed as a list through the writes, and compared with `nb`
(`Proof.Ocb.nonceN_masked_byte`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/NonceBlock.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (nonceN nb nbase length_bytesAt bytesAt_writeBytes_at bytesAt_writeW8_at bytesAt_writeW8_base)
open VG.Proof.AesGcm.RISCV64 (copyLoop_ok in_left in_off and15)

theorem or_byte (b : Byte) (v : Nat) :
    (BitVec.setWidth 64 b ||| BitVec.ofNat 64 v).setWidth 8 = b ||| BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, show i < 64 by omega_arith, hi,
    decide_true, Bool.true_and]

theorem and_byte (b : Byte) (v : Nat) :
    (BitVec.setWidth 64 b &&& BitVec.ofNat 64 v).setWidth 8 = b &&& BitVec.ofNat 8 v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, show i < 64 by omega_arith, hi,
    decide_true, Bool.true_and]

theorem and63 (b : Byte) : BitVec.setWidth 64 b &&& BitVec.ofNat 64 63 = BitVec.ofNat 64 (b.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega_arith), show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem lsl4_ofNat (n : Nat) : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem one_byte : (BitVec.ofNat 64 1).setWidth 8 = (1 : Byte) := by decide

theorem getD_bytesAt_eq (m : Mem) (p : Addr) {k n : Nat} (hk : k < n) :
    m (p + BitVec.ofNat 64 k) = (bytesAt m p n).getD k 0 := by
  rw [List.getD_eq_getElem?_getD]; simp [bytesAt, hk]

/-- A byte written into a list of 16. -/
theorem getD_set16 (L : List Byte) (hL : L.length = 16) {o : Nat} (ho : o < 16) (b : Byte) {k : Nat}
    (hk : k < 16) : (L.take o ++ [b] ++ L.drop (o + 1)).getD k 0 = if k = o then b else L.getD k 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy k o with h | rfl | h
  · rw [List.getElem?_append_left (by simp; omega_arith), List.getElem?_append_left (by simp; omega_arith),
      List.getElem?_take_of_lt h]
    simp [show k ≠ o by omega_arith]
  · rw [List.getElem?_append_left (by simp; omega_arith), List.getElem?_append_right (by simp; omega_arith)]
    simp [show min k L.length = k by omega_arith]
  · rw [List.getElem?_append_right (by simp; omega_arith)]
    simp only [List.length_append, List.length_take, List.length_singleton, List.getElem?_drop,
      show ¬ k = o by omega_arith, ↓reduceIte]
    congr 2; omega_arith

/-- The registers `nonceBlock` writes. -/
abbrev nonceRegs : List Reg := [.t0, .t1, .t2, .a0, .a1, .a2, .a3]

/-- What `nonceBlock` leaves. -/
structure NoncePost (W : Addr) (t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s'.mem
  blk : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = nonceN t nonce &&& ~~~(63 : Block)
  bot : s'.mem.readW (W + BitVec.ofNat 64 botO) 64 = BitVec.ofNat 64 ((nonceN t nonce).extractLsb' 0 6).toNat
  gpr : ∀ r, r ∉ nonceRegs → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- After the first block of `nonceBlock`, from `s` (through `s₁`, after the zeros). -/
def NonceHead (W N : Addr) (nl : Nat) (s s₂ : State) : Prop :=
  ∃ s₁, BlkStep W tmpO 0 [.t0] s s₁ ∧ s₂.gpr .a1 = W + BitVec.ofNat 64 (128 - nl) ∧ s₂.gpr .a0 = N ∧
    s₂.gpr .a2 = BitVec.ofNat 64 nl ∧
    (∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₂.gpr r = s.gpr r) ∧
    s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 (127 - nl)) (1 : Byte) ∧ s₂.sp = s.sp ∧
    s₂.rd = s.rd ∧ s₂.wr = s.wr

/-- The first block of `nonceBlock`: zeros, the 1 before where the nonce
goes, and the arguments of the copy. -/
theorem nonceHead_ok {W N : Addr} {s : State} (hs0 : s.gpr .s0 = W) (hW : W.toNat % 8 = 0)
    (hw : Covers [⟨W, 2560⟩] s.wr) {nl : Nat}
    (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (hs4 : s.gpr .s4 = N) (hs5 : s.gpr .s5 = BitVec.ofNat 64 nl) :
    WP isa (.block (zero16 tmpO ++ ([.addi .a1 .s0 ((tmpO + 15 : Nat) : Int), .sub .a1 .a1 .s5, .li .t1 1,
      .store .b .t1 .a1 0, .addi .a1 .a1 1, Impl.AesGcm.RISCV64.mov .a0 .s4, Impl.AesGcm.RISCV64.mov .a2 .s5] :
      List Instr))) s (NonceHead W N nl s) := by
  have wW : ∀ {e k : Nat}, e + k ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 e) k := fun h => in_off hw h (by decide)
  refine WP.block_append (WP.mono (zero16_ok (s := s) (d := tmpO) hW (by decide) hs0 (wW (by decide))
    (wW (by decide))) fun s₁ B₁ => ?_)
  have e1 : W + BitVec.ofNat 64 (tmpO + 15) - BitVec.ofNat 64 nl = W + BitVec.ofNat 64 (127 - nl) :=
    Offset.add_ofNat_sub W (a := 127) (by omega_arith)
  have e2 : W + BitVec.ofNat 64 (127 - nl) + BitVec.ofNat 64 1 = W + BitVec.ofNat 64 (128 - nl) := by
    rw [Offset.add_add]; congr 2; omega_arith
  refine wp_addi (by decide) fun t₁ u₁ => wp_sub fun t₂ u₂ => wp_li (imm := 1) (by decide) fun t₃ u₃ =>
    wp_sb (a := W + BitVec.ofNat 64 (127 - nl)) (by decide) ?_ ?_ fun t₄ u₄ =>
    wp_addi (imm := 1) (by decide) fun t₅ u₅ => wp_mv fun t₆ u₆ => wp_mv fun t₇ u₇ => WP.block_nil ?_
  · rw [BitVec.add_zero, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), B₁.gpr _ (by decide),
      B₁.gpr _ (by decide), hs0, hs5, e1]
  · rw [u₃.wr, u₂.wr, u₁.wr, B₁.wr]; exact wW (by omega_arith)
  have a1₄ : t₄.gpr .a1 = W + BitVec.ofNat 64 (127 - nl) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), B₁.gpr _ (by decide),
      B₁.gpr _ (by decide), hs0, hs5, e1]
  refine ⟨s₁, B₁, ?_, ?_, ?_, fun r h0 h1' h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, a1₄, e2]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), B₁.gpr _ (by decide), hs4]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), B₁.gpr _ (by decide), hs5]
  · rw [u₇.other _ h5, u₆.other _ h3, u₅.other _ h4, u₄.gpr, u₃.other _ h1', u₂.other _ h4, u₁.other _ h4,
      B₁.gpr _ (by simp [h0])]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, one_byte, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, B₁.sp]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, B₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, B₁.wr]

theorem w127_ne_w112 (W : Addr) : (W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112) = False := by
  simp only [eq_iff_iff, iff_false]
  intro h
  have := congrArg (· - W) h
  simp only [Offset.add_sub_cancel_left] at this
  exact absurd this (by decide)

/-- The last block: `TAGLEN mod 128` into the first byte, `bottom`, and the
last byte's bits cleared. -/
theorem nonceTail_ok {W : Addr} {s : State} (hs0 : s.gpr .s0 = W) (hW : W.toNat % 8 = 0)
    (hw : Covers [⟨W, 2560⟩] s.wr) {t : Nat}
    (ht : t < 2 ^ 64) (hs8 : s.gpr .s8 = BitVec.ofNat 64 t) :
    WP isa (.block [.logicImm .and .t1 .s8 15, .shift .sll .d .t1 .t1 4, .load .b .t2 .s0 tmpO,
        .logic .or .t2 .t2 .t1, .store .b .t2 .s0 tmpO, .load .b .t2 .s0 (tmpO + 15),
        .logicImm .and .t1 .t2 63, .store .d .t1 .s0 botO, .logicImm .and .t2 .t2 0xc0,
        .store .b .t2 .s0 (tmpO + 15)]) s fun s₁ =>
      s₁.mem = ((s.mem.writeW (W + BitVec.ofNat 64 112)
          (s.mem (W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (t % 16)))).writeW (W + BitVec.ofNat 64 288)
          (BitVec.ofNat 64 ((s.mem (W + BitVec.ofNat 64 127)).toNat % 64))).writeW (W + BitVec.ofNat 64 127)
        (s.mem (W + BitVec.ofNat 64 127) &&& BitVec.ofNat 8 192) ∧
      (∀ r, r ≠ .t1 → r ≠ .t2 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 112) 1 := in_left (in_off hw (by decide) (by decide))
  have w₁ : InRegions s.wr (W + BitVec.ofNat 64 112) 1 := in_off hw (by decide) (by decide)
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 127) 1 := in_left (in_off hw (by decide) (by decide))
  have w₂ : InRegions s.wr (W + BitVec.ofNat 64 127) 1 := in_off hw (by decide) (by decide)
  have w₃ : InRegions s.wr (W + BitVec.ofNat 64 288) 8 := in_off hw (by decide) (by decide)
  refine wp_andi (by decide) fun t₂ u₂ => wp_sll (by decide) fun t₃ u₃ => ?_
  have g₃ : ∀ r, r ≠ .t1 → t₃.gpr r = s.gpr r := fun r b => by
    rw [u₃.other _ b, u₂.other _ b]
  have r3₃ : t₃.gpr .t1 = BitVec.ofNat 64 (16 * (t % 16)) := by
    rw [u₃.gpr, u₂.gpr, hs8, show BitVec.ofInt 64 15 = BitVec.ofNat 64 15 from rfl, and15, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt ht, lsl4_ofNat]
  have k₃ : t₃.mem = s.mem ∧ t₃.rd = s.rd ∧ t₃.wr = s.wr := ⟨by rw [u₃.mem, u₂.mem],
    by rw [u₃.rd, u₂.rd], by rw [u₃.wr, u₂.wr]⟩
  refine wp_lbu (a := W + BitVec.ofNat 64 112) (by decide) (by rw [g₃ _ (by decide), hs0]; rfl)
    (by rw [k₃.2.1, k₃.2.2]; exact r₁) fun t₄ u₄ => wp_or fun t₅ u₅ =>
    wp_sb (a := W + BitVec.ofNat 64 112) (by decide)
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), hs0]; rfl)
      (by rw [u₅.wr, u₄.wr, k₃.2.2]; exact w₁) fun t₆ u₆ => ?_
  have g₆ : ∀ r, r ≠ .t1 → r ≠ .t2 → t₆.gpr r = s.gpr r := fun r b c => by
    rw [u₆.gpr, u₅.other _ c, u₄.other _ c, g₃ r b]
  have m₆ : t₆.mem = s.mem.writeW (W + BitVec.ofNat 64 112)
      (s.mem (W + BitVec.ofNat 64 112) ||| BitVec.ofNat 8 (16 * (t % 16))) := by
    rw [u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.other _ (by decide), r3₃, u₄.mem, k₃.1, or_byte]
  refine wp_lbu (a := W + BitVec.ofNat 64 127) (by decide) (by rw [g₆ _ (by decide) (by decide), hs0]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, k₃.2.1, k₃.2.2]; exact r₂) fun t₇ u₇ =>
    wp_andi (by decide) fun t₉ u₉ =>
    wp_sd (a := W + BitVec.ofNat 64 288) (by decide)
      (by rw [u₉.other _ (by decide), u₇.other _ (by decide), g₆ _ (by decide) (by decide), hs0]; rfl)
      (Spill.al8 hW (by decide))
      (by rw [u₉.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, k₃.2.2]; exact w₃) fun t₁₀ u₁₀ =>
    wp_andi (by decide) fun t₁₂ u₁₂ =>
    wp_sb (a := W + BitVec.ofNat 64 127) (by decide)
      (by rw [u₁₂.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₇.other _ (by decide),
        g₆ _ (by decide) (by decide), hs0]; rfl)
      (by rw [u₁₂.wr, u₁₀.wr, u₉.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, k₃.2.2]; exact w₂)
      fun t₁₃ u₁₃ => WP.block_nil ?_
  have b127 : t₆.mem (W + BitVec.ofNat 64 127) = s.mem (W + BitVec.ofNat 64 127) := by
    rw [m₆, WriteBytes.writeW8_apply, ite_eq_right_of_eq_false _ _ (w127_ne_w112 W)]
  have r4₇ : t₇.gpr .t2 = BitVec.setWidth 64 (s.mem (W + BitVec.ofNat 64 127)) := by rw [u₇.gpr, b127]
  refine ⟨?_, fun r b c => ?_, ?_, ?_, ?_⟩
  · rw [u₁₃.mem, u₁₂.gpr, u₁₀.gpr, u₉.other _ (by decide), r4₇,
      show BitVec.ofInt 64 0xc0 = BitVec.ofNat 64 192 from rfl, and_byte, u₁₂.mem, u₁₀.mem, u₉.gpr,
      r4₇, show BitVec.ofInt 64 63 = BitVec.ofNat 64 63 from rfl, and63, u₉.mem, u₇.mem, m₆]
  · rw [u₁₃.gpr, u₁₂.other _ c, u₁₀.gpr, u₉.other _ b, u₇.other _ c, g₆ r b c]
  · rw [u₁₃.sp, u₁₂.sp, u₁₀.sp, u₉.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp]
  · rw [u₁₃.rd, u₁₂.rd, u₁₀.rd, u₉.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, k₃.2.1]
  · rw [u₁₃.wr, u₁₂.wr, u₁₀.wr, u₉.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, k₃.2.2]

theorem nonceBlock_ok {K W : Addr} (L : Lay K W) {s : State} (hs0 : s.gpr .s0 = W) (hw : Covers [⟨W, 2560⟩] s.wr)
    {N : Addr} {nl t : Nat} (hs4 : s.gpr .s4 = N) (hs5 : s.gpr .s5 = BitVec.ofNat 64 nl)
    (hs8 : s.gpr .s8 = BitVec.ofNat 64 t) (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64) (hB : Buf W s N nl) :
    WP isa nonceBlock s (NoncePost W t (bytesAt s.mem N nl) s) := by
  unfold nonceBlock
  refine WP.seq (WP.mono (nonceHead_ok hs0 L.wal hw h1 h15 hs4 hs5) fun s₂ H => ?_)
  obtain ⟨s₁, B₁, x11₂, x12₂, x13₂, g₂, m₂, sp₂, rd₂, wr₂⟩ := H
  have f₁ := B₁.frame
  have z₁ := B₁.val
  have hS₂ : Covers [⟨N, nl⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂]; exact hB.rd
  have hD₂ : Covers [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.wr := by
    rw [wr₂]; exact Proof.AesGcm.RISCV64.covers_off hw (by omega_arith) (by decide)
  have hSD : (⟨N, nl⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 (128 - nl), nl⟩ := hB.w.sub_right (Lay.wSub (by omega_arith))
  have f₂ : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    rw [show W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) by
      rw [Offset.add_add]; congr 2; omega_arith]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have eN : bytesAt s₂.mem N nl = bytesAt s.mem N nl := by
    rw [Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega_arith),
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hB.w.sub_right (Lay.wSub (by decide))) (by omega_arith)]
  refine WP.seq (WP.mono (copyLoop_ok s₂ ⟨x12₂, x11₂, x13₂, h1, by omega_arith, hS₂, hD₂, hSD⟩) fun s₃ h₃ => ?_)
  obtain ⟨m₃, o₃⟩ := h₃
  obtain ⟨rd₃, wr₃, sp₃⟩ := o₃.keeps
  rw [eN] at m₃
  have h31₃ : s₃.gpr .s0 = W := by
    rw [o₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hs0]
  have h19₃ : s₃.gpr .s8 = BitVec.ofNat 64 t := by
    rw [o₃.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hs8]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂]
  have fr₃ : Frame [⟨W + BitVec.ofNat 64 (128 - nl), nl⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact contains_pre _ (by omega_arith))
  refine WP.mono (nonceTail_ok h31₃ L.wal (by rw [wr₃']; exact hw) ht h19₃) fun s₄ ⟨m₄, g₄, sp₄, rd₄, wr₄⟩ => ?_
  -- the bytes at `W + tmpO`, step by step
  have hlen : (bytesAt s.mem N nl).length = nl := length_bytesAt _ _ _
  have L₁ : bytesAt s₁.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros 16 := bytesAt_of_zero z₁
  have e128 : W + BitVec.ofNat 64 (128 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (16 - nl) := by
    rw [Offset.add_add, show 112 + (16 - nl) = 128 - nl by omega_arith]
  have e127 : W + BitVec.ofNat 64 (127 - nl) = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 (15 - nl) := by
    rw [Offset.add_add, show 112 + (15 - nl) = 127 - nl by omega_arith]
  have L₂ : bytesAt s₂.mem (W + BitVec.ofNat 64 112) 16 =
      Spec.Ocb.zeros (15 - nl) ++ [1] ++ Spec.Ocb.zeros (nl) := by
    rw [m₂, e127, bytesAt_writeW8_at _ _ _ (by omega_arith) (by decide), L₁]
    simp only [Spec.Ocb.zeros, List.take_replicate, List.drop_replicate, show min (15 - nl) 16 = 15 - nl by omega_arith,
      show 16 - (15 - nl + 1) = nl by omega_arith]
  have L₃ : bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16 = Spec.Ocb.zeros (15 - nl) ++ [1] ++ bytesAt s.mem N nl := by
    rw [m₃, e128, bytesAt_writeBytes_at _ _ _ (by omega_arith) (by decide), L₂, hlen]
    rw [show 16 - nl + nl = 16 by omega_arith]
    simp only [Spec.Ocb.zeros, List.take_append, List.take_replicate, List.drop_append, List.drop_replicate,
      List.length_replicate, List.length_singleton, List.append_assoc]
    simp only [show min (16 - nl) (15 - nl) = 15 - nl by omega_arith, show 16 - nl - (15 - nl) = 1 by omega_arith,
      show 16 - (15 - nl) = nl + 1 by omega_arith]
    simp only [show 1 - 1 = 0 from rfl, Nat.zero_min, List.replicate_zero, List.nil_append,
      show 15 - nl - 16 = 0 by omega_arith, List.take_one, List.head?_cons, Option.toList_some,
      List.drop_eq_nil_of_le (show [(1 : Byte)].length ≤ nl + 1 by simp), show nl - (nl + 1 - 1) = 0 by omega_arith,
      List.append_nil]
  have L₃d : ∀ k < 16, (bytesAt s₃.mem (W + BitVec.ofNat 64 112) 16).getD k 0 = nbase (bytesAt s.mem N nl) k :=
    fun k hk => by
      have := Proof.Ocb.nbase_list (bytesAt s.mem N nl) (by rw [hlen]; omega_arith) (by rw [hlen]; omega_arith) hk
      rw [hlen] at this; rw [L₃]; exact this
  have b0 : s₃.mem (W + BitVec.ofNat 64 112) = nbase (bytesAt s.mem N nl) 0 := by
    have := getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 0) (n := 16) (by decide)
    rw [BitVec.add_zero] at this
    rw [this, L₃d 0 (by decide)]
  have e127' : W + BitVec.ofNat 64 127 = W + BitVec.ofNat 64 112 + BitVec.ofNat 64 15 :=
    (Offset.add_add W 112 15).symm
  have b15 : s₃.mem (W + BitVec.ofNat 64 127) = nb t (bytesAt s.mem N nl) 15 := by
    rw [e127', getD_bytesAt_eq s₃.mem (W + BitVec.ofNat 64 112) (k := 15) (n := 16) (by decide),
      L₃d 15 (by decide)]
    rfl
  have fr288 : ∀ (M : Mem) (v : BitVec 64), Frame [⟨W + BitVec.ofNat 64 288, 8⟩] M
      (M.writeW (W + BitVec.ofNat 64 288) v) :=
    fun M v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have L₄d : ∀ k < 16, (bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16).getD k 0 =
      if k = 15 then nb t (bytesAt s.mem N nl) 15 &&& 0xc0 else nb t (bytesAt s.mem N nl) k := by
    intro k hk
    rw [m₄, b15, e127', bytesAt_writeW8_at _ _ (o := 15) (n := 16) _ (by decide) (by decide),
      Proof.Cmac.bytesAt_frame (fr288 _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (a := 112) (n := 16) (d := 288) (k := 8) (.inl (by decide)) (by decide) (by decide))
        (by decide),
      getD_set16 _ (length_bytesAt _ _ _) (by decide) _ hk]
    split
    · rfl
    · rename_i hk15
      rw [bytesAt_writeW8_base _ _ _ (by decide) (by decide), b0]
      unfold nb
      rcases k with _ | k
      · rfl
      · simp only [List.getD_cons_succ, show k + 1 ≠ 0 by omega_arith, ↓reduceIte]
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
          show 1 + k = k + 1 by omega_arith]
        exact L₃d (k + 1) hk
  have hlen16 := length_bytesAt s₄.mem (W + BitVec.ofNat 64 112) 16
  have f₃ : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 botO, 8⟩] s.mem s₃.mem :=
    ((f₁.trans f₂).mono (fun r hr => by simp at hr; simp [hr])).trans ((fr₃.sub fun r hr => ⟨_, List.mem_cons_self .., by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e128]; exact Offset.sub_base _ (by omega_arith)⟩))
  refine ⟨?_, ?_, ?_, fun r hr => ?_, by rw [sp₄, sp₃, sp₂], by rw [rd₄, rd₃, rd₂],
    by rw [wr₄, wr₃']⟩
  · rw [m₄]
    refine ((f₃.writeW (List.mem_cons_self ..) _ ?_).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Region.contains_self _ _)).writeW (List.mem_cons_self ..) _ ?_
    · show (⟨W + BitVec.ofNat 64 112, 16⟩ : Region).Contains (W + BitVec.ofNat 64 112) 1
      exact contains_pre _ (by decide)
    · rw [e127']; exact Offset.contains_base _ (by decide) (by decide)
  · show blockAtMem s₄.mem (W + BitVec.ofNat 64 112) = _
    rw [blockAtMem]
    apply Proof.Ocb.toBytes_inj
    rw [Proof.Ocb.toBytes_ofBytes hlen16]
    refine Proof.Cmac.ext16 hlen16 (Proof.Ocb.toBytes_length _) fun k hk => ?_
    rw [L₄d k hk, Proof.Ocb.nonceN_masked_byte _ _ (by omega_arith) (by omega_arith) hk]
  · show s₄.mem.readW (W + BitVec.ofNat 64 288) 64 = _
    rw [m₄, Mem.readW_writeW_sep (Offset.sep W (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self64, b15, Proof.Ocb.nonceN_bottom _ _ (by omega_arith) (by omega_arith)]
  · simp only [nonceRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄ r hr.2.1 hr.2.2.1, o₃.other r hr.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2,
      g₂ r hr.1 hr.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1]

end VG.Proof.AesOcb.RISCV64
