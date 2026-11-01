module

import VerifiedGarbage.Proof.AesCcm.RISCV64.Header
import VerifiedGarbage.Proof.AesCcm.RISCV64.Ctrs
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.AesCcm.Rev64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.Bswap

/-!
# AES-CCM on RISCV64: `B₀` (`b0 y`) and the counter blocks (`ctrAt`)

Untrusted: everything here is checked by Lean. `flagsSeg` computes the flags
`4 (t − 2) + q − 1 + 64 [a > 0]` (which is A.2.1's for an even `t`,
`flags_wp`); `b0Seg y` writes `B₀` to `W + 32` from `Ctr₀` and zeroes the
MAC state at `W + y` (`b0Seg_wp`); `b0 y` then chains `B₀` into it
(`b0_wp`). `ctrAt` writes `Ctrᵢ` to `W + 64` from `Ctr₀` (`ctrAt_wp`). The
last 8 bytes of a block are read and written byte-reversed (`ldbrx`,
`stdbrx`), so ORing `[i]₆₄` into them is AArch64's `ctr_or`
(`Proof.AesCcm.ctr_or`): `rev (rev w ||| i) = w ||| rev i`.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)
open VG.Proof.Cmac (le8)

/-- `rev (rev w ||| v)`: `w` with `rev v` ORed into it. -/
theorem rev_or_rev (w v : BitVec 64) : byteRev64 (byteRev64 w ||| v) = w ||| byteRev64 v := by
  rw [Proof.AesCcm.byteRev64_or, Proof.Gcm.byteRev64_byteRev64]

/-- The first 8 and the last 8 bytes of `Ctr₀`. -/
theorem ctr0_lo {m : Mem} {W : Addr} {nonce : List Byte} (h7 : 7 ≤ nonce.length)
    (hc0 : bytesAt m (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    le8 (m.readW (W + BitVec.ofNat 64 48) 64) = BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
  have h8 : bytesAt m (W + BitVec.ofNat 64 48) 8 = (bytesAt m (W + BitVec.ofNat 64 48) 16).take 8 := by
    rw [Proof.Cmac.bytesAt_split, List.take_left' (length_bytesAt _ _ _)]
  rw [Proof.Cmac.le8_readW, h8, hc0, Proof.AesCcm.ctrBlock_take8 h7]

theorem ctr0_hi {m : Mem} {W : Addr} {nonce : List Byte}
    (hc0 : bytesAt m (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    le8 (m.readW (W + BitVec.ofNat 64 56) 64) = (Spec.Ccm.ctrBlock nonce 0).drop 8 := by
  rw [show W + BitVec.ofNat 64 56 = W + BitVec.ofNat 64 48 + BitVec.ofNat 64 8 from (Offset.add_add W 48 8).symm,
    Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, List.drop_left' (length_bytesAt _ _ _)]

theorem ctr0_take8 {m : Mem} {W : Addr} {nonce : List Byte}
    (hc0 : bytesAt m (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    le8 (m.readW (W + BitVec.ofNat 64 48) 64) = (Spec.Ccm.ctrBlock nonce 0).take 8 := by
  rw [Proof.Cmac.le8_readW, ← hc0, Proof.Cmac.bytesAt_split, List.take_left' (length_bytesAt _ _ _)]

theorem ofNat_lsl2 {a : Nat} (ha : a < 2 ^ 62) : BitVec.ofNat 64 a <<< 2 = BitVec.ofNat 64 (4 * a) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The counter blocks -/

/-- `ctrAt`: `Ctrᵢ` at `W + 64`, for `i` in `t3`. -/
theorem ctrAt_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {i : Nat}
    (hi : i < 256 ^ (15 - c.nl)) (ht3 : s.gpr .t3 = BitVec.ofNat 64 i) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', PK s s' → (∀ r ∈ [Reg.s5, .s6, .s7, .s8, .t3], s'.gpr r = s.gpr r) →
      Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem →
      bytesAt s'.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i → WP isa (.block is) s' Q) :
    WP isa (.block (ctrAt ++ is)) s Q := by
  have h7 := L.h7
  have h13 := L.h13
  unfold ctrAt
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ld (a := c.W + BitVec.ofNat 64 48) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 64) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_loadBE64 (a := c.W + BitVec.ofNat 64 56) (by decide) (by decide) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1]; rfl)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₃ s₄ u₃ u₄ => ?_
  refine wp_or fun s₅ u₅ => ?_
  have pk₅ : PK s s₅ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    (PK.ofUpd u₅))))
  refine wp_storeBE8 (a := c.W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8) (by decide) (by decide) (by decide)
    (by rw [pk₅.gpr .s1 (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [pk₅.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₆ s₇ u₆ u₇ => ?_
  have hk : ∀ r ∈ [Reg.s5, .s6, .s7, .s8, .t3], s₇.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]
  -- The two doublewords written.
  have hv : s₇.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 64) (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW
      (c.W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 i)) := by
    have hr : s₂.mem.readW (c.W + BitVec.ofNat 64 56) 64 = s.mem.readW (c.W + BitVec.ofNat 64 56) 64 := by
      rw [u₂.mem, u₁.gpr, u₁.mem]
      exact Mem.readW_writeW_sep ((L.w_w (a := 64) (n := 8) (d := 56) (k := 8) (.inr (by decide)) (by decide)
        (by decide)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
    rw [u₇.mem, u₆.mem, u₅.gpr, u₄.gpr, u₄.other .t3 (by decide), u₃.other .t3 (by decide),
      u₂.gpr, u₁.other .t3 (by decide), ht3, u₅.mem, u₄.mem, u₃.mem, hr, rev_or_rev, u₂.mem, u₁.gpr, u₁.mem]
  refine k s₇ (pk₅.trans ((PK.ofMupd u₆).trans (PK.ofUpd u₇))) hk
    (by rw [hv]; exact Proof.Cmac.frame_store2 _ _ _) ?_
  rw [hv, Proof.Cmac.bytesAt_store2, ctr0_take8 hc0,
    Proof.AesCcm.ctr_or (by omega) (by omega) (ctr0_hi hc0) (by rw [hnl]; exact hi),
    Proof.AesCcm.ctrBlock_take8 (by omega) 0, ← Proof.AesCcm.ctrBlock_take8 (by omega) i, List.take_append_drop]

/-! ## The flags -/

/-- The flags, from the tag length, the nonce length in its slot and the
length of the associated data in `s6`. -/
theorem flags_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (hs6 : s.gpr .s6 = BitVec.ofNat 64 c.al) :
    WP isa flagsSeg s fun s' => PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .t3 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64) ∧
      ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r := by
  have ht4 := L.t4
  have ht16 := L.t16
  have h13 := L.h13
  unfold flagsSeg
  refine WP.seq (wp_subi (imm := 2) (by decide) fun s₁ u₁ => wp_sll (by decide) fun s₂ u₂ => ?_)
  refine wp_ld (a := c.W + BitVec.ofNat 64 232) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₃ u₃ => ?_
  refine wp_li (imm := 14) (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => WP.block_nil ?_
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₆ : ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s₆.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]
  have t3₆ : s₆.gpr .t3 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl)) := by
    rw [u₆.gpr, u₅.gpr, u₅.other .t3 (by decide), u₄.gpr, u₄.other .t1 (by decide), u₄.other .t3 (by decide),
      u₃.gpr, u₃.other .t3 (by decide), u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, E.s2, S.nlen, ofNat_sub_ofNat' (by omega) (by omega),
      ofNat_lsl2 (by omega), ofNat_sub_ofNat' (by omega) (by decide), BitVec.ofNat_add_ofNat]
  refine WP.ite (decide (c.al = 0)) (eval_z (by rw [k₆ .s6 (by simp), hs6]) L.al_lt)
    (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₆, m₆, by rw [t3₆, h0]; rfl, k₆⟩
  · have h0 : c.al ≠ 0 := by simpa using hf
    refine wp_addi (by decide) fun s₇ u₇ => WP.block_nil ⟨pk₆.trans (PK.ofUpd u₇),
      by rw [u₇.mem, m₆], ?_, fun r hr => ?_⟩
    · rw [u₇.gpr, t3₆, BitVec.ofNat_add_ofNat, ite_eq_right h0]
    · have ht3 : r ≠ .t3 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [u₇.other _ ht3, k₆ r hr]

/-! ## `B₀` -/

theorem flags_byte {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) :
    ((BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64)).setWidth 8 : Byte) =
      Spec.Ccm.flags c.tl (15 - nonce.length) c.al := by
  rw [hnl, Proof.AesCcm.flags_val L.t4 L.t16 L.te L.h7 L.h13]

/-- `B₀` at `W + 32` from `Ctr₀` and the flags in `t3`, and the MAC state at
`W + y` zeroed. -/
theorem b0Seg_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (ht3 : s.gpr .t3 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64))
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (b0Seg y)) s fun s' => PK s s' ∧ (∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r) ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩, ⟨c.W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Spec.Ccm.zeros 16 ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
  have h7 := L.h7
  have h13 := L.h13
  have hy8 : y % 8 = 0 := by omega
  unfold b0Seg zero16
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_ld (a := c.W + BitVec.ofNat 64 48) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 56) (by decide) (by rw [u₁.other _ (by decide), E.s1]; rfl)
    (L.alW (by decide) (by decide)) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 32) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 40) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₄ u₄ => ?_
  refine wp_sb (a := c.W + BitVec.ofNat 64 32) (by decide)
    (by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₅ u₅ => ?_
  have pk₅ : PK s s₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofMupd u₄).trans
    (PK.ofMupd u₅))))
  refine wp_loadBE64 (a := c.W + BitVec.ofNat 64 40) (by decide) (by decide) (by decide) (by decide)
    (by rw [pk₅.gpr .s1 (by decide), E.s1]; rfl)
    (by rw [pk₅.rd, pk₅.wr]; exact E.perm.wR (by decide)) fun s₆ s₇ u₆ u₇ => wp_or fun s₈ u₈ => ?_
  have pk₈ : PK s s₈ := pk₅.trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))
  refine wp_storeBE8 (a := c.W + BitVec.ofNat 64 40) (by decide) (by decide) (by decide)
    (by rw [pk₈.gpr .s1 (by decide), E.s1]; rfl)
    (by rw [pk₈.wr]; exact E.perm.wW (by decide)) fun s₉ s₉' u₉ u₉' => ?_
  have pk₉ : PK s s₉' := pk₈.trans ((PK.ofMupd u₉).trans (PK.ofUpd u₉'))
  refine wp_li (by decide) fun s₁₀ u₁₀ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 y) (by omega)
    (by rw [u₁₀.other _ (by decide), pk₉.gpr .s1 (by decide), E.s1]) (L.alW hy8 (by omega))
    (by rw [u₁₀.wr, pk₉.wr]; exact E.perm.wW (by omega)) fun s₁₁ u₁₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 y + BitVec.ofNat 64 8) (by omega)
    (by rw [u₁₁.gpr, u₁₀.other _ (by decide), pk₉.gpr .s1 (by decide), E.s1, Offset.add_add])
    (by rw [Offset.add_add]; exact L.alW (by omega) (by omega))
    (by rw [u₁₁.wr, u₁₀.wr, pk₉.wr, Offset.add_add]; exact E.perm.wW (by omega)) fun s₁₂ u₁₂ => WP.block_nil ?_
  have pk₁₂ : PK s s₁₂ := pk₉.trans ((PK.ofUpd u₁₀).trans ((PK.ofMupd u₁₁).trans (PK.ofMupd u₁₂)))
  -- `B₀` as written.
  have s10₇ : s₇.gpr .s10 = BitVec.ofNat 64 c.n := by
    rw [(pk₅.trans ((PK.ofUpd u₆).trans (PK.ofUpd u₇))).gpr .s10 (by decide), E.s10]
  have hr : s₅.mem.readW (c.W + BitVec.ofNat 64 40) 64 = s.mem.readW (c.W + BitVec.ofNat 64 56) 64 := by
    rw [u₅.mem, Mem.readW_writeW_sep ((L.w_w (a := 40) (n := 8) (d := 32) (k := 1) (.inr (by decide))
      (by decide) (by decide)).sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide), u₄.mem,
      Mem.readW_writeW_self64, u₃.gpr, u₂.gpr, u₁.mem]
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = (((s.mem.writeW (c.W + BitVec.ofNat 64 32)
      (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64)).writeW (c.W + BitVec.ofNat 64 32)
      ((s.gpr .t3).setWidth 8 : Byte)).writeW (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 c.n)) := ⟨_, rfl⟩
  have hm₉ : s₉'.mem = mB := by
    rw [hmB, u₉'.mem, u₉.mem, u₈.gpr, u₇.gpr, s10₇, hr, rev_or_rev, u₈.mem, u₇.mem, u₆.mem, u₅.mem,
      u₄.gpr, u₄.mem, u₃.gpr, u₃.mem, u₂.other .t3 (by decide), u₂.gpr, u₂.mem, u₂.other .t1 (by decide), u₁.other .t3 (by decide),
      u₁.gpr, u₁.mem, Offset.add_add]
  have hm₁₂ : s₁₂.mem = (mB.writeW (c.W + BitVec.ofNat 64 y) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 y + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₁₂.mem, u₁₁.gpr, u₁₁.mem, u₁₀.gpr, u₁₀.mem, hm₉]; rfl
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega) (by decide)
  have fB : Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩] s.mem mB := by
    rw [hmB, Offset.add_add]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cB 32 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 32 1 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cB 40 8 (by decide) (by decide))
  have fY : Frame [⟨c.W + BitVec.ofNat 64 y, 16⟩] mB s₁₂.mem := by
    rw [hm₁₂]; exact Proof.Cmac.frame_store2 _ _ _
  have dYB : (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have hB : bytesAt mB (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
    have hlo := ctr0_lo (by omega) hc0
    have hhi := Proof.AesCcm.ctr_or (by omega) (by omega) (ctr0_hi hc0) (by rw [hnl]; exact L.hn)
    rw [hmB, Proof.AesCcm.bytesAt_writeW64_at _ _ _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW8_base _ _ _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW64_at _ _ _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide), hlo, hhi, ht3, flags_byte L hnl,
      Proof.AesCcm.ctrBlock_drop8 (by omega)]
    simp only [Spec.Ccm.b0, List.drop_one, List.cons_append, List.tail_cons, List.take_succ_cons,
      List.append_assoc]
    have ht7 : (nonce.take 7).length = 7 := by simp; omega
    have e1 : List.take 7 (List.take 7 nonce ++ List.drop 8 (bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16)) =
        nonce.take 7 := List.take_left' ht7
    rw [e1, List.take_left' ht7]
    have hd1 : List.drop (8 + 8) (BitVec.ofNat 8 (15 - nonce.length - 1) ::
        (List.take 7 nonce ++ List.drop 8 (bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16))) = [] :=
      List.drop_eq_nil_of_le (by simp [length_bytesAt]; omega)
    rw [hd1, List.append_nil]
    have hd2 : List.drop (8 + 8) (Spec.Ccm.flags c.tl (15 - nonce.length) c.al ::
        (List.take 7 nonce ++ le8 (s.mem.readW (c.W + BitVec.ofNat 64 56) 64))) = [] :=
      List.drop_eq_nil_of_le (by simp [Proof.Cmac.length_le8]; omega)
    rw [hd2, List.append_nil, ← List.append_assoc, List.take_append_drop]
  refine ⟨pk₁₂, fun r hr => ?_, ?_, by rw [hm₁₂]; exact zeros16_bytes _ _, ?_⟩
  · have h1 : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.other _ h1.1, u₉'.other _ h1.2.2, u₉.gpr, u₈.other _ h1.2.1, u₇.other _ h1.2.1,
      u₆.other _ h1.2.2, u₅.gpr, u₄.gpr, u₃.gpr, u₂.other _ h1.2.2, u₁.other _ h1.2.1]
  · exact (fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (fY.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  · rw [Proof.Cmac.bytesAt_frame fY (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dYB)
      (by decide), hB]

/-- `B₀` chained into the zeroed MAC state at `W + y`. -/
theorem b0_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (hs6 : s.gpr .s6 = BitVec.ofNat 64 c.al) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 y) s fun s' => Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Ccm.zeros 16) [Spec.Ccm.b0 c.tl nonce c.al c.n]) s' ∧
      ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r := by
  unfold b0
  refine WP.seq (WP.mono (flags_wp L E S hs6) fun s₁ ⟨pk₁, m₁, r9₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (b0Seg_wp L (E.of_pk pk₁) hnl (by rw [m₁]; exact hc0) r9₁ hy)
    fun s₂ ⟨pk₂, k₂, f₂, z₂, b₂⟩ => ?_)
  rw [m₁] at f₂
  have f₂' : Frame (macR c.W y) s.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  refine WP.mono (updBlock_wp L (E.of_pk (pk₁.trans pk₂)) hy) fun s₃ ⟨A, k₃⟩ =>
    ⟨⟨pk₁.trans (pk₂.trans A.pk), f₂'.trans A.frame, ?_⟩, fun r hr => by rw [k₃ r (by simp at hr ⊢; omega),
      k₂ r hr, k₁ r hr]⟩
  rw [A.out, z₂, b₂, ciph_keep L hy f₂']

end VG.Proof.AesCcm.RISCV64
