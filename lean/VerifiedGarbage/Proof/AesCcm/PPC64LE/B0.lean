module

import VerifiedGarbage.Proof.AesCcm.PPC64LE.Header
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.AesCcm.Rev64
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Framework.Bswap

/-!
# AES-CCM on PPC64LE: `B₀` (`b0 y`) and the counter blocks (`ctrAt`)

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

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_subi wp_li wp_or wp_lsl wp_add wp_sub wp_ld wp_std wp_stb)
open VG.Proof.Gather.PPC64LE (eval_zero)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)
open VG.Proof.Cmac (le8)

/-- `rev (rev w ||| v)`: `w` with `rev v` ORed into it. -/
theorem rev_or_rev (w v : BitVec 64) : rev64 (rev64 w ||| v) = w ||| byteRev64 v := by
  rw [rev64_eq, Proof.AesCcm.byteRev64_or, rev64_eq, Proof.Gcm.byteRev64_byteRev64]

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
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega_arith),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-! ## The counter blocks -/

/-- `ctrAt`: `Ctrᵢ` at `W + 64`, for `i` in `r9`. -/
theorem ctrAt_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {i : Nat}
    (hi : i < 256 ^ (15 - c.nl)) (h9 : s.gpr .r9 = BitVec.ofNat 64 i) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', PK s s' → (∀ r ∈ [Reg.r18, .r19, .r20, .r21, .r9], s'.gpr r = s.gpr r) →
      Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] s.mem s'.mem →
      bytesAt s'.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce i → WP isa (.block is) s' Q) :
    WP isa (.block (ctrAt ++ is)) s Q := by
  have h7 := L.h7
  have h13 := L.h13
  unfold ctrAt
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 48) (by decide) (by decide) (by rw [E.r14]; rfl)
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 64) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14]; rfl) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_li (by decide) fun s₃ u₃ => ?_
  refine wp_ldbrx (ea := c.W + BitVec.ofNat 64 56) (by decide)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r14, u₃.gpr]; rfl)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₄ u₄ => ?_
  refine wp_or fun s₅ u₅ => wp_li (by decide) fun s₆ u₆ => ?_
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  refine wp_stdbrx (ea := c.W + BitVec.ofNat 64 72) (by decide)
    (by rw [pk₆.gpr .r14 (by decide), E.r14, u₆.gpr]; rfl)
    (by rw [pk₆.wr]; exact E.perm.wW (by decide)) fun s₇ u₇ => ?_
  have hk : ∀ r ∈ [Reg.r18, .r19, .r20, .r21, .r9], s₇.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide)]
  -- The two doublewords written.
  have hv : s₇.mem = (s.mem.writeW (c.W + BitVec.ofNat 64 64) (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW
      (c.W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 i)) := by
    have hr : s₂.mem.readW (c.W + BitVec.ofNat 64 56) 64 = s.mem.readW (c.W + BitVec.ofNat 64 56) 64 := by
      rw [u₂.mem, u₁.gpr, u₁.mem]
      exact Mem.readW_writeW_sep ((L.w_w (a := 64) (n := 8) (d := 56) (k := 8) (.inr (by decide)) (by decide)
        (by decide)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)
    rw [u₇.mem, u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), h9, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hr, rev_or_rev, u₂.mem, u₁.gpr, u₁.mem,
      Offset.add_add]
  refine k s₇ (pk₆.trans (PK.ofMupd u₇)) hk (by rw [hv]; exact Proof.Cmac.frame_store2 _ _ _) ?_
  rw [hv, Proof.Cmac.bytesAt_store2, ctr0_take8 hc0,
    Proof.AesCcm.ctr_or (by omega_arith) (by omega_arith) (ctr0_hi hc0) (by rw [hnl]; exact hi),
    Proof.AesCcm.ctrBlock_take8 (by omega_arith) 0, ← Proof.AesCcm.ctrBlock_take8 (by omega_arith) i, List.take_append_drop]

/-! ## The flags -/

/-- The flags, from the tag length, the nonce length in its slot and the
length of the associated data in `r19`. -/
theorem flags_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 c.al) :
    WP isa flagsSeg s fun s' => PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .r9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64) ∧
      ∀ r ∈ [Reg.r18, .r19, .r20, .r21], s'.gpr r = s.gpr r := by
  have ht4 := L.t4
  have ht16 := L.t16
  have h13 := L.h13
  unfold flagsSeg
  refine WP.seq (wp_subi (by decide) (by decide) fun s₁ u₁ => wp_lsl (by decide) fun s₂ u₂ => ?_)
  refine wp_ld (a := c.W + BitVec.ofNat 64 232) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₃ u₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => WP.block_nil ?_
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₆ : ∀ r ∈ [Reg.r18, .r19, .r20, .r21], s₆.gpr r = s.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide)]
  have r9₆ : s₆.gpr .r9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl)) := by
    rw [u₆.gpr, u₅.gpr, u₅.other .r9 (by decide), u₄.gpr, u₄.other .r10 (by decide), u₄.other .r9 (by decide),
      u₃.gpr, u₃.other .r9 (by decide), u₂.gpr, u₁.gpr, u₂.mem, u₁.mem, E.r15, S.nlen, ofNat_sub_ofNat' (by omega_arith) (by omega_arith),
      ofNat_lsl2 (by omega_arith), ofNat_sub_ofNat' (by omega_arith) (by decide), BitVec.ofNat_add_ofNat]
  refine WP.ite (decide (c.al = 0)) (eval_zero (by rw [k₆ .r19 (by simp), h19]) L.al_lt)
    (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₆, m₆, by rw [r9₆, h0]; rfl, k₆⟩
  · have h0 : c.al ≠ 0 := by simpa using hf
    refine wp_addi (by decide) (by decide) fun s₇ u₇ => WP.block_nil ⟨pk₆.trans (PK.ofUpd u₇),
      by rw [u₇.mem, m₆], ?_, fun r hr => ?_⟩
    · rw [u₇.gpr, r9₆, BitVec.ofNat_add_ofNat, ite_eq_right h0]
    · have hr9 : r ≠ .r9 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [u₇.other _ hr9, k₆ r hr]

/-! ## `B₀` -/

theorem flags_byte {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) :
    ((BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64)).setWidth 8 : Byte) =
      Spec.Ccm.flags c.tl (15 - nonce.length) c.al := by
  rw [hnl, Proof.AesCcm.flags_val L.t4 L.t16 L.te L.h7 L.h13]

/-- `B₀` at `W + 32` from `Ctr₀` and the flags in `r9`, and the MAC state at
`W + y` zeroed. -/
theorem b0Seg_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (4 * (c.tl - 2) + (14 - c.nl) + if c.al = 0 then 0 else 64))
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (b0Seg y)) s fun s' => PK s s' ∧ (∀ r ∈ [Reg.r18, .r19, .r20, .r21], s'.gpr r = s.gpr r) ∧
      Frame [⟨c.W + BitVec.ofNat 64 32, 16⟩, ⟨c.W + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 = Spec.Ccm.zeros 16 ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 c.tl nonce c.al c.n := by
  have h7 := L.h7
  have h13 := L.h13
  unfold b0Seg zero16
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 48) (by decide) (by decide) (by rw [E.r14]; rfl)
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 56) (by decide) (by decide) (by rw [u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 32) (by decide) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 40) (by decide) (by decide)
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₄ u₄ => ?_
  refine wp_stb (a := c.W + BitVec.ofNat 64 32) (by decide) (by decide)
    (by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₅ u₅ => ?_
  refine wp_li (by decide) fun s₆ u₆ => ?_
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofMupd u₅).trans (PK.ofUpd u₆)))))
  refine wp_ldbrx (ea := c.W + BitVec.ofNat 64 40) (by decide)
    (by rw [pk₆.gpr .r14 (by decide), E.r14, u₆.gpr]; rfl)
    (by rw [pk₆.rd, pk₆.wr]; exact E.perm.wR (by decide)) fun s₇ u₇ => wp_or fun s₈ u₈ => ?_
  have pk₈ : PK s s₈ := pk₆.trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈))
  refine wp_stdbrx (ea := c.W + BitVec.ofNat 64 40) (by decide)
    (by rw [pk₈.gpr .r14 (by decide), E.r14, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]; rfl)
    (by rw [pk₈.wr]; exact E.perm.wW (by decide)) fun s₉ u₉ => ?_
  have pk₉ : PK s s₉ := pk₈.trans (PK.ofMupd u₉)
  refine wp_li (by decide) fun s₁₀ u₁₀ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 y) (by decide) ⟨by omega_arith, by omega_arith⟩
    (by rw [u₁₀.other _ (by decide), pk₉.gpr .r14 (by decide), E.r14])
    (by rw [u₁₀.wr, pk₉.wr]; exact E.perm.wW (by omega_arith)) fun s₁₁ u₁₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 y + BitVec.ofNat 64 8) (by decide) ⟨by omega_arith, by omega_arith⟩
    (by rw [u₁₁.gpr, u₁₀.other _ (by decide), pk₉.gpr .r14 (by decide), E.r14, Offset.add_add])
    (by rw [u₁₁.wr, u₁₀.wr, pk₉.wr, Offset.add_add]; exact E.perm.wW (by omega_arith)) fun s₁₂ u₁₂ => WP.block_nil ?_
  have pk₁₂ : PK s s₁₂ := pk₉.trans ((PK.ofUpd u₁₀).trans ((PK.ofMupd u₁₁).trans (PK.ofMupd u₁₂)))
  -- `B₀` as written.
  have r23₈ : s₇.gpr .r23 = BitVec.ofNat 64 c.n := by
    rw [(pk₆.trans (PK.ofUpd u₇)).gpr .r23 (by decide), E.r23]
  have hr : s₆.mem.readW (c.W + BitVec.ofNat 64 40) 64 = s.mem.readW (c.W + BitVec.ofNat 64 56) 64 := by
    rw [u₆.mem, u₅.mem, Mem.readW_writeW_sep ((L.w_w (a := 40) (n := 8) (d := 32) (k := 1) (.inr (by decide))
      (by decide) (by decide)).sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide), u₄.mem,
      Mem.readW_writeW_self64, u₃.gpr, u₂.gpr, u₁.mem]
  obtain ⟨mB, hmB⟩ : ∃ mB, mB = (((s.mem.writeW (c.W + BitVec.ofNat 64 32)
      (s.mem.readW (c.W + BitVec.ofNat 64 48) 64)).writeW (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64)).writeW (c.W + BitVec.ofNat 64 32)
      ((s.gpr .r9).setWidth 8 : Byte)).writeW (c.W + BitVec.ofNat 64 32 + BitVec.ofNat 64 8)
      (s.mem.readW (c.W + BitVec.ofNat 64 56) 64 ||| byteRev64 (BitVec.ofNat 64 c.n)) := ⟨_, rfl⟩
  have hm₉ : s₉.mem = mB := by
    rw [hmB, u₉.mem, u₈.gpr, u₇.gpr, r23₈, hr, rev_or_rev, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.gpr, u₄.mem,
      u₃.gpr, u₃.mem, u₂.other .r9 (by decide), u₂.gpr, u₂.other .r10 (by decide), u₂.mem, u₁.other .r9 (by decide),
      u₁.gpr, u₁.mem, Offset.add_add]
  have hm₁₂ : s₁₂.mem = (mB.writeW (c.W + BitVec.ofNat 64 y) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 y + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₁₂.mem, u₁₁.gpr, u₁₁.mem, u₁₀.gpr, u₁₀.mem, hm₉]; rfl
  have cB : ∀ d k, 32 ≤ d → d + k ≤ 48 →
      (⟨c.W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) k :=
    fun d k h₁ h₂ => Offset.contains c.W h₁ (by omega_arith) (by decide)
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
    have hlo := ctr0_lo (by omega_arith) hc0
    have hhi := Proof.AesCcm.ctr_or (by omega_arith) (by omega_arith) (ctr0_hi hc0) (by rw [hnl]; exact L.hn)
    rw [hmB, Proof.AesCcm.bytesAt_writeW64_at _ _ _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW8_base _ _ _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW64_at _ _ _ (by decide) (by decide),
      Proof.AesCcm.bytesAt_writeW64_base _ _ _ (by decide) (by decide), hlo, hhi, h9, flags_byte L hnl,
      Proof.AesCcm.ctrBlock_drop8 (by omega_arith)]
    simp only [Spec.Ccm.b0, List.drop_one, List.cons_append, List.tail_cons, List.take_succ_cons,
      List.append_assoc]
    have ht7 : (nonce.take 7).length = 7 := by simp; omega_arith
    have e1 : List.take 7 (List.take 7 nonce ++ List.drop 8 (bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16)) =
        nonce.take 7 := List.take_left' ht7
    rw [e1, List.take_left' ht7]
    have hd1 : List.drop (8 + 8) (BitVec.ofNat 8 (15 - nonce.length - 1) ::
        (List.take 7 nonce ++ List.drop 8 (bytesAt s.mem (c.W + BitVec.ofNat 64 32) 16))) = [] :=
      List.drop_eq_nil_of_le (by simp [length_bytesAt]; omega_arith)
    rw [hd1, List.append_nil]
    have hd2 : List.drop (8 + 8) (Spec.Ccm.flags c.tl (15 - nonce.length) c.al ::
        (List.take 7 nonce ++ le8 (s.mem.readW (c.W + BitVec.ofNat 64 56) 64))) = [] :=
      List.drop_eq_nil_of_le (by simp [Proof.Cmac.length_le8]; omega_arith)
    rw [hd2, List.append_nil, ← List.append_assoc, List.take_append_drop]
  refine ⟨pk₁₂, fun r hr => ?_, ?_, by rw [hm₁₂]; exact zeros16_bytes _ _, ?_⟩
  · have h1 : r ≠ .r12 ∧ r ≠ .r11 ∧ r ≠ .r10 ∧ r ≠ .r0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.other _ h1.2.2.2, u₉.gpr, u₈.other _ h1.1, u₇.other _ h1.1, u₆.other _ h1.2.1,
      u₅.gpr, u₄.gpr, u₃.gpr, u₂.other _ h1.2.1, u₁.other _ h1.2.2.1]
  · exact (fB.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
      (fY.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)
  · rw [Proof.Cmac.bytesAt_frame fY (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dYB)
      (by decide), hB]

/-- `B₀` chained into the zeroed MAC state at `W + y`. -/
theorem b0_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 c.al) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (b0 y) s fun s' => Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Ccm.zeros 16) [Spec.Ccm.b0 c.tl nonce c.al c.n]) s' ∧
      ∀ r ∈ [Reg.r18, .r19, .r20, .r21], s'.gpr r = s.gpr r := by
  unfold b0
  refine WP.seq (WP.mono (flags_wp L E S h19) fun s₁ ⟨pk₁, m₁, r9₁, k₁⟩ => ?_)
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

end VG.Proof.AesCcm.PPC64LE
