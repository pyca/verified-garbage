module

import VerifiedGarbage.Proof.AesCcm.PPC64LE.Ctrs
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Compare
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Aes.Circuit
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Proof.Aes.SboxSpec
public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Env
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Framework.PPC64LE.StraightK
public import VerifiedGarbage.Spec.TripleDes
public meta import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-CCM on PPC64LE: checking the received tag (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` copies the first
`tag_len` bytes of the received tag (at `r18`) and of the computed one (at
`W + 96`) over zeros at `W + 272` and `W + 256`, and leaves 1 in `r21` iff
the two padded blocks are equal, without a branch (`cmp_wp`,
`Proof.AesCcm.words_eq`, `Proof.AesCcm.pad_eq`). `mask` ANDs every byte of
the data with `0 − r21` (`mask_wp`): the data if the tags are equal, zeros
if not.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_subi wp_li wp_sub wp_ld wp_std wp_xor wp_or wp_lsr wp_and
  wp_lbz wp_stb)
open VG.Proof.Gather.PPC64LE (copyBytes_wp eval_zero eval_nonzero)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-- `1 − ((d ||| −d) >>> 63)`: 1 if `d` is 0, else 0. -/
theorem zero_test (d : BitVec 64) :
    BitVec.ofNat 64 1 - ((d ||| (BitVec.ofNat 64 0 - d)) >>> 63) = BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  have h := Proof.AesCcm.neg_or_msb d
  rw [show BitVec.ofNat 64 0 = (0 : BitVec 64) from rfl, h]
  by_cases hd : d = 0 <;> simp only [hd, ite_true, ite_false] <;> decide

/-- The comparison's last block: `r21` is 1 iff the 16 bytes at `W + 256` and
at `W + 272` are equal. -/
theorem cmpTail_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [.load .d .r5 .r14 vO, .load .d .r6 .r14 rO, .logic .xor .r5 .r5 .r6,
      .load .d .r6 .r14 (vO + 8), .load .d .r7 .r14 (rO + 8), .logic .xor .r6 .r6 .r7,
      .logic .or .r5 .r5 .r6, .li .r6 0, .sub .r6 .r6 .r5, .logic .or .r5 .r5 .r6, .lsr .d .r5 .r5 63,
      .li .r21 1, .sub .r21 .r21 .r5]) s fun s' => PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .r21 = BitVec.ofNat 64 (if bytesAt s.mem (c.W + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (c.W + BitVec.ofNat 64 272) 16 then 1 else 0) := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 256) (by decide) (by decide) (by rw [E.r14]; rfl)
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 272) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14]; rfl) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 264) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 280) (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      E.r14]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₅ u₅ => ?_
  refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ =>
    wp_or fun s₁₀ u₁₀ => wp_lsr (by decide) fun s₁₁ u₁₁ => wp_li (by decide) fun s₁₂ u₁₂ =>
    wp_sub fun s₁₃ u₁₃ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans
    (PK.ofUpd u₁₃)))))))))))),
    by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem], ?_⟩
  have hd : s₇.gpr .r5 =
      (s.mem.readW (c.W + BitVec.ofNat 64 256) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 272) 64) |||
      (s.mem.readW (c.W + BitVec.ofNat 64 264) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 280) 64) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .r5 (by decide), u₅.gpr, u₅.other .r6 (by decide), u₄.gpr,
      u₅.other .r5 (by decide), u₄.other .r5 (by decide), u₃.gpr, u₂.gpr, u₂.other .r5 (by decide), u₁.gpr,
      u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rw [u₁₃.gpr, u₁₂.gpr, u₁₂.other .r5 (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other .r5 (by decide),
    u₈.gpr, u₈.other .r5 (by decide), hd, zero_test]
  have hw := Proof.AesCcm.words_eq s.mem (c.W + BitVec.ofNat 64 256) (c.W + BitVec.ofNat 64 272)
  rw [Offset.add_add, Offset.add_add] at hw
  congr 2
  exact propext hw

/-- `cmp`: 1 in `r21` iff the `tag_len` bytes at `T` (`r18`) are the first
`tag_len` of the computed tag at `W + 96`. -/
theorem cmp_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (h18 : s.gpr .r18 = c.T) :
    WP isa cmp s fun s' => PK s s' ∧ Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem ∧
      s'.gpr .r21 = BitVec.ofNat 64
        (if bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem c.T c.tl then 1 else 0) := by
  have ht4 := L.t4
  have ht16 := L.t16
  unfold cmp zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_std (a := c.W + BitVec.ofNat 64 256) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14]; rfl) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add]; rfl)
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 272) (by decide) (by decide)
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₅ u₅ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add]; rfl)
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₆ u₆ => ?_
  refine wp_mv fun s₇ u₇ => wp_addi (by decide) (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  have pk₉ : PK s s₉ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofMupd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))))))))
  have E₉ := E.of_pk pk₉
  have m₉ : s₉.mem = (((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272)
      (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr]
    rfl
  have g₉ : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r9 → r ≠ .r4 → s₉.gpr r = s.gpr r := fun r h0 h3 h9 h4 => by
    rw [u₉.other _ h4, u₈.other _ h9, u₇.other _ h3, u₆.gpr, u₅.gpr, u₄.other _ h0, u₃.gpr, u₂.gpr, u₁.other _ h0]
  have f256 : Frame [⟨c.W + BitVec.ofNat 64 256, 16⟩] s.mem
      ((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)) := Proof.Cmac.frame_store2 _ _ _
  have f272 : Frame [⟨c.W + BitVec.ofNat 64 272, 16⟩]
      ((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)) s₉.mem := by
    rw [m₉]; exact Proof.Cmac.frame_store2 _ _ _
  have z272 : bytesAt s₉.mem (c.W + BitVec.ofNat 64 272) 16 = Spec.Ccm.zeros 16 := by
    rw [m₉]; exact zeros16_bytes _ _
  have z256 : bytesAt s₉.mem (c.W + BitVec.ofNat 64 256) 16 = Spec.Ccm.zeros 16 := by
    rw [Proof.Cmac.bytesAt_frame f272 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]
    exact zeros16_bytes _ _
  have hdT : (⟨c.T, c.tl⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 272, c.tl⟩ :=
    L.t_w.sub_right (Lay.wSub (by omega_arith))
  have hb₁ : VG.Proof.Gather.PPC64LE.BytesPre s₉ c.T (c.W + BitVec.ofNat 64 272) c.tl :=
    { r3 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), h18]
      r9 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.r14]; rfl
      r4 := by rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.r15]
      pos := by omega_arith
      lt := by omega_arith
      rd := by rw [pk₉.rd, pk₉.wr]; exact E.perm.t
      wr := E₉.perm.wC (by omega_arith)
      disj := hdT }
  refine WP.seq (WP.mono (copyBytes_wp s₉ hb₁) fun s₁₀ ⟨hm₁₀, _, k₁₀⟩ => ?_)
  refine WP.seq (wp_addi (by decide) (by decide) fun s₁₁ u₁₁ => wp_addi (by decide) (by decide) fun s₁₂ u₁₂ =>
    wp_mv fun s₁₃ u₁₃ => WP.block_nil ?_)
  have pk₁₃ : PK s s₁₃ := pk₉.trans ((PK.ofKeeps k₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans
    (PK.ofUpd u₁₃))))
  have E₁₃ := E.of_pk pk₁₃
  have m₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hb₂ : VG.Proof.Gather.PPC64LE.BytesPre s₁₃ (c.W + BitVec.ofNat 64 96) (c.W + BitVec.ofNat 64 256) c.tl :=
    { r3 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, k₁₀.gpr _ (by decide),
        E₉.r14]; rfl
      r9 := by rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), k₁₀.gpr _ (by decide), E₉.r14]; rfl
      r4 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), k₁₀.gpr _ (by decide), E₉.r15]
      pos := by omega_arith
      lt := by omega_arith
      rd := E₁₃.perm.wCR (by omega_arith)
      wr := E₁₃.perm.wC (by omega_arith)
      disj := L.w_w (.inl (by omega_arith)) (by omega_arith) (by omega_arith) }
  refine WP.seq (WP.mono (copyBytes_wp s₁₃ hb₂) fun s₁₄ ⟨hm₁₄, _, k₁₄⟩ => ?_)
  have E₁₄ := E₁₃.of_pk (PK.ofKeeps k₁₄)
  refine WP.mono (cmpTail_wp E₁₄) fun s₁₅ ⟨pk₁₅, m₁₅, r21₁₅⟩ => ?_
  -- What `cmp` writes: the two padded blocks at `W + 256`.
  have s256 : Region.Sub ⟨c.W + BitVec.ofNat 64 256, 16⟩ ⟨c.W + BitVec.ofNat 64 256, 32⟩ :=
    Region.sub_prefix (by decide)
  have s272 : Region.Sub ⟨c.W + BitVec.ofNat 64 272, 16⟩ ⟨c.W + BitVec.ofNat 64 256, 32⟩ :=
    Offset.sub c.W (by decide) (by decide)
  have one : ∀ {r : Region}, Region.Sub r ⟨c.W + BitVec.ofNat 64 256, 32⟩ →
      ∀ x ∈ [r], ∃ r' ∈ [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)], Region.Sub x r' := fun h x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, h⟩
  have f₉ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₉.mem := (f256.sub (one s256)).trans (f272.sub (one s272))
  have w₁₀ : Frame [⟨c.W + BitVec.ofNat 64 272, 16⟩] s₉.mem s₁₃.mem := by
    rw [m₁₃, hm₁₀]
    exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Offset.contains c.W (Nat.le_refl _) (by omega_arith) (by decide))
  have w₁₄ : Frame [⟨c.W + BitVec.ofNat 64 256, 16⟩] s₁₃.mem s₁₄.mem := by
    rw [hm₁₄]
    exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Offset.contains c.W (Nat.le_refl _) (by omega_arith) (by decide))
  have f₁₃ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₁₃.mem := f₉.trans (w₁₀.sub (one s272))
  refine ⟨pk₁₃.trans ((PK.ofKeeps k₁₄).trans pk₁₅), ?_, ?_⟩
  · rw [m₁₅]; exact f₁₃.trans (w₁₄.sub (one s256))
  · have hA : bytesAt s₁₃.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl :=
      Proof.Cmac.bytesAt_frame f₁₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide))
        (by omega_arith)
    have hB : bytesAt s₉.mem c.T c.tl = bytesAt s.mem c.T c.tl :=
      Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.t_w.sub_right (Lay.wSub (by decide)))
        (by omega_arith)
    have z256' : bytesAt s₁₃.mem (c.W + BitVec.ofNat 64 256) 16 = Spec.Ccm.zeros 16 := by
      rw [Proof.Cmac.bytesAt_frame w₁₀ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide)]
      exact z256
    have h256 : bytesAt s₁₄.mem (c.W + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl ++ Spec.Ccm.zeros (16 - c.tl) := by
      rw [hm₁₄, Proof.AesCcm.pad_bytes z256' _ (by rw [length_bytesAt]; omega_arith), length_bytesAt, hA]
    have h272 : bytesAt s₁₄.mem (c.W + BitVec.ofNat 64 272) 16 = bytesAt s.mem c.T c.tl ++ Spec.Ccm.zeros (16 - c.tl) := by
      rw [Proof.Cmac.bytesAt_frame w₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), m₁₃, hm₁₀, Proof.AesCcm.pad_bytes z272 _ (by rw [length_bytesAt]; omega_arith), length_bytesAt, hB]
    rw [r21₁₅, h256, h272]
    congr 2
    exact propext (Proof.AesCcm.pad_eq (by rw [length_bytesAt, length_bytesAt]))

/-- One byte ANDed with `0 − r21`: the byte if `P`, else 0. -/
theorem mask_byte (b : Byte) (P : Prop) [Decidable P] :
    ((b.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0))).setWidth 8 : Byte) =
      if P then b else 0 := by
  rw [BitVec.setWidth_and, VG.Proof.Gather.PPC64LE.byte_rt]
  by_cases hP : P <;> simp only [hP, ite_true, ite_false]
  · rw [show ((BitVec.ofNat 64 0 - BitVec.ofNat 64 1).setWidth 8 : Byte) = BitVec.allOnes 8 by decide,
      BitVec.and_allOnes]
  · rw [show ((BitVec.ofNat 64 0 - BitVec.ofNat 64 0).setWidth 8 : Byte) = 0 by decide]
    simp

/-- The byte just past what `writeBytes` writes is unchanged. -/
theorem writeBytes_end (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 xs.length) = m (q + BitVec.ofNat 64 xs.length) := by
  simp only [writeBytes]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp

/-- `mask`: every byte of the data kept if `P`, zeroed if not, for `r21` the
indicator of `P`. -/
theorem mask_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Prop} [Decidable P]
    (h21 : s.gpr .r21 = BitVec.ofNat 64 (if P then 1 else 0)) :
    WP isa mask s fun s' => PK s s' ∧ s'.gpr .r21 = s.gpr .r21 ∧
      s'.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D c.n).map fun b => if P then b else 0) := by
  have hn := L.n_lt
  unfold mask
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    WP.block_nil ?_)
  have pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r21₄ : s₄.gpr .r21 = s.gpr .r21 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have r9₄ : s₄.gpr .r9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h21]
  have r3₄ : s₄.gpr .r3 = c.D := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.r22]
  have r4₄ : s₄.gpr .r4 = BitVec.ofNat 64 c.n := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.r23]
  have E₄ := E.of_pk pk₄
  let f : Byte → Byte := fun b => if P then b else 0
  refine WP.ite (decide (c.n = 0)) (eval_zero r4₄ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₄, r21₄, ?_⟩
    rw [m₄, h0]
    simp [bytesAt, writeBytes_nil]
  · have h0 : c.n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (t : State) => ∃ i, w = c.n - i ∧ i < c.n ∧ t.gpr .r3 = c.D + BitVec.ofNat 64 i ∧
        t.gpr .r4 = BitVec.ofNat 64 (c.n - i) ∧ t.gpr .r9 = s₄.gpr .r9 ∧ t.gpr .r21 = s.gpr .r21 ∧
        t.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D i).map f) ∧ PK s t) ?_ (c.n - 0) _
      ⟨0, rfl, by omega_arith, by rw [r3₄]; exact (BitVec.add_zero _).symm, by rw [r4₄, Nat.sub_zero], rfl, r21₄,
        by rw [m₄]; simp [bytesAt, writeBytes_nil], pk₄⟩
    rintro w t ⟨i, rfl, hi, r3, r4, r9, r21, mem, pk⟩
    have Et := E.of_pk pk
    have hin : i + 1 ≤ c.n := by omega_arith
    have hD : Covers [⟨c.D, c.n⟩] t.wr := Et.perm.d
    unfold maskBody
    refine wp_lbz (a := c.D + BitVec.ofNat 64 i) (by decide) (by decide)
      (by rw [r3]; exact BitVec.add_zero _)
      (VG.Proof.Gather.PPC64LE.in_off (Covers.right hD) hin hn) fun t₁ u₁ => ?_
    refine wp_and fun t₂ u₂ => ?_
    refine wp_stb (a := c.D + BitVec.ofNat 64 i) (by decide) (by decide)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), r3]; exact BitVec.add_zero _)
      (by rw [u₂.wr, u₁.wr]; exact VG.Proof.Gather.PPC64LE.in_off hD hin hn) fun t₃ u₃ => ?_
    refine wp_addi (by decide) (by decide) fun t₄ u₄ => wp_subi (by decide) (by decide) fun t₅ u₅ =>
      WP.block_nil ?_
    have pk₅ : PK s t₅ := pk.trans ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans
      ((PK.ofUpd u₄).trans (PK.ofUpd u₅)))))
    have hlen : ((bytesAt s.mem c.D i).map f).length = i := by rw [List.length_map, length_bytesAt]
    have hb : t.mem (c.D + BitVec.ofNat 64 i) = s.mem (c.D + BitVec.ofNat 64 i) := by
      rw [mem]
      have := writeBytes_end s.mem c.D ((bytesAt s.mem c.D i).map f) (by rw [hlen]; omega_arith)
      rwa [hlen] at this
    have hmem : t₅.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D (i + 1)).map f) := by
      rw [u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₁.other .r9 (by decide), r9, r9₄, u₂.mem,
        u₁.mem, mask_byte, hb, mem, Proof.Cmac.Stream.bytesAt_append, VG.Proof.Gather.PPC64LE.bytesAt_one,
        List.map_append, List.map_singleton]
      rw [writeBytes_snoc _ _ _ _ (by rw [hlen]; omega_arith), hlen]
    have hstep : c.D + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have r3' : t₅.gpr .r3 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r3, hstep]
    have r4' : t₅.gpr .r4 = BitVec.ofNat 64 (c.n - (i + 1)) := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r4,
        VG.Proof.Gather.PPC64LE.ofNat_sub_one (by omega_arith), Nat.sub_sub]
    have r9' : t₅.gpr .r9 = s₄.gpr .r9 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r9]
    have r21' : t₅.gpr .r21 = s.gpr .r21 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
        r21]
    have ev := eval_nonzero (r := .r4) (a := c.n - (i + 1)) r4' (by omega_arith)
    by_cases he : i + 1 = c.n
    · left
      exact ⟨by rw [ev]; simp [he], pk₅, r21', by rw [hmem, he]⟩
    · right
      exact ⟨by rw [ev]; simp; omega_arith, c.n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, r3', r4', r9', r21', hmem, pk₅⟩

end VG.Proof.AesCcm.PPC64LE
