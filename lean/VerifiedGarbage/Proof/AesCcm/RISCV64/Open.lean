module

import VerifiedGarbage.Proof.AesCcm.RISCV64.Seal
import VerifiedGarbage.Proof.AesCcm.Compare
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Entry
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesCcm.RISCV64.Chunk
import VerifiedGarbage.Proof.AesCcm.RISCV64.Crypt
import VerifiedGarbage.Proof.AesCcm.RISCV64.Ctrs
import VerifiedGarbage.Proof.AesCcm.RISCV64.Exit
import VerifiedGarbage.Proof.AesCcm.RISCV64.Mac
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp

/-!
# AES-CCM on RISCV64: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, `Ctr₀`
(`ctrs`), counter mode over the data (`ctr`), which decrypts it, the MAC of
the plaintext (`mac uO`), encrypted at `W + 96` (`tag uO`), the comparison
with the received tag, whose address the entry keeps in `W` (`cmp`), the
plaintext zeroed unless they are equal (`mask`), the result in `a0` and
`restore` (`open_wp`). `cmp` copies the first `tag_len` bytes of the
received tag (at `s5`) and of the computed one (at `W + 96`) over zeros at
`W + 272` and `W + 256`, and leaves 1 in `s8` iff the two padded blocks are
equal, without a branch (`cmp_wp`); `mask` ANDs every byte of the data with
`0 − s8` (`mask_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.RISCV64.Spill (Saved)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher
  cryptTag_eq_iff)

/-! ## Checking the received tag -/

theorem wp_and {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `1 − (0 <ᵤ d)`: 1 if `d` is 0, else 0. -/
theorem zero_test (d : BitVec 64) :
    BitVec.ofNat 64 1 - (if BitVec.ofNat 64 0 < d then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  by_cases hd : d = 0
  · subst hd; decide
  · have h : BitVec.ofNat 64 0 < d := by
      rw [BitVec.lt_def]
      have : d.toNat ≠ 0 := fun h => hd (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [BitVec.toNat_ofNat]; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false hd)]; decide

/-- The comparison's last block: `s8` is 1 iff the 16 bytes at `W + 256` and
at `W + 272` are equal. -/
theorem cmpTail_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block [.load .d .t0 .s1 vO, .load .d .t1 .s1 rO, .logic .xor .t0 .t0 .t1,
      .load .d .t1 .s1 (vO + 8), .load .d .t2 .s1 (rO + 8), .logic .xor .t1 .t1 .t2,
      .logic .or .t0 .t0 .t1, .li .t1 0, .sltu .t0 .t1 .t0, .li .s8 1, .sub .s8 .s8 .t0]) s fun s' =>
      PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .s8 = BitVec.ofNat 64 (if bytesAt s.mem (c.W + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (c.W + BitVec.ofNat 64 272) 16 then 1 else 0) := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 256) (by decide) (by rw [E.s1]; rfl)
    (L.alW (by decide) (by decide)) (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 272) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 264) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl)
    (L.alW (by decide) (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 280) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      E.s1]; rfl)
    (L.alW (by decide) (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₅ u₅ => ?_
  refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_sltu fun s₉ u₉ =>
    wp_li (by decide) fun s₁₀ u₁₀ => wp_sub fun s₁₁ u₁₁ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans (PK.ofUpd u₁₁)))))))))),
    by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem], ?_⟩
  have hd : s₇.gpr .t0 =
      (s.mem.readW (c.W + BitVec.ofNat 64 256) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 272) 64) |||
      (s.mem.readW (c.W + BitVec.ofNat 64 264) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 280) 64) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .t0 (by decide), u₅.gpr, u₅.other .t1 (by decide), u₄.gpr,
      u₅.other .t0 (by decide), u₄.other .t0 (by decide), u₃.gpr, u₂.gpr, u₂.other .t0 (by decide), u₁.gpr,
      u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other .t0 (by decide), u₉.gpr, u₈.gpr, u₈.other .t0 (by decide), hd, zero_test]
  have hw := Proof.AesCcm.words_eq s.mem (c.W + BitVec.ofNat 64 256) (c.W + BitVec.ofNat 64 272)
  rw [Offset.add_add, Offset.add_add] at hw
  congr 2
  exact propext hw

/-- `cmp`: 1 in `s8` iff the `tag_len` bytes at `T` (`s5`) are the first
`tag_len` of the computed tag at `W + 96`. -/
theorem cmp_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (hs5 : s.gpr .s5 = c.T) :
    WP isa cmp s fun s' => PK s s' ∧ Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem ∧
      s'.gpr .s8 = BitVec.ofNat 64
        (if bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem c.T c.tl then 1 else 0) := by
  have ht4 := L.t4
  have ht16 := L.t16
  unfold cmp zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_sd (a := c.W + BitVec.ofNat 64 256) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide)) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.alW (by decide) (by decide))
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 272) (by decide)
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1]; rfl)
    (L.alW (by decide) (by decide))
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₅ u₅ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.alW (by decide) (by decide))
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₆ u₆ => ?_
  refine wp_mv fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  have pk₉ : PK s s₉ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofMupd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))))))))
  have E₉ := E.of_pk pk₉
  have m₉ : s₉.mem = (((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272)
      (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr]
    rfl
  have g₉ : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₉.gpr r = s.gpr r := fun r h0 h3 h9 h4 => by
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
    L.t_w.sub_right (Lay.wSub (by omega))
  have hb₁ : BytesPre s₉ c.T (c.W + BitVec.ofNat 64 272) c.tl :=
    { a0 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs5]
      a1 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1]; rfl
      a2 := by rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s2]
      pos := by omega
      lt := by omega
      rd := by rw [pk₉.rd, pk₉.wr]; exact E.perm.t
      wr := E₉.perm.wC (by omega)
      disj := hdT }
  refine WP.seq (WP.mono (copy_wp s₉ hb₁) fun s₁₀ ⟨hm₁₀, _, k₁₀⟩ => ?_)
  refine WP.seq (wp_addi (by decide) fun s₁₁ u₁₁ => wp_addi (by decide) fun s₁₂ u₁₂ =>
    wp_mv fun s₁₃ u₁₃ => WP.block_nil ?_)
  have pk₁₃ : PK s s₁₃ := pk₉.trans ((PK.ofKeeps k₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans
    (PK.ofUpd u₁₃))))
  have E₁₃ := E.of_pk pk₁₃
  have m₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hb₂ : BytesPre s₁₃ (c.W + BitVec.ofNat 64 96) (c.W + BitVec.ofNat 64 256) c.tl :=
    { a0 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, k₁₀.gpr _ (by decide),
        E₉.s1]; rfl
      a1 := by rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), k₁₀.gpr _ (by decide), E₉.s1]; rfl
      a2 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), k₁₀.gpr _ (by decide), E₉.s2]
      pos := by omega
      lt := by omega
      rd := E₁₃.perm.wCR (by omega)
      wr := E₁₃.perm.wC (by omega)
      disj := L.w_w (.inl (by omega)) (by omega) (by omega) }
  refine WP.seq (WP.mono (copy_wp s₁₃ hb₂) fun s₁₄ ⟨hm₁₄, _, k₁₄⟩ => ?_)
  have E₁₄ := E₁₃.of_pk (PK.ofKeeps k₁₄)
  refine WP.mono (cmpTail_wp L E₁₄) fun s₁₅ ⟨pk₁₅, m₁₅, s8₁₅⟩ => ?_
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
    exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Offset.contains c.W (Nat.le_refl _) (by omega) (by decide))
  have w₁₄ : Frame [⟨c.W + BitVec.ofNat 64 256, 16⟩] s₁₃.mem s₁₄.mem := by
    rw [hm₁₄]
    exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Offset.contains c.W (Nat.le_refl _) (by omega) (by decide))
  have f₁₃ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₁₃.mem := f₉.trans (w₁₀.sub (one s272))
  refine ⟨pk₁₃.trans ((PK.ofKeeps k₁₄).trans pk₁₅), ?_, ?_⟩
  · rw [m₁₅]; exact f₁₃.trans (w₁₄.sub (one s256))
  · have hA : bytesAt s₁₃.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl :=
      Proof.Cmac.bytesAt_frame f₁₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by decide))
        (by omega)
    have hB : bytesAt s₉.mem c.T c.tl = bytesAt s.mem c.T c.tl :=
      Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.t_w.sub_right (Lay.wSub (by decide)))
        (by omega)
    have z256' : bytesAt s₁₃.mem (c.W + BitVec.ofNat 64 256) 16 = Spec.Ccm.zeros 16 := by
      rw [Proof.Cmac.bytesAt_frame w₁₀ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide)]
      exact z256
    have h256 : bytesAt s₁₄.mem (c.W + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl ++ Spec.Ccm.zeros (16 - c.tl) := by
      rw [hm₁₄, Proof.AesCcm.pad_bytes z256' _ (by rw [length_bytesAt]; omega), length_bytesAt, hA]
    have h272 : bytesAt s₁₄.mem (c.W + BitVec.ofNat 64 272) 16 = bytesAt s.mem c.T c.tl ++ Spec.Ccm.zeros (16 - c.tl) := by
      rw [Proof.Cmac.bytesAt_frame w₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), m₁₃, hm₁₀, Proof.AesCcm.pad_bytes z272 _ (by rw [length_bytesAt]; omega), length_bytesAt, hB]
    rw [s8₁₅, h256, h272]
    congr 2
    exact propext (Proof.AesCcm.pad_eq (by rw [length_bytesAt, length_bytesAt]))

/-- One byte ANDed with `0 − s8`: the byte if `P`, else 0. -/
theorem mask_byte (b : Byte) (P : Prop) [Decidable P] :
    ((b.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0))).setWidth 8 : Byte) =
      if P then b else 0 := by
  rw [BitVec.setWidth_and, byte_rt]
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

/-- `mask`: every byte of the data kept if `P`, zeroed if not, for `s8` the
indicator of `P`. -/
theorem mask_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Prop} [Decidable P]
    (hs8 : s.gpr .s8 = BitVec.ofNat 64 (if P then 1 else 0)) :
    WP isa mask s fun s' => PK s s' ∧ s'.gpr .s8 = s.gpr .s8 ∧
      s'.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D c.n).map fun b => if P then b else 0) := by
  have hn := L.n_lt
  unfold mask
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    WP.block_nil ?_)
  have pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have s8₄ : s₄.gpr .s8 = s.gpr .s8 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have r9₄ : s₄.gpr .t1 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hs8]
  have r3₄ : s₄.gpr .a0 = c.D := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s9]
  have r4₄ : s₄.gpr .a2 = BitVec.ofNat 64 c.n := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s10]
  have E₄ := E.of_pk pk₄
  let f : Byte → Byte := fun b => if P then b else 0
  refine WP.ite (decide (c.n = 0)) (eval_z r4₄ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₄, s8₄, ?_⟩
    rw [m₄, h0]
    simp [bytesAt, writeBytes_nil]
  · have h0 : c.n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (t : State) => ∃ i, w = c.n - i ∧ i < c.n ∧ t.gpr .a0 = c.D + BitVec.ofNat 64 i ∧
        t.gpr .a2 = BitVec.ofNat 64 (c.n - i) ∧ t.gpr .t1 = s₄.gpr .t1 ∧ t.gpr .s8 = s.gpr .s8 ∧
        t.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D i).map f) ∧ PK s t) ?_ (c.n - 0) _
      ⟨0, rfl, by omega, by rw [r3₄]; exact (BitVec.add_zero _).symm, by rw [r4₄, Nat.sub_zero], rfl, s8₄,
        by rw [m₄]; simp [bytesAt, writeBytes_nil], pk₄⟩
    rintro w t ⟨i, rfl, hi, r3, r4, r9, s8, mem, pk⟩
    have Et := E.of_pk pk
    have hin : i + 1 ≤ c.n := by omega
    have hD : Covers [⟨c.D, c.n⟩] t.wr := Et.perm.d
    unfold maskBody
    refine wp_lbu (a := c.D + BitVec.ofNat 64 i) (by decide)
      (by rw [r3]; exact BitVec.add_zero _)
      (in_off (Covers.right hD) hin hn) fun t₁ u₁ => ?_
    refine wp_and fun t₂ u₂ => ?_
    refine wp_sb (a := c.D + BitVec.ofNat 64 i) (by decide)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), r3]; exact BitVec.add_zero _)
      (by rw [u₂.wr, u₁.wr]; exact in_off hD hin hn) fun t₃ u₃ => ?_
    refine wp_addi (by decide) fun t₄ u₄ => wp_subi (by decide) fun t₅ u₅ =>
      WP.block_nil ?_
    have pk₅ : PK s t₅ := pk.trans ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans
      ((PK.ofUpd u₄).trans (PK.ofUpd u₅)))))
    have hlen : ((bytesAt s.mem c.D i).map f).length = i := by rw [List.length_map, length_bytesAt]
    have hb : t.mem (c.D + BitVec.ofNat 64 i) = s.mem (c.D + BitVec.ofNat 64 i) := by
      rw [mem]
      have := writeBytes_end s.mem c.D ((bytesAt s.mem c.D i).map f) (by rw [hlen]; omega)
      rwa [hlen] at this
    have hmem : t₅.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D (i + 1)).map f) := by
      rw [u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₁.other .t1 (by decide), r9, r9₄, u₂.mem,
        u₁.mem, mask_byte, hb, mem, Proof.Cmac.Stream.bytesAt_append, bytesAt_one,
        List.map_append, List.map_singleton]
      rw [writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen]
    have hstep : c.D + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have r3' : t₅.gpr .a0 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r3, hstep]
    have r4' : t₅.gpr .a2 = BitVec.ofNat 64 (c.n - (i + 1)) := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r4,
        ofNat_sub_one (by omega), Nat.sub_sub]
    have r9' : t₅.gpr .t1 = s₄.gpr .t1 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r9]
    have s8' : t₅.gpr .s8 = s.gpr .s8 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
        s8]
    have ev := eval_nz (r := .a2) (a := c.n - (i + 1)) r4' (by omega)
    by_cases he : i + 1 = c.n
    · left
      exact ⟨by rw [ev]; simp [he], pk₅, s8', by rw [hmem, he]⟩
    · right
      exact ⟨by rw [ev]; simp; omega, c.n - (i + 1), by omega, i + 1, rfl, by omega, r3', r4', r9', s8', hmem, pk₅⟩

/-! ## The function -/

theorem cmpR_mut (c : Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_hi (by decide) (by decide)

theorem maskR_mut (c : Cx) : ∀ r ∈ [(⟨c.D, c.n⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_data

theorem cmpR_list (W : Addr) : [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)] =
    [(256, 32)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

theorem length_chain {ciph : Spec.Ccm.Cipher} (hc : BlockCipher ciph) :
    ∀ (ms : List (List Byte)) (c : List Byte), c.length = 16 → (Spec.Cmac.chain ciph c ms).length = 16
  | [], _, h => h
  | _ :: ms, _, _ => length_chain hc ms _ (hc _)

/-- The data masked: itself if `P`, zeros if not. -/
theorem masked {m : Mem} {D : Addr} {n : Nat} (hn : n < 2 ^ 64) (P : Prop) [Decidable P] :
    bytesAt (writeBytes m D ((bytesAt m D n).map fun b => if P then b else 0)) D n =
      if P then bytesAt m D n else Spec.Ccm.zeros n := by
  rw [Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [List.length_map, length_bytesAt]) hn,
    List.length_map, length_bytesAt, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil]
  by_cases hP : P
  · simp [hP]
  · simp only [hP, ite_false, Spec.Ccm.zeros]
    rw [List.map_const', length_bytesAt]

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧
      openOut (Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n) (bytesAt s.mem c.A c.al) (bytesAt s.mem c.T c.tl)) (s'.gpr .a0)
        (bytesAt s'.mem c.D c.n) c.n := by
  have L := Ar.lay
  have ht16 := L.t16
  have hn := L.n_lt
  unfold «open»
  refine WP.seq (WP.mono (entry_wp Ar) fun s₁ En => ?_)
  have hN₁ : Buf c s₁ N c.nl := Ar.nonce.of_eq En.rd En.wr
  refine WP.seq (WP.mono (ctrs_wp L En.env hN₁ En.a2 En.a3) fun s₂ ⟨pk₂, f₂, c₂⟩ => ?_)
  rw [entry_buf En.frame Ar.nonce] at c₂
  have hnl : (bytesAt s.mem N c.nl).length = c.nl := length_bytesAt _ _ _
  have f₂' : Frame (mutR c) s₁.mem s₂.mem := f₂.sub (c0_mut c)
  have E₂ := En.env.of_pk pk₂
  refine WP.seq (WP.mono (ctr_wp L E₂ hnl c₂) fun s₃ ⟨pk₃, f₃, h₃⟩ => ?_)
  have E₃ := E₂.of_pk pk₃
  have f₁₃ : Frame (mutR c) s₁.mem s₃.mem := f₂'.trans (f₃.sub (crR_mut c))
  have c₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.Cmac.bytesAt_frame f₃ (crR_disj L (.inl (by decide))) (by decide), c₂]
  refine WP.seq (WP.mono (mac_wp L E₃ (En.slots.mut L f₁₃) hnl c₃ (.inr rfl)) fun s₄ M => ?_)
  have fM := M.frame
  rw [macR_list] at fM
  have c₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide), c₃]
  have E₄ := E₃.of_pk M.pk
  refine WP.seq (WP.mono (tag_wp L E₄ hnl c₄ (.inr rfl)) fun s₅ ⟨pk₅, _, f₅, h₅⟩ => ?_)
  have E₅ := E₄.of_pk pk₅
  have f₁₄ : Frame (mutR c) s₁.mem s₄.mem := f₁₃.trans (M.frame.sub (macR_mut (.inr rfl)))
  have f₁₅ : Frame (mutR c) s₁.mem s₅.mem := f₁₄.trans (f₅.sub (ctrR_mut c (.inr rfl)))
  -- The address of the received tag, from its slot.
  refine WP.seq (wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [E₅.s1]; rfl)
    (L.alW (by decide) (by decide)) (E₅.perm.wR (by decide)) fun s₆ u₆ => WP.block_nil ?_)
  have pk₆ : PK s₅ s₆ := PK.ofUpd u₆
  have m₆ : s₆.mem = s₅.mem := u₆.mem
  have s5₆ : s₆.gpr .s5 = c.T := by rw [u₆.gpr]; exact (En.slots.mut L f₁₅).tag
  refine WP.seq (WP.mono (cmp_wp L (E₅.of_pk pk₆) s5₆) fun s₇ ⟨pk₇, f₇, s8₇⟩ => ?_)
  rw [m₆] at s8₇ f₇
  -- What the comparison compares.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m c.K c.R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have k₁ := entry_ciph L En.frame
  have k₂ : Spec.Ccm.ctxCiph s₂.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₂', k₁]
  have k₃ : Spec.Ccm.ctxCiph s₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₃, k₁]
  have k₄ : Spec.Ccm.ctxCiph s₄.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₄, k₁]
  have bD := L.bufD Ar.perm
  have bD₁ : Buf c s₁ c.D c.n := bD.of_eq En.rd En.wr
  have hd₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [c0_list] at f₂
    rw [Proof.Cmac.bytesAt_frame f₂ (bufW_keep bD₁ (by decide)) (by omega), entry_buf En.frame bD]
  have ha₃ : bytesAt s₃.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [aad_mut L f₁₃, entry_buf En.frame (L.bufA Ar.perm)]
  have hpt : bytesAt s₃.mem c.D c.n =
      Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n) := by
    rw [h₃, k₂, hd₂, crypt_eq (hBC _)]
  have hd₇ : bytesAt s₇.mem c.D c.n = bytesAt s₃.mem c.D c.n := by
    rw [cmpR_list] at f₇
    rw [ctrR_list] at f₅
    rw [Proof.Cmac.bytesAt_frame f₇ (bufW_keep bD₁ (by decide)) (by omega),
      Proof.Cmac.bytesAt_frame f₅ (bufW_keep bD₁ (by decide)) (by omega),
      Proof.Cmac.bytesAt_frame fM (bufW_keep bD₁ (by decide)) (by omega)]
  have hrecv : bytesAt s₅.mem c.T c.tl = bytesAt s.mem c.T c.tl := by
    rw [tag_mut L f₁₅, Proof.Cmac.bytesAt_frame En.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_w.sub_right (Lay.wSub (by decide))) (by omega)]
  have hcomp : bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) c.tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))) := by
    rw [show c.W + BitVec.ofNat 64 96 = c.W + BitVec.ofNat 64 uO from rfl, Proof.AesCcm.bytesAt_prefix s₅.mem _ L.t16,
      h₅, k₄, take_xorFrom_zero (hBC _) _ (length_bytesAt _ _ _) L.t16, M.out, k₃,
      ha₃, hpt, mac_eq _ _ (by rw [hnl]; have := L.h13; omega)]
    rfl
  rw [hcomp, hrecv] at s8₇
  refine WP.seq (WP.mono (mask_wp L (E₅.of_pk (pk₆.trans pk₇)) s8₇) fun s₈ ⟨pk₈, s8₈, m₈⟩ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₉ u₉ => ?_
  have f₈ : Frame [⟨c.D, c.n⟩] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [List.length_map, length_bytesAt]; exact Region.contains_self _ _)
  have f₁₈ : Frame (mutR c) s₁.mem s₈.mem :=
    (f₁₅.trans ((m₆ ▸ (show Frame [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)] s₆.mem s₇.mem by
      rw [m₆]; exact f₇)).sub (cmpR_mut c))).trans (f₈.sub (maskR_mut c))
  have pk₁₉ : PK s₁ s₉ := pk₂.trans (pk₃.trans (M.pk.trans (pk₅.trans (pk₆.trans (pk₇.trans (pk₈.trans
    (PK.ofUpd u₉)))))))
  have sv₉ : Saved c.W s.gpr savedL s₉.mem := by rw [u₉.mem]; exact saved_mut L f₁₈ En.saved
  refine WP.mono (exit_wp L (En.env.of_pk pk₁₉) sv₉ (by rw [pk₁₉.sp, En.sp])
    (fun r hr => by rw [pk₁₉.gpr r (other_keep r hr), En.others r hr])) fun s' ⟨abi, hm, r3'⟩ => ⟨abi, ?_⟩
  -- The result.
  have hmlen : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
      (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))).length =
      c.tl := by
    rw [mac_eq _ _ (by rw [hnl]; have := L.h13; omega), List.length_take,
      length_chain (hBC _) _ _ (by simp [Spec.Cmac.zeros])]
    omega
  have hiff := cryptTag_eq_iff (hBC s.mem) L.t16 (bytesAt s.mem N c.nl) hmlen (length_bytesAt s.mem c.T c.tl)
  have hr3 : s'.gpr .a0 = s₇.gpr .s8 := by rw [r3', u₉.gpr, s8₈]
  simp only [openOut, Spec.Ccm.decryptWith]
  rw [hr3, s8₇, hm, u₉.mem, m₈, masked hn, hd₇, hpt]
  by_cases he : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
      (bytesAt s.mem c.T c.tl) = Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (bytesAt s.mem c.A c.al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n))
  · have hq := hiff.mpr he.symm
    simp only [he, hq, ite_true]
    exact ⟨by decide, trivial⟩
  · have hq : ¬ _ := fun h => he (hiff.mp h).symm
    simp only [he, hq, ite_false]
    exact ⟨by decide, trivial⟩

/-- `vg_aes_ccm_open`. -/
theorem open_wp {s : State} (h : openRISCV64.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openRISCV64.post s s' :=
  WP.mono (open_wp' (args_of_open h)) fun _ hp => hp

end VG.Proof.AesCcm.RISCV64
