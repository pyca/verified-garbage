module

public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Absorb
public import VerifiedGarbage.Proof.GcmSiv.Words
import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
public import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# AES-GCM-SIV on RISC-V: POLYVAL (`polyval`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Polyval.lean`): `absorb` absorbs a string's whole
blocks (`Proof/AesGcmSiv/RISCV64/Absorb.lean`) and its last bytes, padded
with zeros at `W + 240` (`absTail_wp`); `lens` absorbs the lengths block,
and `tagIn` writes the tag input at `W + 96` from the accumulator, loaded
big-endian, and the nonce's copy at `W + 1520` (`polyval_wp`): POLYVAL
computed as GHASH with the key `H · x` (`Proof.GcmSiv.Words.tagInputG`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_addi wp_li wp_ld wp_lwu wp_sd wp_sll wp_srl wp_mv wp_xor)
open VG.Proof.AesGcm.RISCV64 (LoopPre LoopOut copyLoop_ok covers_prefix)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)

/-- What absorbing a string leaves. -/
abbrev AbsPost (c : Cx) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop := Absorbed c (absorbR c) xs t t'

theorem AbsPost.trans {c : Cx} (L : Lay c) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : AbsPost c xs t t₁) (h₂ : AbsPost c ys t₁ t₂) : AbsPost c (xs ++ ys) t t₂ :=
  Absorbed.trans (absorbR_H L) h₁ h₂

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero2 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  rw [Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by omega_arith) (by decide), Proof.Cmac.zero2_bytes]
  simp only [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

/-- The block at `W + 240` as a chunk's source. -/
theorem srcB {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Src c s (c.W + BitVec.ofNat 64 240) 16 where
  rd := P.wCR (by decide)
  lt := by decide
  wrap := by rw [L.wrapW (by decide)]; have := L.ww; omega_arith
  y := L.w_w (.inr (by decide)) (by decide) (by decide)
  rev := L.w_w (.inl (by decide)) (by decide) (by decide)
  gh := L.w_w (.inl (by decide)) (by decide) (by decide)
  b := L.b_w' (by decide)

/-- One chunk of the 16 bytes at `W + 240`: their field element absorbed. -/
theorem chunkB_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    (h9 : t.gpr .s9 = c.W + BitVec.ofNat 64 240) (h10 : t.gpr .s10 = BitVec.ofNat 64 16) :
    WP isa chunk t (Absorbed c (absR c) [Spec.GcmSiv.ofBytes (bytesAt t.mem (c.W + BitVec.ofNat 64 240) 16)] t) :=
  WP.mono (chunk_wp L E (m := 16) (by decide) (by decide) (srcB L E.perm) h9 h10) fun t' C => by
    have A := Absorbed.of_chunk C
    simpa [elemsAt] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 240`, as the
bytes to absorb. -/
structure TailPre (c : Cx) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  pk : PK t t₃
  s9 : t₃.gpr .s9 = c.W + BitVec.ofNat 64 240
  s10 : t₃.gpr .s10 = BitVec.ofNat 64 16
  frame : Frame [⟨c.W + BitVec.ofNat 64 240, 16⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (c.W + BitVec.ofNat 64 240) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨c.W, 3840⟩) (h9 : t.gpr .s9 = P) (h10 : t.gpr .s10 = BitVec.ofNat 64 r) :
    WP isa absTailPre t (TailPre c P r t) := by
  have hw := L.ww
  unfold absTailPre zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun t₁ u₁ => ?_)
  refine wp_sd (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [u₁.other _ (by decide), E.s0]; rfl)
    (L.wal8 (by decide) (by decide)) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun t₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s0, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun t₃ u₃ => ?_
  refine wp_mv fun t₄ u₄ => wp_addi (by decide) fun t₅ u₅ => wp_mv fun t₆ u₆ => WP.block_nil ?_
  have pk₆ : PK t t₆ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have E₆ := E.of_pk pk₆
  have hm₆ : t₆.mem = Proof.Cmac.zero2 t.mem (c.W + BitVec.ofNat 64 240) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem]; rfl
  have dB : (⟨P, r⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 240, r⟩ :=
    (hd.sub_right (Lay.wSub (show 240 + 16 ≤ 3840 by decide))).sub_right (Region.sub_prefix (by omega_arith))
  have lp : LoopPre t₆ P (c.W + BitVec.ofNat 64 240) r :=
    { a0 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), h9]
      a1 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), E.s0]; rfl
      a2 := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), h10]
      pos := hr1
      lt := by omega_arith
      rd := by rw [pk₆.rd, pk₆.wr]; exact hc
      wr := covers_prefix (E₆.perm.wC (show 240 + 16 ≤ 3840 by decide)) (by omega_arith)
      disj := dB }
  refine WP.seq (WP.mono (copyLoop_ok t₆ lp) fun t₇ ⟨hm₇, O⟩ => ?_)
  have pk₇ : PK t₆ t₇ := PK.ofLoop O
  -- The data is outside the zeroed block.
  have hd₆ : bytesAt t₆.mem P r = bytesAt t.mem P r := by
    rw [hm₆]
    exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _)
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide)))
      (by omega_arith)
  have hb₇ : bytesAt t₇.mem (c.W + BitVec.ofNat 64 240) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := Proof.AesCcm.length_bytesAt t.mem P r
    rw [hm₇, hd₆, hm₆, pad_bytes _ _ _ (by omega_arith), hl]
  have f₇ : Frame [⟨c.W + BitVec.ofNat 64 240, 16⟩] t.mem t₇.mem := by
    rw [hm₇, hm₆]
    exact (Proof.Cmac.frame_store2 _ _ _).trans
      ((VG.WriteBytes.writeBytes_frame _ _ _ (by
        rw [Proof.AesCcm.length_bytesAt]; exact Region.contains_self _ _)).sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)
  refine wp_addi (by decide) fun t₈ u₈ => wp_li (by decide) fun t₉ u₉ => WP.block_nil
    ⟨pk₆.trans (pk₇.trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))), ?_, u₉.gpr, by rw [u₉.mem, u₈.mem]; exact f₇,
      by rw [u₉.mem, u₈.mem]; exact hb₇⟩
  rw [u₉.other _ (by decide), u₈.gpr, (E₆.of_pk pk₇).s0]; rfl

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨c.W, 3840⟩) (h9 : t.gpr .s9 = P) (h10 : t.gpr .s10 = BitVec.ofNat 64 r) :
    WP isa absTail t (AbsPost c [Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  unfold absTail
  refine WP.seq (WP.mono (absTailPre_wp L E hr1 hr hc hd h9 h10) fun t₃ T => ?_)
  refine WP.mono (chunkB_wp L (E.of_pk T.pk) T.s9 T.s10) fun t₄ C => ?_
  rw [T.bytes] at C
  have dHY : ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 240, 16⟩ : Region)], ∀ d, d + 16 ≤ 240 →
      (⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega_arith) (by decide)
  refine ⟨T.pk.trans C.pk,
    (T.frame.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, blockAt_frame T.frame (fun q hq => dHY q hq 64 (by decide)),
    blockAt_frame T.frame (fun q hq => dHY q hq 80 (by decide))]

/-! ## Absorbing a string -/

/-- The field elements of `n` bytes at `Q`, padded. -/
theorem elems_pad16_bytesAt (m : Mem) (Q : Addr) (n : Nat) :
    Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt m Q n)) = elemsAt m Q (n / 16) ++
      if n % 16 = 0 then [] else
        [Spec.GcmSiv.ofBytes (bytesAt m (Q + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) ++
          Spec.GcmSiv.zeros (16 - n % 16))] := by
  have hs := Proof.Cmac.bytesAt_add m Q (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega_arith] at hs
  have hl := Proof.AesCcm.length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, Proof.AesCcm.length_bytesAt, hs, List.take_left' hl, List.drop_left' hl,
    GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once `a7` holds their number. -/
theorem absMid_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (hQ : Src c t Q m) (h9 : t.gpr .s9 = Q) (h10 : t.gpr .s10 = BitVec.ofNat 64 m)
    (h7 : t.gpr .a7 = BitVec.ofNat 64 (m / 16)) :
    WP isa (.ite (.zero .a7) (.block []) (.loop chunk (.nonzero .a7))) t fun t₂ =>
      Absorbed c (absR c) (elemsAt t.mem Q (m / 16)) t t₂ ∧
        t₂.gpr .s9 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t₂.gpr .s10 = BitVec.ofNat 64 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (Steps.eval_zero_ofNat _ _ (by omega_arith) h7) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨PK.refl _, Frame.refl _ _, by simp [h0, elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h9, h0, Nat.mul_zero, BitVec.add_zero], by rw [h10]; congr 1; omega_arith⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_wp L E hm (by omega_arith) (hQ.take (by omega_arith)) h9 h10

theorem absorb_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (hQ : Src c t Q m) (hd : (⟨Q, m⟩ : Region).Disjoint ⟨c.W, 3840⟩) (h9 : t.gpr .s9 = Q)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 m) :
    WP isa absorb t (AbsPost c (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem Q m))) t) := by
  unfold absorb wholeLeft
  refine WP.seq (wp_srl (by decide) fun t₁ u₁ => WP.block_nil ?_)
  have pk₁ : PK t t₁ := PK.ofUpd u₁
  refine WP.seq (WP.mono (absMid_wp L (E.of_pk pk₁) hm (hQ.of_eq pk₁.rd pk₁.wr)
    (by rw [u₁.other _ (by decide), h9]) (by rw [u₁.other _ (by decide), h10])
    (by rw [u₁.gpr, h10, ofNat_lsr 4 hm])) fun t₂ ⟨P₂, s9₂, s10₂⟩ => ?_)
  rw [u₁.mem] at P₂
  have P₂' := P₂.of_eq pk₁ u₁.mem
  rw [elems_pad16_bytesAt]
  refine WP.ite (decide (m % 16 = 0)) (Steps.eval_zero_ofNat _ _ (by omega_arith) s10₂) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₂'.sub (absR_sub c))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega_arith) (by omega_arith)
    have dT : (⟨Q + BitVec.ofNat 64 (16 * (m / 16)), m % 16⟩ : Region).Disjoint ⟨c.W, 3840⟩ :=
      hd.sub_left (Offset.sub_base Q (by omega_arith))
    refine WP.mono (absTail_wp L (E.of_pk P₂'.pk) (by omega_arith) (by omega_arith)
      (by rw [P₂'.pk.rd, P₂'.pk.wr]; exact hs.rd) dT s9₂ s10₂) fun t₃ T => ?_
    have e := Proof.Cmac.bytesAt_frame (p := Q + BitVec.ofNat 64 (16 * (m / 16))) (n := m % 16) P₂'.frame
      (fun r hr => ?_) (by omega_arith)
    · rw [e] at T
      exact AbsPost.trans L (P₂'.sub (absR_sub c)) T
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact dT.sub_right (Lay.wSub (by decide))
      · exact hs.b.symm

/-! ## The lengths, and the tag input -/

/-- `lensBlock`: the lengths block at `W + 240`, as the bytes to absorb. -/
theorem lensBlk_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    WP isa (.block lensBlock) t fun t₆ => PK t t₆ ∧ t₆.mem =
      (t.mem.writeW (c.W + BitVec.ofNat 64 240) (BitVec.ofNat 64 (8 * c.al))).writeW
        (c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (BitVec.ofNat 64 (8 * c.n)) ∧
      t₆.gpr .s9 = c.W + BitVec.ofNat 64 240 ∧ t₆.gpr .s10 = BitVec.ofNat 64 16 := by
  have hw := L.ww
  unfold lensBlock
  refine wp_sll (by decide) fun t₁ u₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [u₁.other _ (by decide), E.s0]; rfl)
    (L.wal8 (by decide) (by decide)) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun t₂ u₂ => ?_
  refine wp_sll (by decide) fun t₃ u₃ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s0, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₃.wr, u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun t₄ u₄ => ?_
  refine wp_addi (by decide) fun t₅ u₅ => wp_li (by decide) fun t₆ u₆ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆))))), ?_, ?_, u₆.gpr⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.other .s7 (by decide), u₁.mem,
      E.s5, E.s7, ofNat_shl, ofNat_shl]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      E.s0]; rfl

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    WP isa lens t (AbsPost c [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * c.al) ++ Spec.GcmSiv.le64 (8 * c.n))] t) := by
  unfold lens
  refine WP.seq (WP.mono (lensBlk_wp L E) fun t₆ ⟨pk₆, hm₆, s9₆, s10₆⟩ => ?_)
  have f₆ : Frame [⟨c.W + BitVec.ofNat 64 240, 16⟩] t.mem t₆.mem := by rw [hm₆]; exact Proof.Cmac.frame_store2 _ _ _
  refine WP.mono (chunkB_wp L (E.of_pk pk₆) s9₆ s10₆) fun t₇ C => ?_
  have hb : bytesAt t₆.mem (c.W + BitVec.ofNat 64 240) 16 =
      Spec.GcmSiv.le64 (8 * c.al) ++ Spec.GcmSiv.le64 (8 * c.n) := by
    rw [hm₆, Proof.Cmac.bytesAt_store2, GcmSiv.le64_le8, GcmSiv.le64_le8]
  rw [hb] at C
  have hw := L.ww
  have dHY : ∀ d, d + 16 ≤ 240 → ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 240, 16⟩ : Region)],
      (⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega_arith) (by decide)
  refine ⟨pk₆.trans C.pk,
    (f₆.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, blockAt_frame f₆ (dHY 64 (by decide)), blockAt_frame f₆ (dHY 80 (by decide))]

theorem be64_add (m : Mem) (p : Addr) (a b : Nat) :
    ByteLoad.be64 m (p + BitVec.ofNat 64 a) b = ByteLoad.be64 m p (a + b) := by
  simp only [ByteLoad.be64, Offset.add_add, Nat.add_assoc]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W : Addr) : Mem :=
  let lo := ByteLoad.be64 m W 88 ^^^ m.readW (nP W) 64
  let hi := ((ByteLoad.be64 m W 80 ^^^ (m.readW (nP W + BitVec.ofNat 64 8) 32).setWidth 64) <<< 1) >>> 1
  (m.writeW (W + BitVec.ofNat 64 96) lo).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) hi

theorem tagInMem_bytes (m : Mem) (W : Addr) :
    bytesAt (tagInMem m W) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m (nP W) 12) := by
  rw [tagInMem, Proof.Cmac.bytesAt_store2, Proof.Gcm.RISCV64.blockAt_hOf, Proof.Gcm.RISCV64.hOf,
    GcmSiv.toBytes_append, be64_add, be64_add, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words, GcmSiv.Words.shl_shr_one]

theorem tagInMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (tagInMem m W) :=
  Proof.Cmac.frame_store2 _ _ _

theorem tagIn_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    WP isa (.block tagIn) t fun t' => PK t t' ∧ t'.mem = tagInMem t.mem c.W := by
  have hw := L.ww
  unfold tagIn
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (loadBE64_upd (s := t) (d := .a0) (tmp := .t0) (n := .s0) (off := yO + 8)
    (by decide) (by decide) (by decide) (by decide) (by rw [E.s0]; exact E.perm.wR (by decide)))
    fun t₁ ⟨v₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_)
  refine WP.block_append (WP.mono (loadBE64_upd (s := t₁) (d := .a1) (tmp := .t0) (n := .s0) (off := yO)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [rd₁, wr₁, g₁ _ (by decide) (by decide), E.s0]; exact E.perm.wR (by decide)))
    fun t₂ ⟨v₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_)
  have s0₂ : t₂.gpr .s0 = c.W := by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide) (by decide), E.s0]
  have rw₂ : t₂.rd ++ t₂.wr = t.rd ++ t.wr := by rw [rd₂, wr₂, rd₁, wr₁]
  refine wp_ld (a := nP c.W) (by decide) (by rw [s0₂, nP]; rfl) (by rw [nP]; exact L.wal8 (by decide) (by decide))
    (by rw [rw₂, nP]; exact E.perm.wR (by decide)) fun t₃ u₃ => wp_xor fun t₄ u₄ => ?_
  refine wp_lwu (a := nP c.W + BitVec.ofNat 64 8) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), s0₂, nP, Offset.add_add]; rfl)
    (by rw [nP, Offset.add_add]; exact L.wal4 (by decide) (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂, nP, Offset.add_add]; exact E.perm.wR (by decide)) fun t₅ u₅ => ?_
  refine wp_xor fun t₆ u₆ => wp_sll (by decide) fun t₇ u₇ => wp_srl (by decide) fun t₈ u₈ => ?_
  have s0₈ : t₈.gpr .s0 = c.W := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), s0₂]
  have wr₈ : t₈.wr = t.wr := by
    rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, wr₁]
  refine wp_sd (a := c.W + BitVec.ofNat 64 96) (by decide) (by rw [s0₈]; rfl) (L.wal8 (by decide) (by decide))
    (by rw [wr₈]; exact E.perm.wW (by decide)) fun t₉ u₉ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₉.gpr, s0₈, Offset.add_add]; rfl) (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₉.wr, wr₈, Offset.add_add]; exact E.perm.wW (by decide)) fun t₁₀ u₁₀ => WP.block_nil ?_
  have pk₂ : PK t t₂ := ⟨rd₂.trans rd₁, wr₂.trans wr₁, sp₂.trans sp₁, fun r hr => by
    have h0 : r ≠ .a0 := fun h => by subst h; revert hr; decide
    have h1 : r ≠ .a1 := fun h => by subst h; revert hr; decide
    have ht : r ≠ .t0 := fun h => by subst h; revert hr; decide
    rw [g₂ _ h1 ht, g₁ _ h0 ht]⟩
  refine ⟨pk₂.trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofMupd u₉).trans (PK.ofMupd u₁₀)))))))), ?_⟩
  have m₈ : t₈.mem = t.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, m₁]
  have e0 : t₈.gpr .a0 = ByteLoad.be64 t.mem c.W 88 ^^^ t.mem.readW (nP c.W) 64 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₃.gpr, g₂ _ (by decide) (by decide), v₁, m₂, m₁, E.s0]; rfl
  have e1 : t₈.gpr .a1 = ((ByteLoad.be64 t.mem c.W 80 ^^^
      (t.mem.readW (nP c.W + BitVec.ofNat 64 8) 32).setWidth 64) <<< 1) >>> 1 := by
    rw [u₈.gpr, u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₅.gpr, u₄.mem, u₃.mem, v₂, m₂, m₁, g₁ _ (by decide) (by decide), E.s0]; rfl
  rw [u₁₀.mem, u₉.gpr, u₉.mem, e0, e1, m₈]
  rfl

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (c : Cx) : List Region := ⟨c.W + BitVec.ofNat 64 96, 16⟩ :: absorbR c

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (c : Cx) (t t' : State) : Prop where
  pk : PK t t'
  frame : Frame (polyR c) t.mem t'.mem
  out : bytesAt t'.mem (c.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem c.N 12)
      (bytesAt t.mem c.D c.n) (bytesAt t.mem c.A c.al)

/-- The additional data, as a chunk's source. -/
theorem srcA {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Src c s c.A c.al :=
  ⟨P.a, L.al_lt, L.aw, L.a_w' (by decide), L.a_w' (by decide), L.a_w' (by decide), L.b_a⟩

/-- The data, as a chunk's source. -/
theorem srcD {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Src c s c.D c.n :=
  ⟨Covers.right P.d, L.n_lt, L.dw, L.d_w' (by decide), L.d_w' (by decide), L.d_w' (by decide), L.b_d⟩

/-- The nonce's copy misses what absorbing writes. -/
theorem absorbR_nP {c : Cx} (L : Lay c) : ∀ r ∈ absorbR c, (⟨nP c.W, 12⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.b_w' (by decide)).symm

theorem polyval_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    (hG : Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 80) = 0)
    (hN : bytesAt t.mem (nP c.W) 12 = bytesAt t.mem c.N 12) :
    WP isa polyval t (PolyPost c t) := by
  unfold polyval
  -- The additional data.
  refine WP.seq (wp_mv fun t₁ u₁ => wp_mv fun t₂ u₂ => WP.block_nil ?_)
  have pk₂ : PK t t₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (absorb_wp L (E.of_pk pk₂) L.al_lt ((srcA L E.perm).of_eq pk₂.rd pk₂.wr) L.a_w
    (by rw [u₂.other _ (by decide), u₁.gpr, E.s4]) (by rw [u₂.gpr, u₁.other _ (by decide), E.s5]))
    fun t₃ P₃ => ?_)
  rw [m₂] at P₃
  have P₃' := P₃.of_eq pk₂ m₂
  have E₃ := E.of_pk P₃'.pk
  -- The data.
  refine WP.seq (wp_mv fun t₄ u₄ => wp_mv fun t₅ u₅ => WP.block_nil ?_)
  have pk₅ : PK t₃ t₅ := (PK.ofUpd u₄).trans (PK.ofUpd u₅)
  have m₅ : t₅.mem = t₃.mem := by rw [u₅.mem, u₄.mem]
  refine WP.seq (WP.mono (absorb_wp L (E₃.of_pk pk₅) L.n_lt ((srcD L E₃.perm).of_eq pk₅.rd pk₅.wr) L.d_w
    (by rw [u₅.other _ (by decide), u₄.gpr, E₃.s6]) (by rw [u₅.gpr, u₄.other _ (by decide), E₃.s7]))
    fun t₆ P₆ => ?_)
  rw [m₅, Proof.Cmac.bytesAt_frame P₃'.frame (absorbR_buf L.d_w L.b_d) (by have := L.n_lt; omega_arith)] at P₆
  have P₃₆ := AbsPost.trans L P₃' (P₆.of_eq pk₅ m₅)
  -- The lengths.
  refine WP.seq (WP.mono (lens_wp L (E.of_pk P₃₆.pk)) fun t₇ P₇ => ?_)
  have P₃₇ := AbsPost.trans L P₃₆ P₇
  -- The tag input.
  refine WP.mono (tagIn_wp L (E.of_pk P₃₇.pk)) fun t₈ ⟨pk₈, hm₈⟩ => ⟨P₃₇.pk.trans pk₈, ?_, ?_⟩
  · refine (P₃₇.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₈]
    exact (tagInMem_frame _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega_arith
    have nN : bytesAt t₇.mem (nP c.W) 12 = bytesAt t.mem (nP c.W) 12 :=
      Proof.Cmac.bytesAt_frame P₃₇.frame (absorbR_nP L) (by decide)
    rw [hm₈, tagInMem_bytes, nN, hN, P₃₇.out, hG, hY, tagInputG, Proof.AesCcm.length_bytesAt,
      Proof.AesCcm.length_bytesAt, GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * c.al) ++ Spec.GcmSiv.le64 (8 * c.n))
        (by simp [Spec.GcmSiv.le64])]

end VG.Proof.AesGcmSiv.RISCV64
