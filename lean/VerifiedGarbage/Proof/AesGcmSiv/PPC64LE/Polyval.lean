module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Absorb
public import VerifiedGarbage.Proof.GcmSiv.Words
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
public import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp

/-!
# AES-GCM-SIV on PPC64LE: POLYVAL (`polyval`)

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/AesGcmSiv/AArch64/Polyval.lean`): `absorb` absorbs a string's whole
blocks (`Proof/AesGcmSiv/PPC64LE/Absorb.lean`) and its last bytes, padded
with zeros at `W + 240` (`absTail_wp`); `lens` absorbs the lengths block,
and `tagIn` writes the tag input at `W + 96` (`polyval_wp`): POLYVAL computed
as GHASH with the key `H · x` (`Proof.GcmSiv.Words.tagInputG`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_li wp_ld wp_std wp_lsl wp_lsr wp_lwz wp_xor)
open VG.Proof.AesCcm.PPC64LE (wp_mv wp_ldbrx)
open VG.Proof.AesGcm.PPC64LE (LoopPre LoopOut copyLoop_ok)
open VG.Proof.GcmSiv.Words (hkeyOf tagInputG)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)

/-- What absorbing a string leaves. -/
abbrev AbsPost (c : Cx) (xs : List Spec.GcmSiv.Elem) (t t' : State) : Prop := Absorbed c (absorbR c.W) xs t t'

theorem AbsPost.trans {c : Cx} (L : Lay c) {xs ys : List Spec.GcmSiv.Elem} {t t₁ t₂ : State}
    (h₁ : AbsPost c xs t t₁) (h₂ : AbsPost c ys t₁ t₂) : AbsPost c (xs ++ ys) t t₂ :=
  Absorbed.trans (absorbR_H L) h₁ h₂

/-! ## The last bytes -/

/-- The last bytes copied over a zeroed block. -/
theorem pad_bytes (m : Mem) (c : Addr) (xs : List Byte) (hx : xs.length < 16) :
    bytesAt (writeBytes (Proof.Cmac.zero2 m c) c xs) c 16 = xs ++ Spec.GcmSiv.zeros (16 - xs.length) := by
  rw [Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by omega) (by decide), Proof.Cmac.zero2_bytes]
  simp only [Spec.Cmac.zeros, Spec.GcmSiv.zeros, List.drop_replicate]

/-- The block at `W + 240` as a chunk's source. -/
theorem srcB {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Src c s (c.W + BitVec.ofNat 64 240) 16 where
  rd := P.wCR (by decide)
  lt := by decide
  wrap := by rw [L.wrapW (by decide)]; have := L.ww; omega
  y := L.w_w (.inr (by decide)) (by decide) (by decide)
  rev := L.w_w (.inl (by decide)) (by decide) (by decide)

/-- One chunk of the 16 bytes at `W + 240`: their field element absorbed. -/
theorem chunkB_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    (h23 : t.gpr .r23 = c.W + BitVec.ofNat 64 240) (h24 : t.gpr .r24 = BitVec.ofNat 64 16) :
    WP isa chunk t (Absorbed c (absR c.W) [Spec.GcmSiv.ofBytes (bytesAt t.mem (c.W + BitVec.ofNat 64 240) 16)] t) :=
  WP.mono (chunk_wp L E (m := 16) (by decide) (by decide) (srcB L E.perm) h23 h24) fun t' C => by
    have A := Absorbed.of_chunk C
    simpa [elemsAt] using A

/-- What `absTailPre` leaves: the last bytes, padded, at `W + 240`, as the
bytes to absorb. -/
structure TailPre (c : Cx) (P : Addr) (r : Nat) (t t₃ : State) : Prop where
  pk : PK t t₃
  r23 : t₃.gpr .r23 = c.W + BitVec.ofNat 64 240
  r24 : t₃.gpr .r24 = BitVec.ofNat 64 16
  frame : Frame [⟨c.W + BitVec.ofNat 64 240, 16⟩] t.mem t₃.mem
  bytes : bytesAt t₃.mem (c.W + BitVec.ofNat 64 240) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r)

/-- `absTailPre`: the last `r` (1 to 15) bytes at `P`, padded with zeros. -/
theorem absTailPre_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨c.W, 3824⟩) (h23 : t.gpr .r23 = P) (h24 : t.gpr .r24 = BitVec.ofNat 64 r) :
    WP isa absTailPre t (TailPre c P r t) := by
  have hw := L.ww
  unfold absTailPre zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun t₁ u₁ => ?_)
  refine wp_std (a := c.W + BitVec.ofNat 64 240) (by decide) (by decide) (by rw [u₁.other _ (by decide), E.r14] <;> rfl)
    (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun t₂ u₂ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun t₃ u₃ => ?_
  refine wp_mv fun t₄ u₄ => wp_addi (by decide) (by decide) fun t₅ u₅ => wp_mv fun t₆ u₆ => WP.block_nil ?_
  have pk₆ : PK t t₆ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have E₆ := E.of_pk pk₆
  have hm₆ : t₆.mem = Proof.Cmac.zero2 t.mem (c.W + BitVec.ofNat 64 240) := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem]; rfl
  have dB : (⟨P, r⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 240, r⟩ :=
    (hd.sub_right (Lay.wSub (show 240 + 16 ≤ 3824 by decide))).sub_right (Region.sub_prefix (by omega))
  have lp : LoopPre t₆ P (c.W + BitVec.ofNat 64 240) r :=
    { r3 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), h23]
      r4 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), E.r14] <;> rfl
      r5 := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr,
          u₁.other _ (by decide), h24]
      pos := hr1
      lt := by omega
      rd := by rw [pk₆.rd, pk₆.wr]; exact hc
      wr := VG.Proof.Gather.PPC64LE.covers_prefix (E₆.perm.wC (show 240 + 16 ≤ 3824 by decide)) (by omega)
      disj := dB }
  refine WP.seq (WP.mono (copyLoop_ok t₆ lp) fun t₇ ⟨hm₇, O⟩ => ?_)
  have pk₇ : PK t₆ t₇ := PK.ofLoop O
  -- The data is outside the zeroed block.
  have hd₆ : bytesAt t₆.mem P r = bytesAt t.mem P r := by
    rw [hm₆]
    exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _)
      (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hd.sub_right (Lay.wSub (by decide)))
      (by omega)
  have hb₇ : bytesAt t₇.mem (c.W + BitVec.ofNat 64 240) 16 = bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r) := by
    have hl := Proof.AesCcm.length_bytesAt t.mem P r
    rw [hm₇, hd₆, hm₆, pad_bytes _ _ _ (by omega), hl]
  have f₇ : Frame [⟨c.W + BitVec.ofNat 64 240, 16⟩] t.mem t₇.mem := by
    rw [hm₇, hm₆]
    exact (Proof.Cmac.frame_store2 _ _ _).trans
      ((VG.WriteBytes.writeBytes_frame _ _ _ (by
        rw [Proof.AesCcm.length_bytesAt]; exact Region.contains_self _ _)).sub fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
  refine wp_addi (by decide) (by decide) fun t₈ u₈ => wp_li (by decide) fun t₉ u₉ => WP.block_nil
    ⟨pk₆.trans (pk₇.trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))), ?_, u₉.gpr, by rw [u₉.mem, u₈.mem]; exact f₇,
      by rw [u₉.mem, u₈.mem]; exact hb₇⟩
  rw [u₉.other _ (by decide), u₈.gpr, (E₆.of_pk pk₇).r14] <;> rfl

/-- `absTail`: the last `r` (1 to 15) bytes at `P`, padded with zeros, absorbed. -/
theorem absTail_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {P : Addr} {r : Nat}
    (hr1 : 1 ≤ r) (hr : r < 16) (hc : Covers [⟨P, r⟩] (t.rd ++ t.wr))
    (hd : (⟨P, r⟩ : Region).Disjoint ⟨c.W, 3824⟩) (h23 : t.gpr .r23 = P) (h24 : t.gpr .r24 = BitVec.ofNat 64 r) :
    WP isa absTail t (AbsPost c [Spec.GcmSiv.ofBytes (bytesAt t.mem P r ++ Spec.GcmSiv.zeros (16 - r))] t) := by
  have hw := L.ww
  unfold absTail
  refine WP.seq (WP.mono (absTailPre_wp L E hr1 hr hc hd h23 h24) fun t₃ T => ?_)
  refine WP.mono (chunkB_wp L (E.of_pk T.pk) T.r23 T.r24) fun t₄ C => ?_
  rw [T.bytes] at C
  have dHY : ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 240, 16⟩ : Region)], ∀ d, d + 16 ≤ 240 →
      (⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun q hq d hd => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
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
  rw [show 16 * (n / 16) + n % 16 = n by omega] at hs
  have hl := Proof.AesCcm.length_bytesAt m Q (16 * (n / 16))
  rw [GcmSiv.elems_pad16, Proof.AesCcm.length_bytesAt, hs, List.take_left' hl, List.drop_left' hl,
    GcmSiv.elems_bytesAt]

/-- The whole blocks of `absorb`, once `r11` holds their number. -/
theorem absMid_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat}
    (hm : m < 2 ^ 64) (hQ : Src c t Q m) (h23 : t.gpr .r23 = Q) (h24 : t.gpr .r24 = BitVec.ofNat 64 m)
    (h11 : t.gpr .r11 = BitVec.ofNat 64 (m / 16)) :
    WP isa (.ite (.zero .d .r11) (.block []) (.loop chunk (.nonzero .d .r11))) t fun t₂ =>
      Absorbed c (absR c.W) (elemsAt t.mem Q (m / 16)) t t₂ ∧
        t₂.gpr .r23 = Q + BitVec.ofNat 64 (16 * (m / 16)) ∧ t₂.gpr .r24 = BitVec.ofNat 64 (m % 16) := by
  refine WP.ite (decide (m / 16 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero h11 (by omega)) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : m / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨⟨PK.refl _, Frame.refl _ _, by simp [h0, elemsAt, Proof.Gcm.ghashFrom_nil]⟩,
      by rw [h23, h0, Nat.mul_zero, BitVec.add_zero], by rw [h24]; congr 1; omega⟩
  · have h0 : m / 16 ≠ 0 := by simpa using hf
    exact chunks_wp L E hm (by omega) (hQ.take (by omega)) h23 h24

theorem absorb_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {Q : Addr} {m : Nat} (hm : m < 2 ^ 64)
    (hQ : Src c t Q m) (hd : (⟨Q, m⟩ : Region).Disjoint ⟨c.W, 3824⟩) (h23 : t.gpr .r23 = Q)
    (h24 : t.gpr .r24 = BitVec.ofNat 64 m) :
    WP isa absorb t (AbsPost c (Spec.GcmSiv.elems (Spec.GcmSiv.pad16 (bytesAt t.mem Q m))) t) := by
  unfold absorb wholeLeft
  refine WP.seq (wp_lsr (by decide) fun t₁ u₁ => WP.block_nil ?_)
  have pk₁ : PK t t₁ := PK.ofUpd u₁
  refine WP.seq (WP.mono (absMid_wp L (E.of_pk pk₁) hm (hQ.of_eq pk₁.rd pk₁.wr)
    (by rw [u₁.other _ (by decide), h23]) (by rw [u₁.other _ (by decide), h24])
    (by rw [u₁.gpr, h24, ofNat_lsr 4 hm])) fun t₂ ⟨P₂, r23₂, r24₂⟩ => ?_)
  rw [u₁.mem] at P₂
  have P₂' := P₂.of_eq pk₁ u₁.mem
  rw [elems_pad16_bytesAt]
  refine WP.ite (decide (m % 16 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero r24₂ (by omega)) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : m % 16 = 0 := by simpa using ht
    simp only [h0, ite_true, List.append_nil]
    exact WP.block_nil (P₂'.sub (absR_sub c.W))
  · have h0 : m % 16 ≠ 0 := by simpa using hf
    simp only [h0, ite_false]
    have hs := hQ.slice (a := 16 * (m / 16)) (k := m % 16) (by omega) (by omega)
    have dT : (⟨Q + BitVec.ofNat 64 (16 * (m / 16)), m % 16⟩ : Region).Disjoint ⟨c.W, 3824⟩ :=
      hd.sub_left (Offset.sub_base Q (by omega))
    refine WP.mono (absTail_wp L (E.of_pk P₂'.pk) (by omega) (by omega)
      (by rw [P₂'.pk.rd, P₂'.pk.wr]; exact hs.rd) dT r23₂ r24₂) fun t₃ T => ?_
    have e := Proof.Cmac.bytesAt_frame P₂'.frame (fun r hr => dT.sub_right ?_) (by omega)
    · rw [e] at T
      exact AbsPost.trans L (P₂'.sub (absR_sub c.W)) T
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

/-! ## The lengths, and the tag input -/

/-- `lensBlock`: the lengths block at `W + 240`, as the bytes to absorb. -/
theorem lensBlk_wp {c : Cx} {t : State} (E : Env c t) :
    WP isa (.block lensBlock) t fun t₆ => PK t t₆ ∧ t₆.mem =
      (t.mem.writeW (c.W + BitVec.ofNat 64 240) (BitVec.ofNat 64 (8 * c.al))).writeW
        (c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (BitVec.ofNat 64 (8 * c.n)) ∧
      t₆.gpr .r23 = c.W + BitVec.ofNat 64 240 ∧ t₆.gpr .r24 = BitVec.ofNat 64 16 := by
  unfold lensBlock
  refine wp_lsl (by decide) fun t₁ u₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 240) (by decide) (by decide) (by rw [u₁.other _ (by decide), E.r14] <;> rfl)
    (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun t₂ u₂ => ?_
  refine wp_lsl (by decide) fun t₃ u₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₃.wr, u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun t₄ u₄ => ?_
  refine wp_addi (by decide) (by decide) fun t₅ u₅ => wp_li (by decide) fun t₆ u₆ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆))))), ?_, ?_, u₆.gpr⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.other .r21 (by decide), u₁.mem,
      E.r19, E.r21, ofNat_shl, ofNat_shl]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      E.r14] <;> rfl

/-- `lensBlock` and its chunk: the lengths block absorbed. -/
theorem lens_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    WP isa lens t (AbsPost c [Spec.GcmSiv.ofBytes (Spec.GcmSiv.le64 (8 * c.al) ++ Spec.GcmSiv.le64 (8 * c.n))] t) := by
  unfold lens
  refine WP.seq (WP.mono (lensBlk_wp E) fun t₆ ⟨pk₆, hm₆, r23₆, r24₆⟩ => ?_)
  have f₆ : Frame [⟨c.W + BitVec.ofNat 64 240, 16⟩] t.mem t₆.mem := by rw [hm₆]; exact Proof.Cmac.frame_store2 _ _ _
  refine WP.mono (chunkB_wp L (E.of_pk pk₆) r23₆ r24₆) fun t₇ C => ?_
  have hb : bytesAt t₆.mem (c.W + BitVec.ofNat 64 240) 16 =
      Spec.GcmSiv.le64 (8 * c.al) ++ Spec.GcmSiv.le64 (8 * c.n) := by
    rw [hm₆, Proof.Cmac.bytesAt_store2, GcmSiv.le64_le8, GcmSiv.le64_le8]
  rw [hb] at C
  have dHY : ∀ d, d + 16 ≤ 240 → ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 240, 16⟩ : Region)],
      (⟨c.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint q := fun d hd q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inl hd) (by omega) (by decide)
  refine ⟨pk₆.trans C.pk,
    (f₆.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).trans
      (C.frame.mono fun q hq => List.mem_cons_of_mem _ hq), ?_⟩
  rw [C.out, blockAt_frame f₆ (dHY 64 (by decide)), blockAt_frame f₆ (dHY 80 (by decide))]

/-- The memory `tagIn` leaves. -/
def tagInMem (m : Mem) (W N : Addr) : Mem :=
  let lo := rev64 (m.readW (W + BitVec.ofNat 64 88) 64) ^^^ m.readW (N + BitVec.ofNat 64 0) 64
  let hi := ((rev64 (m.readW (W + BitVec.ofNat 64 80) 64) ^^^ (m.readW (N + BitVec.ofNat 64 8) 32).setWidth 64)
    <<< 1) >>> 1
  (m.writeW (W + BitVec.ofNat 64 96) lo).writeW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) hi

theorem tagInMem_bytes (m : Mem) (W N : Addr) :
    bytesAt (tagInMem m W N) (W + BitVec.ofNat 64 96) 16 =
      GcmSiv.tagOf (Spec.GcmSiv.toBytes (Spec.Gcm.blockAt m (W + BitVec.ofNat 64 80))) (bytesAt m N 12) := by
  rw [tagInMem, Proof.Cmac.bytesAt_store2, ← Proof.Gcm.PPC64LE.blockAt_rev, BitVec.add_zero, BitVec.add_zero,
    Offset.add_add, GcmSiv.toBytes_append, show (12 : Nat) = 8 + 4 from rfl, Proof.Cmac.bytesAt_add,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le4_readW, GcmSiv.tagOf_words, GcmSiv.Words.shl_shr_one]

theorem tagInMem_frame (m : Mem) (W N : Addr) : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] m (tagInMem m W N) :=
  Proof.Cmac.frame_store2 _ _ _

theorem tagIn_wp {c : Cx} {t : State} (E : Env c t) :
    WP isa (.block tagIn) t fun t' => PK t t' ∧ t'.mem = tagInMem t.mem c.W c.N := by
  unfold tagIn
  refine wp_li (by decide) fun t₁ u₁ => ?_
  refine wp_ldbrx (ea := c.W + BitVec.ofNat 64 88) (by decide) (by rw [u₁.other _ (by decide), u₁.gpr, E.r14] <;> rfl)
    (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun t₂ u₂ => ?_
  refine wp_li (by decide) fun t₃ u₃ => ?_
  refine wp_ldbrx (ea := c.W + BitVec.ofNat 64 80) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₃.gpr, E.r14] <;> rfl)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun t₄ u₄ => ?_
  have g₄ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r9 → t₄.gpr r = t.gpr r := fun r h3 h4 h9 => by
    rw [u₄.other _ h4, u₃.other _ h9, u₂.other _ h3, u₁.other _ h9]
  have rd₄ : t₄.rd ++ t₄.wr = t.rd ++ t.wr := by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine wp_ld (a := c.N + BitVec.ofNat 64 0) (by decide) (by decide)
    (by rw [g₄ _ (by decide) (by decide) (by decide), E.r15]) (by rw [rd₄]; exact E.perm.nR (by decide))
    fun t₅ u₅ => wp_xor fun t₆ u₆ => ?_
  refine wp_lwz (a := c.N + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄ _ (by decide) (by decide) (by decide), E.r15])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, rd₄]; exact E.perm.nR (by decide)) fun t₇ u₇ => ?_
  refine wp_xor fun t₈ u₈ => wp_lsl (by decide) fun t₉ u₉ => wp_lsr (by decide) fun t₁₀ u₁₀ => ?_
  have g₁₀ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r9 → t₁₀.gpr r = t.gpr r := fun r h3 h4 h5 h9 => by
    rw [u₁₀.other _ h4, u₉.other _ h4, u₈.other _ h4, u₇.other _ h5, u₆.other _ h3, u₅.other _ h5,
      g₄ _ h3 h4 h9]
  have wr₁₀ : t₁₀.wr = t.wr := by
    rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_std (a := c.W + BitVec.ofNat 64 96) (by decide) (by decide)
    (by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), E.r14] <;> rfl)
    (by rw [wr₁₀]; exact E.perm.wW (by decide)) fun t₁₁ u₁₁ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₁₁.gpr, g₁₀ _ (by decide) (by decide) (by decide) (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₁₁.wr, wr₁₀, Offset.add_add]; exact E.perm.wW (by decide)) fun t₁₂ u₁₂ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans ((PK.ofMupd u₁₁).trans (PK.ofMupd u₁₂))))))))))), ?_⟩
  have m₁₀ : t₁₀.mem = t.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have e3 : t₁₀.gpr .r3 = rev64 (t.mem.readW (c.W + BitVec.ofNat 64 88) 64) ^^^ t.mem.readW (c.N + BitVec.ofNat 64 0) 64 := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr,
      u₅.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have e4 : t₁₀.gpr .r4 = ((rev64 (t.mem.readW (c.W + BitVec.ofNat 64 80) 64) ^^^
      (t.mem.readW (c.N + BitVec.ofNat 64 8) 32).setWidth 64) <<< 1) >>> 1 := by
    rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rw [u₁₂.mem, u₁₁.gpr, u₁₁.mem, e3, e4, m₁₀]
  rfl

/-! ## `polyval` -/

/-- What `polyval` writes: what absorbing writes, and the tag input at `W + 96`. -/
abbrev polyR (W : Addr) : List Region := ⟨W + BitVec.ofNat 64 96, 16⟩ :: absorbR W

/-- What `polyval` leaves, from `t`. -/
structure PolyPost (c : Cx) (t t' : State) : Prop where
  pk : PK t t'
  frame : Frame (polyR c.W) t.mem t'.mem
  out : bytesAt t'.mem (c.W + BitVec.ofNat 64 96) 16 =
    tagInputG (bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16) (bytesAt t.mem c.N 12)
      (bytesAt t.mem c.D c.n) (bytesAt t.mem c.A c.al)

/-- The additional data, as a chunk's source. -/
theorem srcA {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Src c s c.A c.al :=
  ⟨P.a, L.al_lt, L.aw, L.a_w' (by decide), L.a_w' (by decide)⟩

/-- The data, as a chunk's source. -/
theorem srcD {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Src c s c.D c.n :=
  ⟨Covers.right P.d, L.n_lt, L.dw, L.d_w' (by decide), L.d_w' (by decide)⟩

theorem polyval_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    (hG : Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 64) =
      hkeyOf (Spec.GcmSiv.ofBytes (bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16)))
    (hY : Spec.Gcm.blockAt t.mem (c.W + BitVec.ofNat 64 80) = 0) :
    WP isa polyval t (PolyPost c t) := by
  unfold polyval
  -- The additional data.
  refine WP.seq (wp_mv fun t₁ u₁ => wp_mv fun t₂ u₂ => WP.block_nil ?_)
  have pk₂ : PK t t₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (absorb_wp L (E.of_pk pk₂) L.al_lt ((srcA L E.perm).of_eq pk₂.rd pk₂.wr) L.a_w
    (by rw [u₂.other _ (by decide), u₁.gpr, E.r18]) (by rw [u₂.gpr, u₁.other _ (by decide), E.r19]))
    fun t₃ P₃ => ?_)
  rw [m₂] at P₃
  have P₃' := P₃.of_eq pk₂ m₂
  have E₃ := E.of_pk P₃'.pk
  -- The data.
  refine WP.seq (wp_mv fun t₄ u₄ => wp_mv fun t₅ u₅ => WP.block_nil ?_)
  have pk₅ : PK t₃ t₅ := (PK.ofUpd u₄).trans (PK.ofUpd u₅)
  have m₅ : t₅.mem = t₃.mem := by rw [u₅.mem, u₄.mem]
  refine WP.seq (WP.mono (absorb_wp L (E₃.of_pk pk₅) L.n_lt ((srcD L E₃.perm).of_eq pk₅.rd pk₅.wr) L.d_w
    (by rw [u₅.other _ (by decide), u₄.gpr, E₃.r20]) (by rw [u₅.gpr, u₄.other _ (by decide), E₃.r21]))
    fun t₆ P₆ => ?_)
  rw [m₅, Proof.Cmac.bytesAt_frame P₃'.frame (absorbR_buf L.d_w) (by have := L.n_lt; omega)] at P₆
  have P₃₆ := AbsPost.trans L P₃' (P₆.of_eq pk₅ m₅)
  -- The lengths.
  refine WP.seq (WP.mono (lens_wp L (E.of_pk P₃₆.pk)) fun t₇ P₇ => ?_)
  have P₃₇ := AbsPost.trans L P₃₆ P₇
  -- The tag input.
  refine WP.mono (tagIn_wp (E.of_pk P₃₇.pk)) fun t₈ ⟨pk₈, hm₈⟩ => ⟨P₃₇.pk.trans pk₈, ?_, ?_⟩
  · refine (P₃₇.frame.mono fun q hq => List.mem_cons_of_mem _ hq).trans ?_
    rw [hm₈]
    exact (tagInMem_frame _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self
  · have hp : ∀ xs ys : List Byte, (Spec.GcmSiv.pad16 xs ++ Spec.GcmSiv.pad16 ys).length % 16 = 0 := fun xs ys => by
      rw [List.length_append]; have := GcmSiv.pad16_mod xs; have := GcmSiv.pad16_mod ys; omega
    have nN : bytesAt t₇.mem c.N 12 = bytesAt t.mem c.N 12 :=
      Proof.Cmac.bytesAt_frame P₃₇.frame (absorbR_buf L.n_w) (by decide)
    rw [hm₈, tagInMem_bytes, nN, P₃₇.out, hG, hY, tagInputG, Proof.AesCcm.length_bytesAt,
      Proof.AesCcm.length_bytesAt, GcmSiv.elems_append (hp _ _), GcmSiv.elems_append (GcmSiv.pad16_mod _),
      GcmSiv.elems_single (bs := Spec.GcmSiv.le64 (8 * c.al) ++ Spec.GcmSiv.le64 (8 * c.n))
        (by simp [Spec.GcmSiv.le64])]

end VG.Proof.AesGcmSiv.PPC64LE
