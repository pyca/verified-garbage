module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
public import VerifiedGarbage.Proof.GcmSiv.Spec
public import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE

/-!
# AES-GCM-SIV on PPC64LE: a block encrypted (`tag`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcmSiv/Arm/Tag.lean`): `tag o` copies the block at `W + 96` to
`W + 112` and zeroes the 16 bytes at `W + o`, on which `vg_aes_ctr32` leaves
the encryption of the block with the encryption key (`tag_wp`): the tag, or a
keystream block.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_li wp_ld wp_std)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Proof.AesGcm.PPC64LE (CtrCall CtrPost ctr_call)
open VG.Spec.Aes (bytesAt)

/-- The memory after the copy of the counter block. -/
def copyMem (m : Mem) (W : Addr) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 112) (m.readW (W + BitVec.ofNat 64 96) 64)).writeW
    (W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8) (m.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64)

theorem copyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] m (copyMem m W) :=
  Proof.Cmac.frame_store2 _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) :
    bytesAt (copyMem m W) (W + BitVec.ofNat 64 112) 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [copyMem, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, Proof.Cmac.bytesAt_split]

/-- What `tag o` writes. -/
abbrev tagR (W : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 o, 16⟩, ⟨W + BitVec.ofNat 64 1776, 2048⟩]

/-- What `tag o` leaves, from `t`. -/
structure TagPost (c : Cx) (o : Nat) (t t' : State) : Prop where
  pk : PK t t'
  r23 : t'.gpr .r23 = t.gpr .r23
  r24 : t'.gpr .r24 = t.gpr .r24
  r25 : t'.gpr .r25 = t.gpr .r25
  frame : Frame (tagR c.W o) t.mem t'.mem
  out : bytesAt t'.mem (c.W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R (bytesAt t.mem (c.W + BitVec.ofNat 64 96) 16)

/-- The block of `tag o`: the arguments of its call. -/
theorem tagArgs_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {o : Nat} (ho : o = 0 ∨ o = 240) :
    WP isa (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ ([.addi .r6 .r14 o, .li .r7 1] : List Instr))) t
      fun t₁₃ => PK t t₁₃ ∧ t₁₃.mem = Proof.Cmac.zero2 (copyMem t.mem c.W) (c.W + BitVec.ofNat 64 o) ∧
        CtrCall t₁₃ (c.W + BitVec.ofNat 64 256) (c.W + BitVec.ofNat 64 112) (c.W + BitVec.ofNat 64 o)
          (c.W + BitVec.ofNat 64 1776) c.R 1 ∧ ∀ r ∈ [Reg.r23, .r24, .r25], t₁₃.gpr r = t.gpr r := by
  have hw := L.ww
  have o₁ : o + 16 ≤ 256 := by omega
  unfold copy16 zero16 ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_ld (a := c.W + BitVec.ofNat 64 96) (by decide) (by decide) (by rw [E.r14] <;> rfl)
    (E.perm.wR (by decide)) fun t₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₁.other _ (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by decide)) fun t₂ u₂ => ?_
  have g₂ : ∀ r, r ≠ .r3 → r ≠ .r4 → t₂.gpr r = t.gpr r := fun r h3 h4 => by rw [u₂.other _ h4, u₁.other _ h3]
  have wr₂ : t₂.wr = t.wr := by rw [u₂.wr, u₁.wr]
  refine wp_std (a := c.W + BitVec.ofNat 64 112) (by decide) (by decide)
    (by rw [g₂ _ (by decide) (by decide), E.r14] <;> rfl) (by rw [wr₂]; exact E.perm.wW (by decide)) fun t₃ u₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.gpr, g₂ _ (by decide) (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₃.wr, wr₂, Offset.add_add]; exact E.perm.wW (by decide)) fun t₄ u₄ => ?_
  refine wp_li (by decide) fun t₅ u₅ => ?_
  have w14 : t₅.gpr .r14 = c.W := by rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, g₂ _ (by decide) (by decide), E.r14]
  have wr₅ : t₅.wr = t.wr := by rw [u₅.wr, u₄.wr, u₃.wr, wr₂]
  refine wp_std (a := c.W + BitVec.ofNat 64 o) (by decide) (by rcases ho with rfl | rfl <;> decide) (by rw [w14])
    (by rw [wr₅]; exact E.perm.wW (by omega)) fun t₆ u₆ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 o + BitVec.ofNat 64 8) (by decide)
    (by rcases ho with rfl | rfl <;> decide) (by rw [u₆.gpr, w14, Offset.add_add])
    (by rw [u₆.wr, wr₅, Offset.add_add]; exact E.perm.wW (by omega)) fun t₇ u₇ => ?_
  refine wp_addi (by decide) (by decide) fun t₈ u₈ => wp_mv fun t₉ u₉ => wp_addi (by decide) (by decide) fun t₁₀ u₁₀ =>
    wp_addi (by decide) (by decide) fun t₁₁ u₁₁ => wp_addi (by decide) (by rcases ho with rfl | rfl <;> decide)
    fun t₁₂ u₁₂ => wp_li (by decide) fun t₁₃ u₁₃ => WP.block_nil ?_
  have pk : PK t t₁₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofMupd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans
    ((PK.ofUpd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans (PK.ofUpd u₁₃))))))))))))
  have E₁₃ := E.of_pk pk
  have pk₈ : PK t t₈ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofMupd u₇).trans (PK.ofUpd u₈)))))))
  have w14' : t₇.gpr .r14 = c.W := by rw [u₇.gpr, u₆.gpr, w14]
  have hm : t₁₃.mem = Proof.Cmac.zero2 (copyMem t.mem c.W) (c.W + BitVec.ofNat 64 o) := by
    rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, u₄.mem,
      u₃.gpr, u₃.mem, u₂.gpr, u₂.other .r3 (by decide), u₁.gpr, u₂.mem, u₁.mem]
    rfl
  have dO : (⟨c.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  refine ⟨pk, hm, ?_, fun r hr => ?_⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
      u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr,
      g₂ _ (by decide) (by decide)]
  exact cargs L E₁₃ (E₁₃.perm.wCR (by decide)) (L.w_w (.inr (by decide)) (by decide) (by decide))
      (L.w_w (.inl (by decide)) (by decide) (by decide)) (L.w_w (.inr (by omega)) (by decide) (by omega)) dO.symm
      (L.w_w (.inl (by omega)) (by omega) (by decide)) (E₁₃.perm.wC (by omega))
      (by rw [L.wrapW (by omega)]; omega) (by decide)
      (by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
        u₉.other _ (by decide), u₈.gpr, w14'] <;> rfl)
      (by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
        u₉.gpr, (E.of_pk pk₈).r17])
      (by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
        u₉.other _ (by decide), u₈.other _ (by decide), w14'] <;> rfl)
      (by rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide),
        u₉.other _ (by decide), u₈.other _ (by decide), w14'])
      u₁₃.gpr
      (by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
        u₉.other _ (by decide), u₈.other _ (by decide), w14'] <;> rfl)

theorem tag_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {o : Nat} (ho : o = 0 ∨ o = 240) :
    WP isa (tag o) t (TagPost c o t) := by
  have hw := L.ww
  have o₁ : o + 16 ≤ 256 := by omega
  unfold tag
  refine WP.seq (WP.mono (tagArgs_wp L E ho) fun t₁₃ ⟨pk, hm, cc, reg₁⟩ => ?_)
  have dO : (⟨c.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 112, 16⟩ :=
    L.w_w (by omega) (by omega) (by decide)
  have fZ := Proof.Cmac.frame_store2 (m := copyMem t.mem c.W) (c.W + BitVec.ofNat 64 o) 0 0
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 112, 16⟩, ⟨c.W + BitVec.ofNat 64 o, 16⟩] t.mem t₁₃.mem := by
    rw [hm, Proof.Cmac.zero2]
    exact ((copyMem_frame _ _).mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      (fZ.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp)
  have hb₁ : bytesAt t₁₃.mem (c.W + BitVec.ofNat 64 112) 16 = bytesAt t.mem (c.W + BitVec.ofNat 64 96) 16 := by
    rw [hm, Proof.Cmac.zero2, Proof.Cmac.bytesAt_frame16 fZ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm), copyMem_bytes]
  have hz₁ : Spec.Gcm.blockAt t₁₃.mem (c.W + BitVec.ofNat 64 o) = 0 := by
    rw [hm, Spec.Gcm.blockAt, Proof.Cmac.zero2_bytes]; decide
  have ek₁ : Spec.GcmSiv.ctxCiph t₁₃.mem (c.W + BitVec.ofNat 64 256) c.R =
      Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.Cmac.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rb)
      · exact (L.w_w (.inr (by omega)) (by decide) (by omega)).sub_left (Region.sub_prefix L.rb))
      (by have := L.rb; omega)]
  refine WP.mono (ctr_call cc) fun t₁₄ P => ?_
  have reg : ∀ r, r ∈ [Reg.r23, .r24, .r25] → t₁₄.gpr r = t.gpr r := fun r hr => by
    rw [P.saved r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;>
      decide), reg₁ r hr]
  refine ⟨pk.trans (PK.ofSaved P.rd P.wr P.sp P.saved), reg _ (by simp), reg _ (by simp), reg _ (by simp),
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (P.frame.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Nat.mul_one] at hq
      rcases hq with rfl | rfl | rfl <;> simp), ?_⟩
  have hout := P.out
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith c.R (bytesAt t₁₃.mem (c.W + BitVec.ofNat 64 256) (16 * (c.R + 1))) =
      Spec.GcmSiv.ctxCiph t₁₃.mem (c.W + BitVec.ofNat 64 256) c.R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.PPC64LE
