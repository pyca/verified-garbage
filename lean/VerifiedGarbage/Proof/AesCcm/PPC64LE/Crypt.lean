module

public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Chunk
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesCcm.PPC64LE.B0
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Callee
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Header
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.CmacAes.Stream.PPC64LE.Common
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-CCM on PPC64LE: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data in chunks (`ctrHead_wp`, by `chunk_wp`), then its last
`n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which `vg_aes_ctr32` writes over a
zero block (`tail_wp`): the data XORed with CCM's keystream from `Ctr₁`
(`ctr_wp`), which is its encryption (`Proof.AesCcm.crypt_eq`), as on
AArch64.
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_li wp_lsr wp_and wp_std)
open VG.Proof.AesCtr.PPC64LE (ctr_call)
open VG.Proof.Gather.PPC64LE (eval_zero eval_nonzero)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (xorFrom xorFrom_append ctr32_ccm length_bytesAt bytesAt_prefix bytesAt_suffix
  BlockCipher xorFrom_zeros xorFrom_tail)

/-- The whole blocks, in chunks. -/
theorem ctrHead_wp {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} (E : Env c s)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    WP isa (.seq (.block [Impl.AesCbc.PPC64LE.mov .r18 .r22, .lsr .d .r19 .r23 4, .li .r20 1])
      (.ite (.zero .d .r19) (.block []) (.loop ctrChunk (.nonzero .d .r19)))) s
      (CtrInv c nonce s (c.n / 16)) := by
  have hn64 := L.n_lt
  refine WP.seq (wp_mv fun s₁ u₁ => wp_lsr (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
    WP.block_nil ?_)
  have I₀ : CtrInv c nonce s 0 s₃ :=
    { pk := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
      r18 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.r22]; exact (BitVec.add_zero _).symm
      r19 := by
        rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r23,
          VG.Proof.CmacAes.Stream.PPC64LE.shr_ofNat hn64]; rfl
      r20 := u₃.gpr
      le := Nat.zero_le _
      frame := by rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _
      done := rfl
      rest := by rw [u₃.mem, u₂.mem, u₁.mem] }
  refine WP.ite (decide (c.n / 16 = 0)) (eval_zero (a := c.n / 16) (by rw [I₀.r19, Nat.sub_zero]) (by omega_arith))
    (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n / 16 = 0 := of_decide_eq_true ht
    exact WP.block_nil (by rw [h0]; exact I₀)
  · have h0 : c.n / 16 ≠ 0 := of_decide_eq_false hf
    refine WP.loop (M := isa) (fun m t => ∃ b, m = c.n / 16 - b ∧ b < c.n / 16 ∧ CtrInv c nonce s b t) ?_
      (c.n / 16 - 0) s₃ ⟨0, rfl, by omega_arith, I₀⟩
    rintro m t ⟨b, rfl, hb, I⟩
    refine WP.mono (chunk_wp L hnl E hc0 I hb) fun t' ⟨k, _, hk1, hkb, I'⟩ => ?_
    have ev := eval_nonzero (r := .r19) (a := c.n / 16 - (b + k)) I'.r19 (by omega_arith)
    by_cases he : b + k = c.n / 16
    · left; exact ⟨by rw [ev]; simp [he], by rw [← he]; exact I'⟩
    · right; exact ⟨by rw [ev]; simp; omega_arith, c.n / 16 - (b + k), by omega_arith, b + k, rfl, by omega_arith, I'⟩

/-- The last `n mod 16` (not 0) bytes, XORed with `CIPH_K(Ctr₁₊ₙ/₁₆)`. -/
theorem tail_wp {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} (E : Env c s)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {t : State}
    (I : CtrInv c nonce s (c.n / 16) t) (h21 : t.gpr .r21 = BitVec.ofNat 64 (c.n % 16)) (h0 : c.n % 16 ≠ 0) :
    WP isa ctrTail t fun t' => PK s t' ∧ Frame (crR c) s.mem t'.mem ∧
      bytesAt t'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  have Et := E.of_pk I.pk
  have hc0t : bytesAt t.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [Proof.Cmac.bytesAt_frame I.frame (crR_disj L (.inl (by decide))) (by decide), hc0]
  have hi : 1 + c.n / 16 < 256 ^ (15 - c.nl) := by have := L.hn; omega_arith
  unfold ctrTail
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_mv fun t₁ u₁ => ?_)
  refine ctrAt_wp L (Et.of_pk (PK.ofUpd u₁)) hnl (by rw [u₁.mem]; exact hc0t) hi
    (by rw [u₁.gpr, I.r20]) fun t₂ pk₂ kp₂ f₂ hc₂ => ?_
  unfold zero16 ctrArgs
  simp only [List.cons_append, List.nil_append]
  have pk₂' : PK s t₂ := I.pk.trans ((PK.ofUpd u₁).trans pk₂)
  refine wp_li (by decide) fun t₃ u₃ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 80) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), pk₂'.gpr .r14 (by decide), E.r14]; rfl)
    (by rw [u₃.wr, pk₂'.wr]; exact E.perm.wW (by decide)) fun t₄ u₄ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₄.gpr, u₃.other _ (by decide), pk₂'.gpr .r14 (by decide), E.r14, Offset.add_add]; rfl)
    (by rw [u₄.wr, u₃.wr, pk₂'.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun t₅ u₅ => ?_
  refine wp_mv fun t₆ u₆ => wp_mv fun t₇ u₇ => wp_addi (by decide) (by decide) fun t₈ u₈ =>
    wp_addi (by decide) (by decide) fun t₉ u₉ => wp_addi (by decide) (by decide) fun t₁₀ u₁₀ =>
    wp_li (by decide) fun t₁₁ u₁₁ => WP.block_nil ?_
  have pk₁₁ : PK t₂ t₁₁ := (PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans ((PK.ofMupd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans (PK.ofUpd u₁₁))))))))
  have E₁₁ := E.of_pk (pk₂'.trans pk₁₁)
  have m₁₁ : t₁₁.mem = (t₂.mem.writeW (c.W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₃.gpr]; rfl
  have r_ : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r8 → r ≠ .r6 → r ≠ .r7 → t₁₁.gpr r = t₂.gpr r :=
    fun r h0 h3 h4 h5 h8 h6 h7 => by
      rw [u₁₁.other _ h7, u₁₀.other _ h6, u₉.other _ h8, u₈.other _ h5, u₇.other _ h4, u₆.other _ h3, u₅.gpr,
        u₄.gpr, u₃.other _ h0]
  have C := cargsW L E₁₁ (o := 64) (d := 80) (by decide) (by decide) (by decide)
    (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide), pk₂'.gpr .r16 (by decide), E.r16])
    (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), pk₂'.gpr .r17 (by decide), E.r17])
    (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      pk₂'.gpr .r14 (by decide), E.r14]; rfl)
    (by rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      pk₂'.gpr .r14 (by decide), E.r14]; rfl)
    (by rw [u₁₁.gpr])
    (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      pk₂'.gpr .r14 (by decide), E.r14]; rfl)
  refine WP.seq (WP.mono (ctr_call C) fun t₁₂ h => ?_)
  have sv : ∀ r ∈ [Reg.r18, .r21], t₁₂.gpr r = t.gpr r := fun r hr => by
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [h.saved _ hp, r_ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        kp₂ _ (by simp), u₁.other _ (by decide)]
  refine WP.seq (wp_addi (by decide) (by decide) fun t₁₃ u₁₃ => wp_mv fun t₁₄ u₁₄ => wp_mv fun t₁₅ u₁₅ =>
    WP.block_nil ?_)
  have pk₁₅ : PK s t₁₅ := pk₂'.trans (pk₁₁.trans ((PK.ofSaved h.rd h.wr h.sp h.saved).trans ((PK.ofUpd u₁₃).trans
    ((PK.ofUpd u₁₄).trans (PK.ofUpd u₁₅)))))
  have E₁₅ := E.of_pk pk₁₅
  have m₁₅ : t₁₅.mem = t₁₂.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem]
  have hS := (L.bufD E₁₅.perm).drop (k := 16 * (c.n / 16)) (by omega_arith)
  rw [show c.n - 16 * (c.n / 16) = c.n % 16 by omega_arith] at hS
  have xp : XorPre t₁₅ (c.W + BitVec.ofNat 64 80) (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) :=
    { r3 := by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, h.saved .r14 (by decide),
        (pk₁₁).gpr .r14 (by decide), pk₂'.gpr .r14 (by decide), E.r14]; rfl
      r9 := by rw [u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide), sv .r18 (by simp), I.r18]
      r4 := by rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), sv .r21 (by simp), h21]
      pos := by omega_arith
      lt := by omega_arith
      rd := E₁₅.perm.wCR (by omega_arith)
      wr := VG.Proof.Gather.PPC64LE.covers_off E₁₅.perm.d (by omega_arith) hn64
      disj := (hS.wd (by omega_arith)).symm }
  refine WP.mono (xorBytes_wp t₁₅ xp) fun t₁₆ ⟨hm₁₆, _, k₁₆⟩ => ?_
  -- What the tail wrote in `W`.
  have s64 : Region.Sub ⟨c.W + BitVec.ofNat 64 64, 16⟩ ⟨c.W + BitVec.ofNat 64 64, 32⟩ := Region.sub_prefix (by decide)
  have s80 : Region.Sub ⟨c.W + BitVec.ofNat 64 80, 16⟩ ⟨c.W + BitVec.ofNat 64 64, 32⟩ :=
    Offset.sub c.W (by decide) (by decide)
  rw [u₁.mem] at f₂
  have fz : Frame [⟨c.W + BitVec.ofNat 64 80, 16⟩] t₂.mem t₁₁.mem := by rw [m₁₁]; exact Proof.Cmac.frame_store2 _ _ _
  have cT : Frame [⟨c.W + BitVec.ofNat 64 64, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩] t.mem t₁₅.mem := by
    rw [m₁₅]
    refine ((f₂.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_)).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s64⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s80⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, s64⟩
      · exact ⟨_, by simp, s80⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  have toR : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region), ⟨c.W + BitVec.ofNat 64 384, 2048⟩],
      ∃ r' ∈ crR c, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  have sep : ∀ {a l : Nat}, a + l ≤ c.n → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region),
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorL (bytesAt t₁₅.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16))
      (bytesAt t₁₅.mem (c.W + BitVec.ofNat 64 80) (c.n % 16)) := ⟨_, rfl⟩
  rw [← hxs] at hm₁₆
  have hxl : xs.length = c.n % 16 := by simp [hxs, xorL, length_bytesAt]
  have fw : Frame [⟨c.D + BitVec.ofNat 64 (16 * (c.n / 16)), c.n % 16⟩] t₁₅.mem t₁₆.mem := by
    rw [hm₁₆]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  refine ⟨pk₁₅.trans (PK.ofKeeps k₁₆), ?_, ?_⟩
  · refine I.frame.trans ((cT.sub toR).trans (fw.sub fun r hr => ?_))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega_arith)⟩
  · have h₁ : bytesAt t₁₅.mem c.D (16 * (c.n / 16)) = bytesAt t.mem c.D (16 * (c.n / 16)) := by
      have := Proof.Cmac.bytesAt_frame cT (sep (a := 0) (l := 16 * (c.n / 16)) (by omega_arith)) (by omega_arith)
      rwa [BitVec.add_zero] at this
    have h₂ : bytesAt t₁₅.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) := by
      rw [Proof.Cmac.bytesAt_frame cT (sep (by omega_arith)) (by omega_arith),
        show c.n % 16 = c.n - 16 * (c.n / 16) by omega_arith, I.rest]
    have f₁₁ : Frame (crR c) s.mem t₁₁.mem := I.frame.trans ((f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s64⟩).trans (fz.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s80⟩))
    have hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem c.K c.R) := fun x => Proof.Cmac.aesWith_length _ _ x
    have hc₁₁ : bytesAt t₁₁.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + c.n / 16) := by
      rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide), hc₂]
    have hz₁₁ : bytesAt t₁₁.mem (c.W + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 := by
      rw [m₁₁]; exact zeros16_bytes _ _
    have hks : bytesAt t₁₅.mem (c.W + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph s.mem c.K c.R (Spec.Ccm.ctrBlock nonce (1 + c.n / 16)) := by
      have hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 1 + c.n / 16) (by rw [hnl]; have := L.h13; omega_arith)
        (fun i hi => by
          rw [show i = 0 by omega_arith, Nat.add_zero]
          show Spec.Gcm.ofBytes _ = _
          rw [hc₁₁]) h.out
      rw [Nat.mul_one] at hx
      rw [m₁₅, hx, hz₁₁, ciph_crR L f₁₁, xorFrom_zeros hBC]
    have ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem c.K c.R) nonce (1 + c.n / 16)
      (d := bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16)) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt, hBC] at ht
    have ht' := ht.resolve_right (by omega_arith)
    rw [hm₁₆, Proof.AesCcm.bytesAt_writeBytes_at t₁₅.mem c.D xs (by rw [hxl]; omega_arith) hn64,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega_arith), List.append_nil,
      ← bytesAt_prefix t₁₅.mem c.D (show 16 * (c.n / 16) ≤ c.n by omega_arith), h₁, I.done, hxs, xorL, h₂,
      bytesAt_prefix t₁₅.mem (c.W + BitVec.ofNat 64 80) (show c.n % 16 ≤ 16 by omega_arith), hks, ht']
    conv => rhs; rw [show c.n = 16 * (c.n / 16) + c.n % 16 from (Nat.div_add_mod c.n 16).symm]
    rw [Proof.Cmac.Stream.bytesAt_append, xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 (c.n / 16)]

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    WP isa ctr s fun s' => PK s s' ∧ Frame (crR c) s.mem s'.mem ∧
      bytesAt s'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 := L.n_lt
  unfold ctr
  refine WP.assoc (WP.seq (WP.mono (ctrHead_wp L hnl E hc0) fun t I => ?_))
  refine WP.seq (wp_li (by decide) fun t₁ u₁ => wp_and fun t₂ u₂ => WP.block_nil ?_)
  have pk₂ : PK t t₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem, u₁.mem]
  have r21₂ : t₂.gpr .r21 = BitVec.ofNat 64 (c.n % 16) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), I.pk.gpr .r23 (by decide), E.r23, ofNat_and15 hn64]
  refine WP.ite (decide (c.n % 16 = 0)) (eval_zero r21₂ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨I.pk.trans pk₂, by rw [m₂]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (c.n / 16) = c.n by omega_arith] at hd
    rw [m₂, hd]
  · have I₂ : CtrInv c nonce s (c.n / 16) t₂ :=
      { I with
        pk := I.pk.trans pk₂
        r18 := by rw [u₂.other _ (by decide), u₁.other _ (by decide), I.r18]
        r19 := by rw [u₂.other _ (by decide), u₁.other _ (by decide), I.r19]
        r20 := by rw [u₂.other _ (by decide), u₁.other _ (by decide), I.r20]
        frame := by rw [m₂]; exact I.frame
        done := by rw [m₂]; exact I.done
        rest := by rw [m₂]; exact I.rest }
    exact tail_wp L hnl E hc0 I₂ r21₂ (of_decide_eq_false hf)

end VG.Proof.AesCcm.PPC64LE
