module

public import VerifiedGarbage.Proof.AesCcm.RISCV64.Chunk
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesCcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesCcm.RISCV64.B0
import VerifiedGarbage.Proof.AesCcm.RISCV64.Callee
import VerifiedGarbage.Proof.AesCcm.RISCV64.Ctrs
import VerifiedGarbage.Proof.AesCcm.RISCV64.Header
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
public import VerifiedGarbage.Impl.AesCcm.RISCV64

/-!
# AES-CCM on RISCV64: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data in chunks (`ctrHead_wp`, by `chunk_wp`), then its last
`n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which `vg_aes_ctr32` writes over a
zero block (`tail_wp`): the data XORed with CCM's keystream from `Ctr₁`
(`ctr_wp`), which is its encryption (`Proof.AesCcm.crypt_eq`), as on
AArch64.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Proof.AesCtr.RISCV64 (ctr_call)
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (xorFrom xorFrom_append ctr32_ccm length_bytesAt bytesAt_prefix bytesAt_suffix
  BlockCipher xorFrom_zeros xorFrom_tail)

/-- The whole blocks, in chunks. -/
theorem ctrHead_wp {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} (E : Env c s)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    WP isa (.seq (.block [mov .s5 .s9, .shift .srl .d .s6 .s10 4, .li .s7 1])
      (.ite (.zero .s6) (.block []) (.loop ctrChunk (.nonzero .s6)))) s
      (CtrInv c nonce s (c.n / 16)) := by
  have hn64 := L.n_lt
  refine WP.seq (wp_mv fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
    WP.block_nil ?_)
  have I₀ : CtrInv c nonce s 0 s₃ :=
    { pk := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
      s5 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.s9]; exact (BitVec.add_zero _).symm
      s6 := by
        rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s10,
          ofNat_lsr4 hn64, Nat.sub_zero]
      s7 := u₃.gpr
      le := Nat.zero_le _
      frame := by rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _
      done := rfl
      rest := by rw [u₃.mem, u₂.mem, u₁.mem] }
  refine WP.ite (decide (c.n / 16 = 0)) (eval_z (a := c.n / 16) (by rw [I₀.s6, Nat.sub_zero]) (by omega))
    (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n / 16 = 0 := of_decide_eq_true ht
    exact WP.block_nil (by rw [h0]; exact I₀)
  · have h0 : c.n / 16 ≠ 0 := of_decide_eq_false hf
    refine WP.loop (M := isa) (fun m t => ∃ b, m = c.n / 16 - b ∧ b < c.n / 16 ∧ CtrInv c nonce s b t) ?_
      (c.n / 16 - 0) s₃ ⟨0, rfl, by omega, I₀⟩
    rintro m t ⟨b, rfl, hb, I⟩
    refine WP.mono (chunk_wp L hnl E hc0 I hb) fun t' ⟨k, _, hk1, hkb, I'⟩ => ?_
    have ev := eval_nz (r := .s6) (a := c.n / 16 - (b + k)) I'.s6 (by omega)
    by_cases he : b + k = c.n / 16
    · left; exact ⟨by rw [ev]; simp [he], by rw [← he]; exact I'⟩
    · right; exact ⟨by rw [ev]; simp; omega, c.n / 16 - (b + k), by omega, b + k, rfl, by omega, I'⟩

/-- The last `n mod 16` (not 0) bytes, XORed with `CIPH_K(Ctr₁₊ₙ/₁₆)`. -/
theorem tail_wp {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} (E : Env c s)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {t : State}
    (I : CtrInv c nonce s (c.n / 16) t) (hs8 : t.gpr .s8 = BitVec.ofNat 64 (c.n % 16)) (h0 : c.n % 16 ≠ 0) :
    WP isa ctrTail t fun t' => PK s t' ∧ Frame (crR c) s.mem t'.mem ∧
      bytesAt t'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  have Et := E.of_pk I.pk
  have hc0t : bytesAt t.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [Proof.Cmac.bytesAt_frame I.frame (crR_disj L (.inl (by decide))) (by decide), hc0]
  have hi : 1 + c.n / 16 < 256 ^ (15 - c.nl) := by have := L.hn; omega
  unfold ctrTail
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_mv fun t₁ u₁ => ?_)
  refine ctrAt_wp L (Et.of_pk (PK.ofUpd u₁)) hnl (by rw [u₁.mem]; exact hc0t) hi
    (by rw [u₁.gpr, I.s7]) fun t₂ pk₂ kp₂ f₂ hc₂ => ?_
  unfold zero16 ctrArgs
  simp only [List.cons_append, List.nil_append]
  have pk₂' : PK s t₂ := I.pk.trans ((PK.ofUpd u₁).trans pk₂)
  refine wp_li (by decide) fun t₃ u₃ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 80) (by decide)
    (by rw [u₃.other _ (by decide), pk₂'.gpr .s1 (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₃.wr, pk₂'.wr]; exact E.perm.wW (by decide)) fun t₄ u₄ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₄.gpr, u₃.other _ (by decide), pk₂'.gpr .s1 (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.alW (by decide) (by decide))
    (by rw [u₄.wr, u₃.wr, pk₂'.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun t₅ u₅ => ?_
  refine wp_mv fun t₆ u₆ => wp_mv fun t₇ u₇ => wp_addi (by decide) fun t₈ u₈ =>
    wp_addi (by decide) fun t₉ u₉ => wp_addi (by decide) fun t₁₀ u₁₀ =>
    wp_li (by decide) fun t₁₁ u₁₁ => WP.block_nil ?_
  have pk₁₁ : PK t₂ t₁₁ := (PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans ((PK.ofMupd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans (PK.ofUpd u₁₁))))))))
  have E₁₁ := E.of_pk (pk₂'.trans pk₁₁)
  have m₁₁ : t₁₁.mem = (t₂.mem.writeW (c.W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₃.gpr]; rfl
  have r_ : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a5 → r ≠ .a3 → r ≠ .a4 → t₁₁.gpr r = t₂.gpr r :=
    fun r h0 h3 h4 h5 h8 h6 h7 => by
      rw [u₁₁.other _ h7, u₁₀.other _ h6, u₉.other _ h8, u₈.other _ h5, u₇.other _ h4, u₆.other _ h3, u₅.gpr,
        u₄.gpr, u₃.other _ h0]
  have C := cargsW L E₁₁ (o := 64) (d := 80) (by decide) (by decide) (by decide)
    (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ (by decide), pk₂'.gpr .s3 (by decide), E.s3])
    (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide), pk₂'.gpr .s4 (by decide), E.s4])
    (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      pk₂'.gpr .s1 (by decide), E.s1]; rfl)
    (by rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      pk₂'.gpr .s1 (by decide), E.s1]; rfl)
    (by rw [u₁₁.gpr])
    (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      pk₂'.gpr .s1 (by decide), E.s1]; rfl)
  refine WP.seq (WP.mono (ctr_call C) fun t₁₂ h => ?_)
  have sv : ∀ r ∈ [Reg.s5, .s8], t₁₂.gpr r = t.gpr r := fun r hr => by
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [h.saved _ hp, r_ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        kp₂ _ (by simp), u₁.other _ (by decide)]
  refine WP.seq (wp_addi (by decide) fun t₁₃ u₁₃ => wp_mv fun t₁₄ u₁₄ => wp_mv fun t₁₅ u₁₅ =>
    WP.block_nil ?_)
  have pk₁₅ : PK s t₁₅ := pk₂'.trans (pk₁₁.trans ((PK.ofSaved h.rd h.wr h.sp h.saved).trans ((PK.ofUpd u₁₃).trans
    ((PK.ofUpd u₁₄).trans (PK.ofUpd u₁₅)))))
  have E₁₅ := E.of_pk pk₁₅
  have m₁₅ : t₁₅.mem = t₁₂.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem]
  have hS := (L.bufD E₁₅.perm).drop (k := 16 * (c.n / 16)) (by omega)
  rw [show c.n - 16 * (c.n / 16) = c.n % 16 by omega] at hS
  have xp : BytesPre t₁₅ (c.W + BitVec.ofNat 64 80) (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) :=
    { a0 := by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, h.saved .s1 (by decide),
        (pk₁₁).gpr .s1 (by decide), pk₂'.gpr .s1 (by decide), E.s1]; rfl
      a1 := by rw [u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide), sv .s5 (by simp), I.s5]
      a2 := by rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), sv .s8 (by simp), hs8]
      pos := by omega
      lt := by omega
      rd := E₁₅.perm.wCR (by omega)
      wr := covers_off E₁₅.perm.d (by omega) hn64
      disj := (hS.wd (by omega)).symm }
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
    exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega)⟩
  · have h₁ : bytesAt t₁₅.mem c.D (16 * (c.n / 16)) = bytesAt t.mem c.D (16 * (c.n / 16)) := by
      have := Proof.Cmac.bytesAt_frame cT (sep (a := 0) (l := 16 * (c.n / 16)) (by omega)) (by omega)
      rwa [BitVec.add_zero] at this
    have h₂ : bytesAt t₁₅.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) := by
      rw [Proof.Cmac.bytesAt_frame cT (sep (by omega)) (by omega),
        show c.n % 16 = c.n - 16 * (c.n / 16) by omega, I.rest]
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
      have hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 1 + c.n / 16) (by rw [hnl]; have := L.h13; omega)
        (fun i hi => by
          rw [show i = 0 by omega, Nat.add_zero]
          show Spec.Gcm.ofBytes _ = _
          rw [hc₁₁]) h.out
      rw [Nat.mul_one] at hx
      rw [m₁₅, hx, hz₁₁, ciph_crR L f₁₁, xorFrom_zeros hBC]
    have ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem c.K c.R) nonce (1 + c.n / 16)
      (d := bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16)) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt, hBC] at ht
    have ht' := ht.resolve_right (by omega)
    rw [hm₁₆, Proof.AesCcm.bytesAt_writeBytes_at t₁₅.mem c.D xs (by rw [hxl]; omega) hn64,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega), List.append_nil,
      ← bytesAt_prefix t₁₅.mem c.D (show 16 * (c.n / 16) ≤ c.n by omega), h₁, I.done, hxs, xorL, h₂,
      bytesAt_prefix t₁₅.mem (c.W + BitVec.ofNat 64 80) (show c.n % 16 ≤ 16 by omega), hks, ht']
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
  refine WP.seq (wp_andi (by decide) fun t₂ u₂ => WP.block_nil ?_)
  have pk₂ : PK t t₂ := PK.ofUpd u₂
  have m₂ : t₂.mem = t.mem := by rw [u₂.mem]
  have s8₂ : t₂.gpr .s8 = BitVec.ofNat 64 (c.n % 16) := by
    rw [u₂.gpr, I.pk.gpr .s10 (by decide), E.s10, show BitVec.ofInt 64 15 = BitVec.ofNat 64 15 from rfl,
      ofNat_and15 hn64]
  refine WP.ite (decide (c.n % 16 = 0)) (eval_z s8₂ (by omega)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨I.pk.trans pk₂, by rw [m₂]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (c.n / 16) = c.n by omega] at hd
    rw [m₂, hd]
  · have I₂ : CtrInv c nonce s (c.n / 16) t₂ :=
      { I with
        pk := I.pk.trans pk₂
        s5 := by rw [u₂.other _ (by decide), I.s5]
        s6 := by rw [u₂.other _ (by decide), I.s6]
        s7 := by rw [u₂.other _ (by decide), I.s7]
        frame := by rw [m₂]; exact I.frame
        done := by rw [m₂]; exact I.done
        rest := by rw [m₂]; exact I.rest }
    exact tail_wp L hnl E hc0 I₂ s8₂ (of_decide_eq_false hf)

end VG.Proof.AesCcm.RISCV64
