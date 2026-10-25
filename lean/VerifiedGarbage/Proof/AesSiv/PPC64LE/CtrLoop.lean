module

public import VerifiedGarbage.Proof.AesSiv.PPC64LE.Ctr
import VerifiedGarbage.Proof.AesSiv.PPC64LE.Mac
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp

/-!
# AES-SIV on PPC64LE: CTR a block at a time, and the whole of CTR

Untrusted: everything here is checked by Lean. After `ctrWhole`, the rest of
the data (its last `L mod 16` bytes, and more only if `L ≥ 2³⁵`) is done a
block at a time: the counter `Q + i` is copied to the counter block at
`W + 96`, `vg_aes_ctr32` writes its cipher over the zeroed keystream block at
`W + 80` (`ctrHead_wp`), its first `min(16, left)` bytes are XORed into the
data (`xorBytes`), the counter is incremented and the length left reduced
(`ctrStep_wp`). After block `i` the data is CTR's output on its first
`16 i + min(16, left)` bytes (`ctrPart_step`); `ctr_wp` is the whole: CTR's
output from the counter `Q` of the IV.
-/

@[expose] public section

namespace VG.Proof.AesSiv.PPC64LE

open VG VG.Impl.AesSiv.PPC64LE VG.WriteBytes
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor Upd Mupd
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_subi wp_li wp_lsl wp_lsr wp_add wp_sub)
open VG.Proof.AesCcm.PPC64LE (wp_mv XorPre xorBytes_wp xorL)
open VG.Proof.AesCtr.PPC64LE (CtrCall ctr_call)
open VG.Proof.Gather.PPC64LE (eval_zero eval_nonzero Keeps)
open VG.Spec.Aes (bytesAt)

/-- The C context is clear of what CTR writes. -/
theorem ctrR_c {c : Cx} (L : Lay c) : ∀ r ∈ ctrR c, (⟨c.C, 512⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.c_d
  · exact L.c0_w' (by decide) (by decide)
  · exact L.c0_w' (by decide) (by decide)

/-- What the setup of a block, the call and the length leave. -/
structure CHead (c : Cx) (s₀ : State) (q : List Byte) (i : Nat) (s s' : State) : Prop where
  pk : PK s s'
  r19 : s'.gpr .r19 = s.gpr .r19
  r20 : s'.gpr .r20 = s.gpr .r20
  r3 : s'.gpr .r3 = c.W + BitVec.ofNat 64 ksO
  r9 : s'.gpr .r9 = s.gpr .r19
  r4 : s'.gpr .r4 = BitVec.ofNat 64 (min 16 (c.n - 16 * i))
  ks : bytesAt s'.mem (c.W + BitVec.ofNat 64 ksO) 16 = Siv.ksBlock (Spec.Siv.ctxCiph s₀.mem c.C c.R) q i
  frame : Frame [⟨c.W + BitVec.ofNat 64 ksO, 32⟩, ⟨c.W + BitVec.ofNat 64 scrO, 2048⟩] s.mem s'.mem

/-- `ctrPre`, the call and `ctrMin`: the keystream block of block `i`, and
the bytes of it to XOR. -/
theorem ctrHead_wp {c : Cx} (L : Lay c) {s₀ : State} {q : List Byte} {i : Nat} {s : State}
    (I : CInv c s₀ q i s) (hi : 16 * i < c.n) (E₀ : Env c s₀) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ s', CHead c s₀ q i s s' → WP isa rest s' Q) :
    WP isa (.seq (.block ctrPre) (.seq Impl.AesCtr.PPC64LE.ctrCall (.seq ctrMin rest))) s Q := by
  have hn := L.n_lt
  have hRb := L.rb
  have E := E₀.of_pk I.pk
  unfold ctrPre
  simp only [List.append_assoc]
  refine WP.seq (zero16_wp E (d := ksO) (by decide) (by decide) fun s₁ pk₁ g₁ m₁ => ?_)
  have E₁ := E.of_pk pk₁
  refine copy16_wp E₁ (by decide) (by decide) (by decide) (by decide) (by decide) fun s₂ pk₂ g₂ m₂ => ?_
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (by decide) (by decide)
    fun s₅ u₅ => wp_addi (by decide) (by decide) fun s₆ u₆ => wp_addi (by decide) (by decide) fun s₇ u₇ =>
    wp_li (by decide) fun s₈ u₈ => WP.block_nil ?_
  have pk₈ : PK s₂ s₈ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))
  have E₈ := E.of_pk (pk₁.trans (pk₂.trans pk₈))
  have m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have C : CtrCall s₈ (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 cbO) (c.W + BitVec.ofNat 64 ksO)
      (c.W + BitVec.ofNat 64 scrO) c.R 1 :=
    cargs L E₈ (E₈.perm.wC (by decide)) (by rw [L.wrapW (by decide)]; have := L.ww; simp only [ksO]; omega_arith)
      (L.c_w' (by decide) (by decide)) (L.w_w (.inr (by decide)) (by decide) (by decide))
      (L.w_w (.inl (by decide)) (by decide) (by decide))
      (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, g₁, E.r15])
      (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, g₁, E.r16])
      (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, g₁, E.r14])
      (by simp (disch := decide) only [u₈.other, u₇.gpr, u₆.other, u₅.other, u₄.other, u₃.other, g₂, g₁, E.r14])
      (by simp (disch := decide) only [u₈.gpr])
      (by simp (disch := decide) only [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, g₂, g₁, E.r14])
  refine WP.seq (WP.mono (ctr_call C) fun s₉ h₉ => ?_)
  have pk₉ : PK s₈ s₉ := PK.ofSaved h₉.rd h₉.wr h₉.sp h₉.saved
  have E₉ := E₈.of_pk pk₉
  have keep9 (r : Reg) (hr : r ∈ preserved) : s₉.gpr r = s.gpr r := by
    have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    have h9 : r ≠ .r9 := fun e => by subst e; exact absurd hr (by decide)
    have h3 : r ≠ .r3 := fun e => by subst e; exact absurd hr (by decide)
    have h4 : r ≠ .r4 := fun e => by subst e; exact absurd hr (by decide)
    have h5 : r ≠ .r5 := fun e => by subst e; exact absurd hr (by decide)
    have h6 : r ≠ .r6 := fun e => by subst e; exact absurd hr (by decide)
    have h7 : r ≠ .r7 := fun e => by subst e; exact absurd hr (by decide)
    have h8 : r ≠ .r8 := fun e => by subst e; exact absurd hr (by decide)
    rw [h₉.saved r hr, u₈.other _ h7, u₇.other _ h6, u₆.other _ h8, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3,
      g₂ _ h9, g₁ _ h0]
  -- `ctrMin`.
  have hl : c.n - 16 * i < 2 ^ 64 := by omega_arith
  have r20₉ : s₉.gpr .r20 = BitVec.ofNat 64 (c.n - 16 * i) := by rw [keep9 _ (by decide), I.r20]
  -- The keystream block.
  have dW (d k : Nat) (hd : d + k ≤ 2576) (h1 : d + k ≤ 64 ∨ 112 ≤ d) (h2 : d + k ≤ 384) :
      ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 ksO, 16⟩ : Region)], (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact L.w_w (by simp only [ksO]; omega_arith) hd (by decide)
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 ksO, 16⟩] s.mem s₁.mem := by
    rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
  have f₂ : Frame [⟨c.W + BitVec.ofNat 64 cbO, 16⟩] s₁.mem s₂.mem := by rw [m₂]; exact copyMem_frame _ _ _ _
  have s80 : Region.Sub ⟨c.W + BitVec.ofNat 64 ksO, 16⟩ ⟨c.W + BitVec.ofNat 64 ksO, 32⟩ := Region.sub_prefix (by decide)
  have s96 : Region.Sub ⟨c.W + BitVec.ofNat 64 cbO, 16⟩ ⟨c.W + BitVec.ofNat 64 ksO, 32⟩ :=
    Offset.sub _ (by decide) (by decide)
  have f₀₈ : Frame (ctrR c) s₀.mem s₈.mem := by
    rw [m₈]
    refine I.frame.trans ((f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have hz : bytesAt s₂.mem (c.W + BitVec.ofNat 64 ksO) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂, Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), m₁, Proof.Cmac.zero2_bytes]
  have hcb : bytesAt s₂.mem (c.W + BitVec.ofNat 64 cbO) 16 = Spec.Siv.be128 (Spec.Siv.beNat q + i) := by
    rw [m₂, copyMem_bytes, m₁, Proof.Cmac.zero2, Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), I.cnt.bytes]
  have hks : bytesAt s₉.mem (c.W + BitVec.ofNat 64 ksO) 16 = Siv.ksBlock (Spec.Siv.ctxCiph s₀.mem c.C c.R) q i := by
    have hx := Proof.AesCcm.ctr32_bytes h₉.out
    rw [Nat.mul_one, m₈, hz, Proof.AesSiv.xorKs_zeros, Spec.Gcm.blockAt, hcb,
      Proof.Cmac.aesWith_bytes _ _ (length_be128 _)] at hx
    rw [hx, ← m₈]
    have := ctrPart_frame f₀₈ (ctrR_c L) hRb
    rw [← this]
    rfl
  unfold ctrMin
  refine WP.seq (WP.seq (wp_lsr (by decide) fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by decide) (by decide)
    fun t₃ v₃ => wp_mv fun t₄ v₄ => WP.block_nil ?_))
  have pk₄ : PK s₉ t₄ := (PK.ofUpd v₁).trans ((PK.ofUpd v₂).trans ((PK.ofUpd v₃).trans (PK.ofUpd v₄)))
  have m₄ : t₄.mem = s₉.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  have r10 : t₄.gpr .r10 = BitVec.ofNat 64 ((c.n - 16 * i) / 16) := by
    rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, r20₉, ofNat_lsr4' hl]
  have fr : Frame [⟨c.W + BitVec.ofNat 64 ksO, 32⟩, ⟨c.W + BitVec.ofNat 64 scrO, 2048⟩] s.mem t₄.mem := by
    have f₁₈ : Frame [⟨c.W + BitVec.ofNat 64 ksO, 32⟩, ⟨c.W + BitVec.ofNat 64 scrO, 2048⟩] s₁.mem s₈.mem := by
      rw [m₈]
      refine f₂.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s96⟩
    rw [m₄]
    refine (f₁.sub fun r hr => ?_).trans (f₁₈.trans (h₉.frame.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s80⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, s96⟩
      · exact ⟨_, by simp, s80⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  have base : PK s t₄ ∧ t₄.gpr .r19 = s.gpr .r19 ∧ t₄.gpr .r20 = s.gpr .r20 ∧
      t₄.gpr .r3 = c.W + BitVec.ofNat 64 ksO ∧ t₄.gpr .r9 = s.gpr .r19 := by
    refine ⟨pk₁.trans (pk₂.trans (pk₈.trans (pk₉.trans pk₄))),
      by simp (disch := decide) only [v₄.other, v₃.other, v₂.other, v₁.other, keep9],
      by simp (disch := decide) only [v₄.other, v₃.other, v₂.other, v₁.other, keep9],
      by simp (disch := decide) only [v₄.other, v₃.gpr, v₂.other, v₁.other, E₉.r14],
      by simp (disch := decide) only [v₄.gpr, v₃.other, v₂.other, v₁.other, keep9]⟩
  refine WP.ite (decide ((c.n - 16 * i) / 16 = 0)) (eval_zero r10 (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : (c.n - 16 * i) / 16 = 0 := by simpa using ht
    refine WP.block_nil (k _ ⟨base.1, base.2.1, base.2.2.1, base.2.2.2.1, base.2.2.2.2, ?_, by rw [m₄, hks], fr⟩)
    rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), r20₉,
      Nat.min_eq_right (by omega_arith)]
  · have h0 : (c.n - 16 * i) / 16 ≠ 0 := by simpa using hf
    refine wp_li (by decide) fun t₅ v₅ => WP.block_nil (k _ ⟨base.1.trans (PK.ofUpd v₅),
      by rw [v₅.other _ (by decide), base.2.1], by rw [v₅.other _ (by decide), base.2.2.1],
      by rw [v₅.other _ (by decide), base.2.2.2.1], by rw [v₅.other _ (by decide), base.2.2.2.2],
      by rw [v₅.gpr, Nat.min_eq_left (by omega_arith)], by rw [v₅.mem, m₄, hks], by rw [v₅.mem]; exact fr⟩)

/-- What a block of CTR leaves: block `i + 1`'s registers and counter, and
the data CTR's output on its first `16 i + min(16, left)` bytes. -/
structure Stepped (c : Cx) (s₀ : State) (q : List Byte) (i : Nat) (s s' : State) : Prop where
  pk : PK s s'
  r19 : s'.gpr .r19 = c.D + BitVec.ofNat 64 (16 * (i + 1))
  r20 : s'.gpr .r20 = BitVec.ofNat 64 (c.n - 16 * i - min 16 (c.n - 16 * i))
  cnt : CntAt s'.mem c.W q (i + 1)
  data : bytesAt s'.mem c.D c.n =
    ctrPart (Spec.Siv.ctxCiph s₀.mem c.C c.R) q (bytesAt s₀.mem c.D c.n) (16 * i + min 16 (c.n - 16 * i))
  frame : Frame (ctrR c) s₀.mem s'.mem

/-- The XOR, the counter's increment and the length left. -/
theorem ctrTail_wp {c : Cx} (L : Lay c) {s₀ : State} {q : List Byte} {i : Nat} {s s₃ : State}
    (I : CInv c s₀ q i s) (hi : 16 * i < c.n) (E₀ : Env c s₀) (hlow64 : Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63)
    (H : CHead c s₀ q i s s₃) :
    WP isa (.seq Impl.AesCcm.PPC64LE.xorBytes (.seq (.block ctrPost) ctrLeft)) s₃ (Stepped c s₀ q i s) := by
  have hn := L.n_lt
  have E := E₀.of_pk I.pk
  have E₃ := E.of_pk H.pk
  have hm1 : 0 < min 16 (c.n - 16 * i) := by omega_arith
  have hm16 : min 16 (c.n - 16 * i) ≤ 16 := Nat.min_le_left _ _
  have hmn : 16 * i + min 16 (c.n - 16 * i) ≤ c.n := by omega_arith
  generalize hmd : min 16 (c.n - 16 * i) = mn at hm1 hm16 hmn
  have hsub : Region.Sub ⟨c.D + BitVec.ofNat 64 (16 * i), mn⟩ ⟨c.D, c.n⟩ := Offset.sub_base _ hmn
  have xp : XorPre s₃ (c.W + BitVec.ofNat 64 ksO) (c.D + BitVec.ofNat 64 (16 * i)) mn :=
    { r3 := H.r3
      r9 := by rw [H.r9, I.r19]
      r4 := by rw [H.r4, hmd]
      pos := hm1
      lt := by omega_arith
      rd := E₃.perm.wCR (by simp only [ksO]; omega_arith)
      wr := VG.Proof.Gather.PPC64LE.covers_off E₃.perm.d hmn hn
      disj := ((L.d_w' (d := ksO) (k := mn) (by simp only [ksO]; omega_arith)).sub_left hsub).symm }
  refine WP.seq (WP.mono (xorBytes_wp s₃ xp) fun s₄ ⟨m₄, _, k₄⟩ => ?_)
  have ck : ∀ r ∈ keepRegs, r ∉ VG.Proof.Gather.PPC64LE.copyRegs := by decide
  have pk₄ : PK s₃ s₄ := ⟨k₄.rd, k₄.wr, k₄.sp, fun r hr => k₄.gpr r (ck r hr)⟩
  have E₄ := E₃.of_pk pk₄
  have hxl : (xorL (bytesAt s₃.mem (c.D + BitVec.ofNat 64 (16 * i)) mn)
      (bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) mn)).length = mn := by
    simp [xorL, Proof.Cmac.bytesAt_length]
  have fx : Frame [⟨c.D + BitVec.ofNat 64 (16 * i), mn⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  -- The counter, as it was.
  have dH : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 ksO, 32⟩ : Region), ⟨c.W + BitVec.ofNat 64 scrO, 2048⟩],
      (⟨c.W + BitVec.ofNat 64 cntO, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have cnt₄ : CntAt s₄.mem c.W q i := (I.cnt.frame H.frame dH).frame fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((L.d_w' (d := cntO) (k := 16) (by decide)).sub_left hsub).symm
  have hb : Spec.Siv.beNat q % 2 ^ 64 + i + 1 < 2 ^ 64 := by omega_arith
  refine WP.seq (bump1_wp E₄ cnt₄ hb fun s₅ pk₅ g₅ f₅ cnt₅ => ?_)
  refine wp_addi (by decide) (by decide) fun s₆ u₆ => wp_lsr (by decide) fun s₇ u₇ => WP.block_nil ?_
  have r20₇ : s₇.gpr .r20 = BitVec.ofNat 64 (c.n - 16 * i) := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide) (by decide), k₄.gpr _ (by decide), H.r20,
      I.r20]
  have r9₇ : s₇.gpr .r9 = BitVec.ofNat 64 ((c.n - 16 * i) / 16) := by
    rw [u₇.gpr, u₆.other _ (by decide), g₅ _ (by decide) (by decide), k₄.gpr _ (by decide), H.r20, I.r20,
      ofNat_lsr4' (by omega_arith)]
  have r19₇ : s₇.gpr .r19 = c.D + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [u₇.other _ (by decide), u₆.gpr, g₅ _ (by decide) (by decide), k₄.gpr _ (by decide), H.r19, I.r19,
      Offset.add_add]
    congr 2
  have pk₇ : PK s s₇ := H.pk.trans (pk₄.trans (pk₅.trans ((PK.ofUpd u₆).trans (PK.ofUpd u₇))))
  have m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- The data.
  have hx : (bytesAt s₀.mem c.D c.n).length = c.n := Proof.Cmac.bytesAt_length _ _ _
  have dP : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 ksO, 32⟩ : Region), ⟨c.W + BitVec.ofNat 64 scrO, 2048⟩],
      (⟨c.D, c.n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact L.d_w' (by decide)
  have d₃ : bytesAt s₃.mem c.D (bytesAt s₀.mem c.D c.n).length =
      ctrPart (Spec.Siv.ctxCiph s₀.mem c.C c.R) q (bytesAt s₀.mem c.D c.n) (16 * i) := by
    rw [hx, Proof.Cmac.bytesAt_frame H.frame dP (by omega_arith), I.data]
  have st := ctrPart_step (Spec.Siv.ctxCiph s₀.mem c.C c.R) (fun y => Proof.Cmac.aesWith_length _ _ y) q
    (bytesAt s₀.mem c.D c.n) s₃.mem c.D (i := i) (n := mn) (by omega_arith) hm16 (by omega_arith) d₃
  have kt : bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) mn =
      (Siv.ksBlock (Spec.Siv.ctxCiph s₀.mem c.C c.R) q i).take mn := by
    rw [← H.ks]
    have := take_bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) (a := mn) (b := 16 - mn)
    rw [show mn + (16 - mn) = 16 by omega_arith] at this
    exact this.symm
  rw [hx, ← kt, show Spec.Cmac.xor (bytesAt s₃.mem (c.D + BitVec.ofNat 64 (16 * i)) mn)
      (bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) mn) = xorL (bytesAt s₃.mem (c.D + BitVec.ofNat 64 (16 * i)) mn)
      (bytesAt s₃.mem (c.W + BitVec.ofNat 64 ksO) mn) from rfl, ← m₄] at st
  have data₇ : bytesAt s₇.mem c.D c.n =
      ctrPart (Spec.Siv.ctxCiph s₀.mem c.C c.R) q (bytesAt s₀.mem c.D c.n) (16 * i + mn) := by
    rw [m₇, Proof.Cmac.bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by omega_arith), st]
  -- The frame.
  have frame₇ : Frame (ctrR c) s₀.mem s₇.mem := by
    rw [m₇]
    refine ((I.frame.trans (H.frame.sub fun r hr => ?_)).trans (fx.sub fun r hr => ?_)).trans
      (f₅.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp [scrO], fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, hsub⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Region.sub_prefix (by decide)⟩
  unfold ctrLeft
  refine WP.ite (decide ((c.n - 16 * i) / 16 = 0)) (eval_zero r9₇ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : (c.n - 16 * i) / 16 = 0 := by simpa using ht
    refine wp_li (by decide) fun s₈ u₈ => WP.block_nil ⟨pk₇.trans (PK.ofUpd u₈), by rw [u₈.other _ (by decide), r19₇],
      by rw [u₈.gpr]; congr 1; omega_arith, by rw [u₈.mem, m₇]; exact cnt₅, by rw [u₈.mem, hmd]; exact data₇,
      by rw [u₈.mem]; exact frame₇⟩
  · have h0 : (c.n - 16 * i) / 16 ≠ 0 := by simpa using hf
    refine wp_subi (by decide) (by decide) fun s₈ u₈ => WP.block_nil ⟨pk₇.trans (PK.ofUpd u₈),
      by rw [u₈.other _ (by decide), r19₇], ?_, by rw [u₈.mem, m₇]; exact cnt₅, by rw [u₈.mem, hmd]; exact data₇,
      by rw [u₈.mem]; exact frame₇⟩
    rw [u₈.gpr, r20₇, ofNat_sub' (by omega_arith) (by omega_arith)]
    congr 1; omega_arith

/-- `ctr`: the data XORed with CTR's keystream under `K2` from the counter
`Q` of the IV at `W + src`. -/
theorem ctr_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {src : Nat} (hsrc : src + 16 ≤ cntO)
    (hsrc8 : src % 8 = 0) :
    WP isa (ctr src) s fun s' => PK s s' ∧ Frame (ctrR c) s.mem s'.mem ∧
      bytesAt s'.mem c.D c.n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R)
        (Spec.Siv.counter (bytesAt s.mem (c.W + BitVec.ofNat 64 src) 16)) (bytesAt s.mem c.D c.n) := by
  have hn := L.n_lt
  have hRb := L.rb
  have hk := wholeOf_le c.n
  unfold ctr
  rw [← List.append_nil (counter src)]
  refine WP.seq (counter_wp E hsrc hsrc8 fun s₁ pk₁ f₁ hq₁ => WP.block_nil ?_)
  generalize hqd : Spec.Siv.counter (bytesAt s.mem (c.W + BitVec.ofNat 64 src) 16) = q at hq₁ ⊢
  have hql : q.length = 16 := by rw [← hqd]; exact length_counter _
  have hlow : Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31 := by rw [← hqd]; exact counter_low _
  have hlow64 : Spec.Siv.beNat q % 2 ^ 64 < 2 ^ 63 := by rw [← hqd]; exact counter_low64 _
  have E₁ := E.of_pk pk₁
  have dC : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 cntO, 16⟩ : Region)], (⟨c.C, 512⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.c0_w' (by decide) (by decide)
  have hc : Spec.Siv.ctxCiph s₁.mem c.C c.R = Spec.Siv.ctxCiph s.mem c.C c.R := by
    rw [← ctrPart_frame f₁ dC hRb]; rfl
  have hd : bytesAt s₁.mem c.D c.n = bytesAt s.mem c.D c.n :=
    Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.d_w' (by decide)) (by omega_arith)
  have fr : ∀ {m' : Mem}, Frame (ctrR c) s₁.mem m' → Frame (ctrR c) s.mem m' := fun h =>
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 48⟩, by simp, Region.sub_prefix (by decide)⟩).trans h
  have done {t : State} (pk : PK s₁ t) (f : Frame (ctrR c) s₁.mem t.mem)
      (hdat : bytesAt t.mem c.D c.n = Spec.Siv.ctr (Spec.Siv.ctxCiph s₁.mem c.C c.R) q (bytesAt s₁.mem c.D c.n)) :
      PK s t ∧ Frame (ctrR c) s.mem t.mem ∧
        bytesAt t.mem c.D c.n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem c.C c.R) q (bytesAt s.mem c.D c.n) :=
    ⟨pk₁.trans pk, fr f, by rw [hdat, hc, hd]⟩
  have hcl : ∀ y, (Spec.Siv.ctxCiph s₁.mem c.C c.R y).length = 16 := fun y => Proof.Cmac.aesWith_length _ _ y
  refine WP.seq (WP.mono (ctrWhole_wp L E₁ hql hlow hlow64 (cnt_init hq₁)) fun s₂ I => ?_)
  refine WP.ite (decide (c.n - 16 * wholeOf c.n = 0)) (eval_zero I.r20 (by omega_arith)) (fun ht => WP.block_nil ?_)
    (fun hf => ?_)
  · have h0 : c.n - 16 * wholeOf c.n = 0 := by simpa using ht
    refine done I.pk I.frame ?_
    rw [I.data]
    exact ctrPart_all _ hcl q _ (by rw [Proof.Cmac.bytesAt_length]; omega_arith)
  · have h0 : 16 * wholeOf c.n < c.n := by have : c.n - 16 * wholeOf c.n ≠ 0 := by simpa using hf
                                           omega_arith
    refine WP.loop (M := isa) (fun (m : Nat) (t : State) => ∃ i, m = c.n - 16 * i ∧ 16 * i < c.n ∧ CInv c s₁ q i t)
      ?_ (c.n - 16 * wholeOf c.n) s₂ ⟨wholeOf c.n, rfl, h0, I⟩
    rintro m t ⟨i, rfl, hi, It⟩
    unfold ctrBody
    refine ctrHead_wp L It hi E₁ fun t₃ H => WP.mono (ctrTail_wp L It hi E₁ hlow64 H) fun t' S => ?_
    have ev := eval_nonzero S.r20 (by omega_arith)
    by_cases hfin : c.n - 16 * i ≤ 16
    · left
      refine ⟨by rw [ev]; simp; omega_arith, done (It.pk.trans S.pk) S.frame ?_⟩
      rw [S.data]
      exact ctrPart_all _ hcl q _ (by rw [Proof.Cmac.bytesAt_length]; omega_arith)
    · right
      refine ⟨by rw [ev]; simp; omega_arith, c.n - 16 * (i + 1), by omega_arith, i + 1, rfl, by omega_arith,
        ⟨It.pk.trans S.pk, S.r19, ?_, by omega_arith, S.cnt, ?_, S.frame⟩⟩
      · rw [S.r20]; congr 1; omega_arith
      · rw [S.data]; congr 1; omega_arith

end VG.Proof.AesSiv.PPC64LE
