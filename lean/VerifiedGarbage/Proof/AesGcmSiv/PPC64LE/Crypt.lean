module

public import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Tag
public import VerifiedGarbage.Proof.GcmSiv.Ctr
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.AesGcmSiv.PPC64LE
public import VerifiedGarbage.Impl.AesGcm.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesGcmSiv.PPC64LE.Wp
import VerifiedGarbage.Proof.GcmSiv.Spec

/-!
# AES-GCM-SIV on PPC64LE: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcmSiv/Arm/Crypt.lean`): `cryptHead` writes the initial counter
block from the tag at `W + 96`; each whole block is encrypted in place by a
call of `vg_aes_ctr32` on a copy of the counter block, whose first word is
then incremented (`cryptBlock_wp`, `blocks_wp`); the last bytes are XORed
with a keystream block computed at `W + 240` (`cryptTail_wp`): RFC 8452's
counter mode (`crypt_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.Impl.AesGcmSiv.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (Upd Mupd wp_addi wp_li wp_ld wp_std wp_lsl wp_lsr wp_lwz wp_stw wp_subi
  wp_or)
open VG.Proof.AesCcm.PPC64LE (wp_mv)
open VG.Proof.AesGcm.PPC64LE (CtrCall CtrPost ctr_call LoopPre LoopOut xorLoop_ok xorBytes)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)

theorem ctr32_single (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb x : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem toBytes_xor (a b : Spec.Gcm.Block) :
    Spec.Gcm.toBytes (a ^^^ b) = Spec.Cmac.xor (Spec.Gcm.toBytes a) (Spec.Gcm.toBytes b) := by
  apply List.ext_getElem (by simp [Spec.Gcm.toBytes, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [Spec.Gcm.toBytes, Spec.Cmac.xor, BitVec.extractLsb'_xor]

theorem inc32_word (x : BitVec 32) : ((x.setWidth 64 + BitVec.ofNat 64 1).setWidth 32 : BitVec 32) = x + 1#32 := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- What the counter block at `W + 96` holds before block `j`: the first
word of `icb` plus `j`, and the rest of `icb`. -/
structure CtrSt (W : Addr) (icb : List Byte) (j : Nat) (m : Mem) : Prop where
  word : m.readW (W + BitVec.ofNat 64 96) 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)
  rest : bytesAt m (W + BitVec.ofNat 64 100) 12 = icb.drop 4

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, Offset.add_add, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _
        (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega_arith) (by omega_arith)) hc

/-- What counter mode writes: the counter block and its copy, the block at
`W + 240`, `vg_aes_ctr32`'s working space and the data. -/
abbrev cryR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 1776, 2048⟩, ⟨D, n⟩]

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {c : Cx} (L : Lay c) :
    ∀ r ∈ cryR c.W c.D c.n, (⟨c.W + BitVec.ofNat 64 256, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm

theorem ciph_cryR {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (cryR c.W c.D c.n) m m') :
    Spec.GcmSiv.ctxCiph m' (c.W + BitVec.ofNat 64 256) c.R = Spec.GcmSiv.ctxCiph m (c.W + BitVec.ofNat 64 256) c.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (key_cryR L r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega_arith)]

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (c : Cx) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j : Nat) (t t' : State) : Prop where
  pk : PK t t'
  r23 : t'.gpr .r23 = c.D + BitVec.ofNat 64 (16 * (j + 1))
  r24 : t'.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * (j + 1))
  r11 : t'.gpr .r11 = BitVec.ofNat 64 ((c.n - 16 * (j + 1)) / 16)
  ctr : CtrSt c.W icb (j + 1) t'.mem
  data : bytesAt t'.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (cryR c.W c.D c.n) t.mem t'.mem

/-- The block of `cryptBlock`: the arguments of its call. -/
theorem blkArgs_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {j : Nat} (hj : 16 * (j + 1) ≤ c.n)
    (h23 : t.gpr .r23 = c.D + BitVec.ofNat 64 (16 * j)) :
    WP isa (.block (copy16 cbO ccO ++ ctrArgs ++ ([Impl.AesGcm.PPC64LE.mov .r6 .r23, .li .r7 1] : List Instr))) t fun t₁₀ =>
      PK t t₁₀ ∧ t₁₀.mem = copyMem t.mem c.W ∧
      CtrCall t₁₀ (c.W + BitVec.ofNat 64 256) (c.W + BitVec.ofNat 64 112) (c.D + BitVec.ofNat 64 (16 * j))
        (c.W + BitVec.ofNat 64 1776) c.R 1 ∧ t₁₀.gpr .r23 = t.gpr .r23 ∧ t₁₀.gpr .r24 = t.gpr .r24 := by
  have hw := L.ww
  have hn := L.n_lt
  have hdw := L.dw
  unfold copy16 ctrArgs
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
  refine wp_addi (by decide) (by decide) fun t₅ u₅ => wp_mv fun t₆ u₆ => wp_addi (by decide) (by decide) fun t₇ u₇ =>
    wp_addi (by decide) (by decide) fun t₈ u₈ => wp_mv fun t₉ u₉ => wp_li (by decide) fun t₁₀ u₁₀ => WP.block_nil ?_
  have pk₁₀ : PK t t₁₀ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans
    (PK.ofUpd u₁₀)))))))))
  have E₁₀ := E.of_pk pk₁₀
  have g₁₀ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → t₁₀.gpr r = t.gpr r :=
    fun r h3 h4 h5 h6 h7 h8 => by
      rw [u₁₀.other _ h7, u₉.other _ h6, u₈.other _ h8, u₇.other _ h5, u₆.other _ h4, u₅.other _ h3, u₄.gpr, u₃.gpr,
        g₂ _ h3 h4]
  have hm₁₀ : t₁₀.mem = copyMem t.mem c.W := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.other .r3 (by decide),
      u₁.gpr, u₂.mem, u₁.mem]
    rfl
  have dQ : (⟨c.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨c.W, 3824⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  have hQw : (c.D + BitVec.ofNat 64 (16 * j)).toNat + 16 * 1 ≤ 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * j) (by omega_arith)]
    have := Nat.mod_le (c.D.toNat + 16 * j) (2 ^ 64)
    by_cases h : c.D.toNat + 16 * j < 2 ^ 64
    · rw [Nat.mod_eq_of_lt h]; omega_arith
    · omega_arith
  refine ⟨pk₁₀, hm₁₀, ?_, g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g₁₀ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  exact
    cargs L E₁₀ (E₁₀.perm.wCR (by decide)) (L.w_w (.inr (by decide)) (by decide) (by decide))
      (L.w_w (.inl (by decide)) (by decide) (by decide))
      (by simpa using (dQ.sub_right (Lay.wSub (show 256 + 240 ≤ 3824 by decide))).symm)
      (by simpa using (dQ.sub_right (Lay.wSub (show 112 + 16 ≤ 3824 by decide))).symm)
      (by simpa using dQ.sub_right (Lay.wSub (show 1776 + 2048 ≤ 3824 by decide)))
      (VG.Proof.Gather.PPC64LE.covers_off (n := 16 * 1) E₁₀.perm.d (by omega_arith) (by omega_arith)) hQw
      (by decide)
      (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.gpr, g₂ _ (by decide) (by decide), E.r14] <;> rfl)
      (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, g₂ _ (by decide) (by decide), E.r17])
      (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
        u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, g₂ _ (by decide) (by decide), E.r14] <;> rfl)
      (by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, g₂ _ (by decide) (by decide), h23])
      u₁₀.gpr
      (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, g₂ _ (by decide) (by decide), E.r14] <;> rfl)

theorem cryptBlock_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = c.n) {j : Nat}
    (hj : 16 * (j + 1) ≤ c.n) (h23 : t.gpr .r23 = c.D + BitVec.ofNat 64 (16 * j))
    (h24 : t.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * j)) (C : CtrSt c.W icb j t.mem)
    (hx : bytesAt t.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R = ciph) :
    WP isa cryptBlock t (BlockPost c ciph icb x j t) := by
  have hw := L.ww
  have hn := L.n_lt
  have hdw := L.dw
  unfold cryptBlock
  refine WP.seq (WP.mono (blkArgs_wp L E hj h23) fun t₁₀ ⟨pk₁₀, hm₁₀, cc, r23₁₀, r24₁₀⟩ => ?_)
  have E₁₀ := E.of_pk pk₁₀
  have dQ : (⟨c.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨c.W, 3824⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  -- What the copy changed.
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁₀.mem := by rw [hm₁₀]; exact copyMem_frame _ _
  have dD : ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨c.D, c.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hcb : bytesAt t₁₀.mem (c.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁₀, copyMem_bytes, C.block]
  have hc₁ : Spec.GcmSiv.ctxCiph t₁₀.mem (c.W + BitVec.ofNat 64 256) c.R = ciph := by
    rw [← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.Cmac.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rb))
      (by have := L.rb; omega_arith)]
  have hx₁ : bytesAt t₁₀.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.Cmac.bytesAt_frame f₁ dD (by omega_arith), hx]
  refine WP.seq (WP.mono (ctr_call cc) fun t₁₁ P => ?_)
  have fc := P.frame
  have hout := P.out
  simp only [Nat.mul_one] at fc
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    ctr32_single, List.cons.injEq, and_true] at hout
  have hb₂ : bytesAt t₁₁.mem (c.D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁₀.mem (c.D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith c.R (bytesAt t₁₀.mem (c.W + BitVec.ofNat 64 256) (16 * (c.R + 1))) =
        Spec.GcmSiv.ctxCiph t₁₀.mem (c.W + BitVec.ofNat 64 256) c.R from rfl, hc₁, hcb]
  have hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  have hx₂ : bytesAt t₁₁.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x _ (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega_arith)])
    rw [hxl]
    refine frame_outside fc (fun q hq => ?_) (by omega_arith) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inl rfl
    · exact .inr (L.d_w' (by decide))
  have pk₁₁ : PK t₁₀ t₁₁ := PK.ofSaved P.rd P.wr P.sp P.saved
  have E₁₁ := E₁₀.of_pk pk₁₁
  have h23₂ : t₁₁.gpr .r23 = c.D + BitVec.ofNat 64 (16 * j) := by
    rw [P.saved _ (by decide), r23₁₀, h23]
  have h24₂ : t₁₁.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * j) := by
    rw [P.saved _ (by decide), r24₁₀, h24]
  -- What the first two pieces changed.
  have f₂' : Frame [⟨c.W + BitVec.ofNat 64 112, 16⟩, ⟨c.D + BitVec.ofNat 64 (16 * j), 16⟩,
      ⟨c.W + BitVec.ofNat 64 1776, 2048⟩] t.mem t₁₁.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  have f₂ : Frame (cryR c.W c.D c.n) t.mem t₁₁.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨⟨c.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have dC : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 112 →
      ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨c.W + BitVec.ofNat 64 1776, 2048⟩], (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h₁ h₂ q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (dQ.sub_right (Lay.wSub (by omega_arith))).symm
      · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  have w₂ : t₁₁.mem.readW (c.W + BitVec.ofNat 64 96) 32 = t.mem.readW (c.W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (Nat.le_refl _) (by decide)) (by decide)
  have r₂ : bytesAt t₁₁.mem (c.W + BitVec.ofNat 64 100) 12 = bytesAt t.mem (c.W + BitVec.ofNat 64 100) 12 :=
    Proof.Cmac.bytesAt_frame f₂' (dC (by decide) (by decide)) (by decide)
  -- The counter, the pointer and the count.
  unfold blockNext wholeLeft
  simp only [List.cons_append, List.nil_append]
  refine wp_lwz (a := c.W + BitVec.ofNat 64 96) (by decide) (by decide) (by rw [E₁₁.r14] <;> rfl)
    (E₁₁.perm.wR (by decide)) fun t₁₂ u₁₂ => ?_
  refine wp_addi (by decide) (by decide) fun t₁₃ u₁₃ => ?_
  refine wp_stw (a := c.W + BitVec.ofNat 64 96) (by decide) (by decide)
    (by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), E₁₁.r14] <;> rfl)
    (by rw [u₁₃.wr, u₁₂.wr]; exact E₁₁.perm.wW (by decide)) fun t₁₄ u₁₄ => ?_
  refine wp_addi (by decide) (by decide) fun t₁₅ u₁₅ => wp_subi (by decide) (by decide) fun t₁₆ u₁₆ =>
    wp_lsr (by decide) fun t₁₇ u₁₇ => WP.block_nil ?_
  have pk₁₇ : PK t₁₁ t₁₇ := (PK.ofUpd u₁₂).trans ((PK.ofUpd u₁₃).trans ((PK.ofMupd u₁₄).trans ((PK.ofUpd u₁₅).trans
    ((PK.ofUpd u₁₆).trans (PK.ofUpd u₁₇)))))
  have hm₁₇ : t₁₇.mem = t₁₁.mem.writeW (c.W + BitVec.ofNat 64 96)
      (t₁₁.mem.readW (c.W + BitVec.ofNat 64 96) 32 + 1#32) := by
    rw [u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.gpr, u₁₂.gpr, u₁₃.mem, u₁₂.mem, inc32_word]
  have r24' : t₁₇.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * (j + 1)) := by
    rw [u₁₇.other _ (by decide), u₁₆.gpr, u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), h24₂, ofNat_sub (by omega_arith) (by omega_arith)]
    congr 1 <;> omega_arith
  have fw : ∀ v : BitVec 32, Frame [⟨c.W + BitVec.ofNat 64 96, 4⟩] t₁₁.mem
      (t₁₁.mem.writeW (c.W + BitVec.ofNat 64 96) v) :=
    fun v => (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨pk₁₀.trans (pk₁₁.trans pk₁₇), ?_, r24', ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [u₁₇.other _ (by decide), u₁₆.other _ (by decide), u₁₅.gpr, u₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), h23₂, Offset.add_add, Nat.mul_succ]
  · rw [u₁₇.gpr, u₁₆.gpr, u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide),
      h24₂, ofNat_sub (by omega_arith) (by omega_arith), ofNat_lsr 4 (by omega_arith)]
    congr 1 <;> omega_arith
  · rw [hm₁₇, Mem.readW_writeW_self32, w₂, C.word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_arith
  · rw [hm₁₇, Proof.Cmac.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), r₂, C.rest]
  · rw [hm₁₇, Proof.Cmac.bytesAt_frame (fw _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)) (Nat.le_of_lt (by omega_arith)), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega_arith]
  · rw [hm₁₇]
    exact f₂.writeW (List.mem_cons_self ..) _ (Offset.contains _ (Nat.le_refl _) (by decide) (by decide))

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (c : Cx) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  pk : PK t t'
  r23 : t'.gpr .r23 = c.D + BitVec.ofNat 64 (16 * b)
  r24 : t'.gpr .r24 = BitVec.ofNat 64 (c.n - 16 * b)
  ctr : CtrSt c.W icb b t'.mem
  data : bytesAt t'.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (cryR c.W c.D c.n) t.mem t'.mem

theorem blocks_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = c.n) (hb1 : 1 ≤ c.n / 16)
    (h23 : t.gpr .r23 = c.D) (h24 : t.gpr .r24 = BitVec.ofNat 64 c.n)
    (C : CtrSt c.W icb 0 t.mem) (hx : bytesAt t.mem c.D c.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R = ciph) :
    WP isa (.loop cryptBlock (.nonzero .d .r11)) t (BlocksPost c ciph icb x (c.n / 16) t) := by
  have hn := L.n_lt
  refine WP.loop (M := isa)
    (fun (k : Nat) (t' : State) => ∃ j, k = c.n / 16 - j ∧ j < c.n / 16 ∧ BlocksPost c ciph icb x j t t') ?_
    (c.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨PK.refl _, by rw [h23, Nat.mul_zero, BitVec.add_zero], by rw [h24, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (c.W + BitVec.ofNat 64 256) c.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptBlock_wp L (E.of_pk P.pk) hxl (j := j) (by omega_arith) P.r23 P.r24 P.ctr P.data hc')
    fun t'' Q => ?_
  have P' : BlocksPost c ciph icb x (j + 1) t t'' :=
    ⟨P.pk.trans Q.pk, Q.r23, Q.r24, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  have ev := VG.Proof.Gather.PPC64LE.eval_nonzero Q.r11 (by omega_arith)
  by_cases he : j + 1 = c.n / 16
  · left
    exact ⟨ev.trans (by simp; omega_arith), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), c.n / 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, P'⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (c : Cx) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  pk : PK t t'
  data : bytesAt t'.mem c.D c.n = GcmSiv.ctrPart ciph icb x c.n
  frame : Frame (cryR c.W c.D c.n) t.mem t'.mem

theorem cryptTail_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = c.n) {b r : Nat}
    (hn : c.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h23 : t.gpr .r23 = c.D + BitVec.ofNat 64 (16 * b))
    (h24 : t.gpr .r24 = BitVec.ofNat 64 r) (C : CtrSt c.W icb b t.mem)
    (hx : bytesAt t.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R = ciph) :
    WP isa cryptTail t (TailPost c ciph icb x t) := by
  have hn' := L.n_lt
  have hdw := L.dw
  have hw := L.ww
  unfold cryptTail
  refine WP.seq (WP.mono (tag_wp L E (o := 240) (by decide)) fun t₂ T => ?_)
  have E₂ := E.of_pk T.pk
  have dT : ∀ q ∈ tagR c.W 240, (⟨c.D, c.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> exact L.d_w' (by decide)
  have hx₂ : bytesAt t₂.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.Cmac.bytesAt_frame T.frame dT (by omega_arith), hx]
  have hks : bytesAt t₂.mem (c.W + BitVec.ofNat 64 240) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  refine WP.seq (wp_addi (by decide) (by decide) fun t₃ u₃ => wp_mv fun t₄ u₄ => wp_mv fun t₅ u₅ => WP.block_nil ?_)
  have pk₅ : PK t₂ t₅ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans (PK.ofUpd u₅))
  have E₅ := E₂.of_pk pk₅
  have m₅ : t₅.mem = t₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have dQ : (⟨c.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨c.W, 3824⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  have lp : LoopPre t₅ (c.W + BitVec.ofNat 64 240) (c.D + BitVec.ofNat 64 (16 * b)) r :=
    { r3 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, E₂.r14] <;> rfl
      r4 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), T.r23, h23]
      r5 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), T.r24, h24]
      pos := hr1
      lt := by omega_arith
      rd := VG.Proof.Gather.PPC64LE.covers_prefix (E₅.perm.wCR (show 240 + 16 ≤ 3824 by decide)) (by omega_arith)
      wr := VG.Proof.Gather.PPC64LE.covers_off E₅.perm.d (by omega_arith) (by omega_arith)
      disj := ((dQ.sub_right (Lay.wSub (show 240 + 16 ≤ 3824 by decide))).sub_right
        (Region.sub_prefix (by omega_arith))).symm }
  refine WP.mono (xorLoop_ok t₅ lp) fun t₆ ⟨hm₆, O⟩ => ?_
  rw [m₅] at hm₆
  have hl : (xorBytes t₂.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 240) r).length = r := by
    simp [xorBytes, Proof.Cmac.bytesAt_length]
  have fw : Frame [⟨c.D + BitVec.ofNat 64 (16 * b), r⟩] t₂.mem t₆.mem := by
    rw [hm₆]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  refine ⟨T.pk.trans (pk₅.trans (PK.ofLoop O)), ?_, ?_⟩
  · have hb' : bytesAt t₆.mem (c.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (c.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      have e := Proof.AesGcm.PPC64LE.bytesAt_writeBytes_self t₂.mem (c.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 240) r) (by omega_arith)
      rw [hl] at e
      have hs := Proof.Cmac.bytesAt_add t₂.mem (c.W + BitVec.ofNat 64 240) r (16 - r)
      rw [show r + (16 - r) = 16 by omega_arith, hks] at hs
      rw [hm₆, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x _ (i := b) (n := r) (by omega_arith) hk (by rw [hxl]; exact hx₂)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; omega_arith) (by omega_arith)) hb'
    rwa [hxl, ← hn] at this
  · refine (T.frame.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨⟨c.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base _ (by omega_arith)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (c : Cx) (t t' : State) : Prop where
  pk : PK t t'
  frame : Frame (cryR c.W c.D c.n) t.mem t'.mem
  data : bytesAt t'.mem c.D c.n =
    Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16)) (bytesAt t.mem c.D c.n)

/-- The memory `cryptHead` leaves: the counter block from the tag. -/
def headMem (m : Mem) (W : Addr) : Mem :=
  (m.writeW (W + BitVec.ofNat 64 96) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
    (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (m.readW (W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) 64 |||
      1#64 <<< 63)

/-- What `cryptHead` leaves: the counter block from the tag, and the data as
the bytes to encrypt. -/
structure HeadPost (c : Cx) (t t₁ : State) : Prop where
  pk : PK t t₁
  r23 : t₁.gpr .r23 = c.D
  r24 : t₁.gpr .r24 = BitVec.ofNat 64 c.n
  r11 : t₁.gpr .r11 = BitVec.ofNat 64 (c.n / 16)
  frame : Frame [⟨c.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁.mem
  ctr : CtrSt c.W (Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16)) 0 t₁.mem
  data : bytesAt t₁.mem c.D c.n = bytesAt t.mem c.D c.n
  ciph : Spec.GcmSiv.ctxCiph t₁.mem (c.W + BitVec.ofNat 64 256) c.R =
    Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R

theorem cryptHead_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) : WP isa (.block cryptHead) t (HeadPost c t) := by
  have hw := L.ww
  have hn := L.n_lt
  unfold cryptHead wholeLeft
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ u₁ => wp_mv fun t₂ u₂ => ?_
  have g₂ : ∀ r, r ≠ .r23 → r ≠ .r24 → t₂.gpr r = t.gpr r := fun r h3 h4 => by rw [u₂.other _ h4, u₁.other _ h3]
  have rd₂ : t₂.rd ++ t₂.wr = t.rd ++ t.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine wp_ld (a := c.W + BitVec.ofNat 64 0) (by decide) (by decide) (by rw [g₂ _ (by decide) (by decide), E.r14] <;> rfl)
    (by rw [rd₂]; exact E.perm.wR (by decide)) fun t₃ u₃ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₃.other _ (by decide), g₂ _ (by decide) (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, Offset.add_add]; exact E.perm.wR (by decide)) fun t₄ u₄ => ?_
  refine wp_li (by decide) fun t₅ u₅ => wp_lsl (by decide) fun t₆ u₆ => wp_or fun t₇ u₇ => ?_
  have g₇ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r23 → r ≠ .r24 → t₇.gpr r = t.gpr r :=
    fun r h3 h4 h5 h23 h24 => by
      rw [u₇.other _ h4, u₆.other _ h5, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3, g₂ _ h23 h24]
  have wr₇ : t₇.wr = t.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_std (a := c.W + BitVec.ofNat 64 96) (by decide) (by decide)
    (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r14] <;> rfl)
    (by rw [wr₇]; exact E.perm.wW (by decide)) fun t₈ u₈ => ?_
  refine wp_std (a := c.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (by decide) (by decide)
    (by rw [u₈.gpr, g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r14, Offset.add_add] <;> rfl)
    (by rw [u₈.wr, wr₇, Offset.add_add]; exact E.perm.wW (by decide)) fun t₉ u₉ => ?_
  refine wp_lsr (by decide) fun t₁₀ u₁₀ => WP.block_nil ?_
  have pk₁ : PK t t₁₀ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofMupd u₈).trans ((PK.ofMupd u₉).trans
    (PK.ofUpd u₁₀)))))))))
  have E₁ := E.of_pk pk₁
  have hm₁ : t₁₀.mem = headMem t.mem c.W := by
    rw [u₁₀.mem, u₉.mem, u₈.gpr, u₈.mem, u₇.gpr, u₇.other .r3 (by decide), u₇.mem, u₆.gpr, u₆.other .r3 (by decide),
      u₆.other .r4 (by decide), u₆.mem, u₅.gpr, u₅.other .r3 (by decide), u₅.other .r4 (by decide), u₅.mem, u₄.gpr,
      u₄.other .r3 (by decide), u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem]
    rfl
  have r23₁ : t₁₀.gpr .r23 = c.D := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.r20]
  have r24₁ : t₁₀.gpr .r24 = BitVec.ofNat 64 c.n := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r21]
  have r11₁ : t₁₀.gpr .r11 = BitVec.ofNat 64 (c.n / 16) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.r21, ofNat_lsr 4 hn]
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 96, 16⟩] t.mem t₁₀.mem := by
    rw [hm₁, headMem]; exact Proof.Cmac.frame_store2 _ _ _
  have dD : ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨c.D, c.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  have hx₁ : bytesAt t₁₀.mem c.D c.n = bytesAt t.mem c.D c.n :=
    Proof.Cmac.bytesAt_frame f₁ dD (by omega_arith)
  have hc₁ : Spec.GcmSiv.ctxCiph t₁₀.mem (c.W + BitVec.ofNat 64 256) c.R =
      Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.Cmac.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rb))
      (by have := L.rb; omega_arith)]
  have hicb : bytesAt t₁₀.mem (c.W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16) := by
    rw [hm₁, headMem, Proof.Cmac.bytesAt_store2, show (1#64 <<< 63 : BitVec 64) = 0x8000000000000000#64 by decide,
      ← GcmSiv.initialCounter_words, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split,
      BitVec.add_zero]
  have h4 := Proof.Cmac.bytesAt_add t₁₀.mem (c.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, Offset.add_add] at h4
  have C₀ : CtrSt c.W (Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16)) 0 t₁₀.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  exact ⟨pk₁, r23₁, r24₁, r11₁, f₁, C₀, hx₁, hc₁⟩

theorem crypt_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) : WP isa crypt t (CryptPost c t) := by
  have hw := L.ww
  have hn := L.n_lt
  unfold crypt
  refine WP.seq (WP.mono (cryptHead_wp L E) fun t₁₀ Hd => ?_)
  have pk₁ := Hd.pk
  have E₁ := E.of_pk pk₁
  have r23₁ := Hd.r23
  have r24₁ := Hd.r24
  have r11₁ := Hd.r11
  have f₁ := Hd.frame
  have C₀ := Hd.ctr
  have hx₁ := Hd.data
  have hc₁ := Hd.ciph
  have hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  have hxl : (bytesAt t.mem c.D c.n).length = c.n := Proof.Cmac.bytesAt_length _ _ _
  have fC : ∀ q ∈ [(⟨c.W + BitVec.ofNat 64 96, 16⟩ : Region)], ∃ q' ∈ cryR c.W c.D c.n, Region.Sub q q' :=
    fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨c.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  -- The whole blocks.
  have hmid : WP isa (.ite (.zero .d .r11) (.block []) (.loop cryptBlock (.nonzero .d .r11))) t₁₀
      (BlocksPost c (Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16)) (bytesAt t.mem c.D c.n) (c.n / 16) t₁₀) := by
    refine WP.ite (decide (c.n / 16 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero r11₁ (by omega_arith)) (fun ht => ?_)
      (fun hf => ?_)
    · have h0 : c.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨PK.refl _, by rw [r23₁, Nat.mul_zero, BitVec.add_zero], by rw [r24₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : c.n / 16 ≠ 0 := by simpa using hf
      exact blocks_wp L E₁ hxl (by omega_arith) r23₁ r24₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have r24₂ : t₂.gpr .r24 = BitVec.ofNat 64 (c.n % 16) := by rw [B.r24]; congr 1; omega_arith
  refine WP.ite (decide (c.n % 16 = 0)) (VG.Proof.Gather.PPC64LE.eval_zero r24₂ (by omega_arith)) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : c.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨pk₁.trans B.pk, (f₁.sub fC).trans B.frame, ?_⟩
    rw [B.data, show 16 * (c.n / 16) = c.n by omega_arith, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : c.n % 16 ≠ 0 := by simpa using hf
    have hc₂ : Spec.GcmSiv.ctxCiph t₂.mem (c.W + BitVec.ofNat 64 256) c.R =
        Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R := by
      rw [ciph_cryR L B.frame, hc₁]
    refine WP.mono (cryptTail_wp L (E₁.of_pk B.pk) hxl (b := c.n / 16) (r := c.n % 16) (by omega_arith)
      (by omega_arith) (by omega_arith) B.r23 r24₂ B.ctr B.data hc₂) fun t₃ T => ?_
    refine ⟨pk₁.trans (B.pk.trans T.pk), ((f₁.sub fC).trans B.frame).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.PPC64LE
