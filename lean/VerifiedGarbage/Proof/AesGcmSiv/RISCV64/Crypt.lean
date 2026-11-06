module

public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Tag
public import VerifiedGarbage.Proof.GcmSiv.Ctr
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Callee
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Derive
import VerifiedGarbage.Proof.ChaCha20Poly1305.Gathered
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Aes
import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# AES-GCM-SIV on RISC-V: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/AesGcmSiv/X86_64/Crypt.lean`): `cryptHead` writes the initial
counter block from the tag at `W + 96`; up to 64 whole blocks at a time,
their counter blocks are copied to `W + 496`, the counter block's first
word incremented after each (`ctrBuild_wp`), encrypted in place by one call
of `vg_aes_encrypt_blocks` and XORed into the data (`cryptChunk_wp`,
`blocks_wp`); the last bytes are XORed with a keystream block computed at
`W + 240` (`cryptTail_wp`): RFC 8452's counter mode (`crypt_wp`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_addi wp_li wp_ld wp_sd wp_sll wp_srl wp_lwu wp_sw wp_sub wp_subi wp_or wp_mv)
open VG.Proof.AesGcm.RISCV64 (CtrCall CtrPost ctr_call LoopPre LoopOut xorLoop_ok xorBytes covers_off covers_prefix)
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)

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
`W + 240`, the counter blocks at `W + 496`, the working space of the calls
and the data. -/
abbrev cryR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 96, 32⟩, ⟨W + BitVec.ofNat 64 240, 16⟩, ⟨W + BitVec.ofNat 64 496, 1024⟩,
    ⟨W + BitVec.ofNat 64 1792, 2048⟩, ⟨D, n⟩]

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {c : Cx} (L : Lay c) :
    ∀ r ∈ cryR c.W c.D c.n, (⟨c.W + BitVec.ofNat 64 256, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm

theorem ciph_cryR {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (cryR c.W c.D c.n) m m') :
    Spec.GcmSiv.ctxCiph m' (c.W + BitVec.ofNat 64 256) c.R = Spec.GcmSiv.ctxCiph m (c.W + BitVec.ofNat 64 256) c.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (key_cryR L r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega_arith)]

/-- The counter block, after writes apart from it. -/
theorem CtrSt.of_frame {W : Addr} {icb : List Byte} {j : Nat} {m m' : Mem} (C : CtrSt W icb j m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨W + BitVec.ofNat 64 96, 16⟩ : Region).Disjoint r) : CtrSt W icb j m' :=
  ⟨by rw [hf.readW (Region.contains_self _ _) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))
      (by decide)]; exact C.word,
    by rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left
      (by rw [show W + BitVec.ofNat 64 100 = W + BitVec.ofNat 64 96 + BitVec.ofNat 64 4 by rw [Offset.add_add]]
          exact Offset.sub_base _ (by decide))) (by decide)]; exact C.rest⟩

/-- A run of blocks the XOR loop wrote: each the XOR of the old one with the
block of the source at the same offset. -/
theorem xorBytes_block (m : Mem) (D S : Addr) {k l : Nat} (hl : l < k) (hk : 16 * k < 2 ^ 64) :
    bytesAt (writeBytes m D (Proof.AesGcm.RISCV64.xorBytes m D S (16 * k))) (D + BitVec.ofNat 64 (16 * l)) 16 =
      Spec.Cmac.xor (bytesAt m (D + BitVec.ofNat 64 (16 * l)) 16) (bytesAt m (S + BitVec.ofNat 64 (16 * l)) 16) := by
  apply List.ext_getElem (by simp [bytesAt, Spec.Cmac.xor])
  intro i h₁ h₂
  have hi : i < 16 := by simpa [bytesAt] using h₁
  have hp : 16 * l + i < 16 * k := by omega
  have hl' : (Proof.AesGcm.RISCV64.xorBytes m D S (16 * k)).length = 16 * k :=
    Proof.AesGcm.RISCV64.length_xorBytes _ _ _ _
  simp only [bytesAt, Spec.Cmac.xor, List.getElem_map, List.getElem_range, List.getElem_zipWith, writeBytes,
    Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 16 * l + i < 2 ^ 64 by omega), hl', hp, ite_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hl']; exact hp), Option.getD_some]
  simp [Proof.AesGcm.RISCV64.xorBytes, bytesAt]

/-! ## The counter blocks -/

/-- The memory after the counter block is copied to `P`. -/
def cpyMem (m : Mem) (W P : Addr) : Mem :=
  (m.writeW P (m.readW (W + BitVec.ofNat 64 96) 64)).writeW (P + BitVec.ofNat 64 8)
    (m.readW (W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) 64)

theorem cpyMem_bytes (m : Mem) (W P : Addr) : bytesAt (cpyMem m W P) P 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [cpyMem, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, Proof.Cmac.bytesAt_split]

/-- After `l` of the `k` counter blocks of a chunk from block `j`, from `t₀`. -/
structure GInv (c : Cx) (icb : List Byte) (j k l : Nat) (t₀ t : State) : Prop where
  env : Env c t
  pk : PK t₀ t
  s9 : t.gpr .s9 = t₀.gpr .s9
  s10 : t.gpr .s10 = t₀.gpr .s10
  s11 : t.gpr .s11 = BitVec.ofNat 64 k
  a5 : t.gpr .a5 = c.W + BitVec.ofNat 64 (496 + 16 * l)
  a1 : t.gpr .a1 = BitVec.ofNat 64 (k - l)
  le : l ≤ k
  ctr : CtrSt c.W icb (j + l) t.mem
  frame : Frame [⟨c.W + BitVec.ofNat 64 96, 16⟩, ⟨c.W + BitVec.ofNat 64 496, 1024⟩] t₀.mem t.mem
  blk : ∀ q < l, bytesAt t.mem (c.W + BitVec.ofNat 64 (496 + 16 * q)) 16 = Spec.GcmSiv.counterBlock icb (j + q)

theorem ctr0_wp {c : Cx} {t : State} (E : Env c t) {icb : List Byte} {j k : Nat} (C : CtrSt c.W icb j t.mem)
    (h11 : t.gpr .s11 = BitVec.ofNat 64 k) :
    WP isa (.block [.addi .a5 .s0 (revO : Int), Impl.AesGcm.RISCV64.mov .a1 .s11]) t (GInv c icb j k 0 t) := by
  refine wp_addi (imm := revO) (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ => WP.block_nil ?_
  have pk : PK t t₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  refine ⟨E.of_pk pk, pk, by rw [u₂.other _ (by decide), u₁.other _ (by decide)],
    by rw [u₂.other _ (by decide), u₁.other _ (by decide)], by rw [u₂.other _ (by decide), u₁.other _ (by decide), h11],
    by rw [u₂.other _ (by decide), u₁.gpr, E.s0]; rfl, by rw [u₂.gpr, u₁.other _ (by decide), h11, Nat.sub_zero],
    Nat.zero_le _, by rw [u₂.mem, u₁.mem, Nat.add_zero]; exact C, by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- A counter block of a chunk. -/
theorem ctrStep_wp {c : Cx} (L : Lay c) {icb : List Byte} {j k l : Nat} (hk : k ≤ 64) (hl : l < k)
    {t₀ t : State} (G : GInv c icb j k l t₀ t) : WP isa (.block ctrBody) t (GInv c icb j k (l + 1) t₀) := by
  have hw := L.ww
  have E := G.env
  unfold ctrBody
  refine wp_ld (a := c.W + BitVec.ofNat 64 96) (by decide) (by rw [E.s0]; rfl) (L.wal8 (by decide) (by decide))
    (E.perm.wR (by decide)) fun t₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₁.other _ (by decide), E.s0, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr, Offset.add_add]; exact E.perm.wR (by decide)) fun t₂ u₂ => ?_
  have a5₂ : t₂.gpr .a5 = c.W + BitVec.ofNat 64 (496 + 16 * l) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), G.a5]
  have wr₂ : t₂.wr = t.wr := by rw [u₂.wr, u₁.wr]
  refine wp_sd (a := c.W + BitVec.ofNat 64 (496 + 16 * l)) (by decide) (by rw [a5₂, BitVec.add_zero])
    (L.wal8 (by omega) (by omega)) (by rw [wr₂]; exact E.perm.wW (by omega)) fun t₃ u₃ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 (496 + 16 * l) + BitVec.ofNat 64 8) (by decide) (by rw [u₃.gpr, a5₂])
    (by rw [Offset.add_add]; exact L.wal8 (by omega) (by omega))
    (by rw [u₃.wr, wr₂, Offset.add_add]; exact E.perm.wW (by omega)) fun t₄ u₄ => ?_
  have m₄ : t₄.mem = cpyMem t.mem c.W (c.W + BitVec.ofNat 64 (496 + 16 * l)) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.other .a2 (by decide), u₁.gpr, u₂.mem, u₁.mem]; rfl
  have f₄ : Frame [⟨c.W + BitVec.ofNat 64 (496 + 16 * l), 16⟩] t.mem t₄.mem := by
    rw [m₄]; exact Proof.Cmac.frame_store2 _ _ _
  refine wp_lwu (a := c.W + BitVec.ofNat 64 96) (by decide)
    (by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s0]; rfl)
    (L.wal4 (by decide) (by decide)) (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, wr₂, u₁.rd]; exact E.perm.wR (by decide))
    fun t₅ u₅ => ?_
  refine wp_addi (imm := 1) (by decide) fun t₆ u₆ => ?_
  refine wp_sw (a := c.W + BitVec.ofNat 64 96) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), E.s0]; rfl)
    (L.wal4 (by decide) (by decide)) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂]; exact E.perm.wW (by decide))
    fun t₇ u₇ => ?_
  refine wp_addi (imm := 16) (by decide) fun t₈ u₈ => wp_subi (imm := 1) (by decide) fun t₉ u₉ => WP.block_nil ?_
  have pk : PK t t₉ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofMupd u₇).trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))))))))
  have g₆ : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a5 → t₉.gpr r = t.gpr r :=
    fun r h0 h1 h2 h3 h5 => by
      rw [u₉.other _ h1, u₈.other _ h5, u₇.gpr, u₆.other _ h2, u₅.other _ h2, u₄.gpr, u₃.gpr, u₂.other _ h3,
        u₁.other _ h2]
  have hm : t₉.mem = t₄.mem.writeW (c.W + BitVec.ofNat 64 96) (t₄.mem.readW (c.W + BitVec.ofNat 64 96) 32 + 1#32) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₅.gpr, u₆.mem, u₅.mem, inc32_word]
  have fw : Frame [⟨c.W + BitVec.ofNat 64 96, 4⟩] t₄.mem t₉.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have dP : (⟨c.W + BitVec.ofNat 64 96, 16⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 (496 + 16 * l), 16⟩ :=
    L.w_w (.inl (by omega)) (by decide) (by omega)
  have w₄ : t₄.mem.readW (c.W + BitVec.ofNat 64 96) 32 = t.mem.readW (c.W + BitVec.ofNat 64 96) 32 :=
    f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dP.sub_left (Region.sub_prefix (by decide))) (by decide)
  have C₄ : CtrSt c.W icb (j + l) t₄.mem := G.ctr.of_frame f₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact dP
  refine ⟨E.of_pk pk, G.pk.trans pk, by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), G.s9],
    by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), G.s10],
    by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), G.s11], ?_, ?_, by omega, ⟨?_, ?_⟩, ?_,
    fun q hq => ?_⟩
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), G.a5, Offset.add_add,
      show 496 + 16 * l + 16 = 496 + 16 * (l + 1) by omega]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), G.a1, ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · rw [hm, Mem.readW_writeW_self32, C₄.word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [hm, Proof.Cmac.bytesAt_frame (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _)) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), C₄.rest]
  · refine G.frame.trans ((f₄.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
  · have fw' : Frame [⟨c.W + BitVec.ofNat 64 96, 4⟩] t₄.mem t₉.mem := fw
    rw [Proof.Cmac.bytesAt_frame fw' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) (by omega) (by decide)) (by decide)]
    by_cases e : q = l
    · subst e; rw [m₄, cpyMem_bytes, G.ctr.block]
    · rw [Proof.Cmac.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact G.blk q (by omega)

/-- `ctrBuild`: the `k` counter blocks from block `j`. -/
theorem ctrBuild_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {icb : List Byte} {j k : Nat} (hk1 : 1 ≤ k)
    (hk : k ≤ 64) (C : CtrSt c.W icb j t.mem) (h11 : t.gpr .s11 = BitVec.ofNat 64 k) :
    WP isa ctrBuild t (GInv c icb j k k t) := by
  unfold ctrBuild
  refine WP.seq (WP.mono (ctr0_wp E C h11) fun t₀ G₀ => ?_)
  refine WP.loop (M := isa) (fun m t' => ∃ l, m = k - l ∧ l < k ∧ GInv c icb j k l t t') ?_
    (k - 0) _ ⟨0, rfl, by omega, G₀⟩
  rintro m t' ⟨l, rfl, hl, G⟩
  refine WP.mono (ctrStep_wp L hk hl G) fun t'' G' => ?_
  have ev := Steps.eval_nonzero_ofNat _ _ (by omega) G'.a1
  by_cases he : l + 1 = k
  · left; exact ⟨ev.trans (by simp; omega), he ▸ G'⟩
  · right; exact ⟨ev.trans (by simp; omega), k - (l + 1), by omega, l + 1, rfl, by omega, G'⟩

/-! ## A chunk -/

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (c : Cx) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  pk : PK t t'
  s9 : t'.gpr .s9 = c.D + BitVec.ofNat 64 (16 * b)
  s10 : t'.gpr .s10 = BitVec.ofNat 64 (c.n - 16 * b)
  ctr : CtrSt c.W icb b t'.mem
  data : bytesAt t'.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (cryR c.W c.D c.n) t.mem t'.mem

/-- The arguments of the call of a chunk. -/
theorem encArgs_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {k : Nat} (hk : k ≤ 64)
    (h11 : t.gpr .s11 = BitVec.ofNat 64 k) :
    WP isa (.block chunkEncArgs) t fun t₅ => PK t t₅ ∧ t₅.mem = t.mem ∧
      (∀ r ∈ [Reg.s9, .s10, .s11], t₅.gpr r = t.gpr r) ∧
      Proof.AesOcb.RISCV64.BCall t₅ (c.W + BitVec.ofNat 64 256) (c.W + BitVec.ofNat 64 496)
        (c.W + BitVec.ofNat 64 1792) c.R k := by
  unfold chunkEncArgs
  refine wp_addi (imm := skO) (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_addi (imm := revO) (by decide)
    fun t₃ u₃ => wp_mv fun t₄ u₄ => wp_addi (imm := scrO) (by decide) fun t₅ u₅ => WP.block_nil ?_
  have pk : PK t t₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    (PK.ofUpd u₅))))
  have E₅ := E.of_pk pk
  refine ⟨pk, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], fun r hr => ?_,
    bargs L E₅ (K' := c.W + BitVec.ofNat 64 256) (E₅.perm.wCR (by decide)) hk (L.w_w (.inl (by decide)) (by decide) (by omega))
      (L.w_w (.inl (by decide)) (by decide) (by decide)) ?_ ?_ ?_ ?_ ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      E.s0]; rfl
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      E.s3]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      E.s0]; rfl
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h11]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      E.s0]; rfl

/-- The arguments of the XOR of a chunk's keystream into the data. -/
theorem ksArgs_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) {j k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 64)
    (hjk : 16 * (j + k) ≤ c.n) (h9 : t.gpr .s9 = c.D + BitVec.ofNat 64 (16 * j))
    (h11 : t.gpr .s11 = BitVec.ofNat 64 k) :
    WP isa (.block ksArgs) t fun t₃ => PK t t₃ ∧ t₃.mem = t.mem ∧ (∀ r ∈ [Reg.s9, .s10, .s11], t₃.gpr r = t.gpr r) ∧
      Proof.AesGcm.RISCV64.LoopPre t₃ (c.W + BitVec.ofNat 64 496) (c.D + BitVec.ofNat 64 (16 * j)) (16 * k) := by
  have hn := L.n_lt
  have hdw := L.dw
  unfold ksArgs
  refine wp_addi (imm := revO) (by decide) fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_sll (by decide) fun t₃ u₃ =>
    WP.block_nil ?_
  have pk : PK t t₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
  have E₃ := E.of_pk pk
  have dQ : (⟨c.D + BitVec.ofNat 64 (16 * j), 16 * k⟩ : Region).Disjoint ⟨c.W, 3840⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  refine ⟨pk, by rw [u₃.mem, u₂.mem, u₁.mem], fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  exact { a0 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.s0]; rfl
          a1 := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h9]
          a2 := by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h11, ofNat_shl, Nat.pow_succ]
          pos := by omega
          lt := by omega
          rd := covers_prefix (E₃.perm.wCR (show 496 + 1024 ≤ 3840 by decide)) (by omega)
          wr := covers_off E₃.perm.d (by omega) (by omega)
          disj := (dQ.sub_right (Lay.wSub (show 496 + 1024 ≤ 3840 by decide))).symm.sub_left
            (Region.sub_prefix (by omega)) }

/-- After the XOR: `s9` and `s10` past the chunk, and `a7` zero if no whole
block is left. -/
theorem chunkNext_wp {c : Cx} (L : Lay c) {t : State} {j k : Nat} (hjk : 16 * (j + k) ≤ c.n)
    (ha1 : t.gpr .a1 = c.D + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (16 * k))
    (h10 : t.gpr .s10 = BitVec.ofNat 64 (c.n - 16 * j)) (h11 : t.gpr .s11 = BitVec.ofNat 64 k) :
    WP isa (.block chunkNext) t fun t' => PK t t' ∧ t'.mem = t.mem ∧
      t'.gpr .s9 = c.D + BitVec.ofNat 64 (16 * (j + k)) ∧ t'.gpr .s10 = BitVec.ofNat 64 (c.n - 16 * (j + k)) ∧
      t'.gpr .a7 = BitVec.ofNat 64 ((c.n - 16 * (j + k)) / 16) := by
  have hn := L.n_lt
  unfold chunkNext wholeLeft
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ u₁ => wp_sll (by decide) fun t₂ u₂ => wp_sub fun t₃ u₃ => wp_srl (by decide) fun t₄ u₄ =>
    WP.block_nil ?_
  have s10' : t₃.gpr .s10 = BitVec.ofNat 64 (c.n - 16 * (j + k)) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h10, u₂.gpr, u₁.other _ (by decide), h11,
      ofNat_shl, ofNat_sub (by omega) (by omega)]
    congr 1; omega
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄))),
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_, by rw [u₄.other _ (by decide), s10'], ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, ha1, Offset.add_add,
      Nat.mul_add]
  · rw [u₄.gpr, s10', ofNat_lsr 4 (by omega)]

theorem cryptChunk_wp {c : Cx} (L : Lay c) {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = c.n)
    {j : Nat} (hj : j < c.n / 16) {t t' : State} (E : Env c t') (P : BlocksPost c ciph icb x j t t')
    (hc : Spec.GcmSiv.ctxCiph t'.mem (c.W + BitVec.ofNat 64 256) c.R = ciph) :
    WP isa cryptChunk t' fun t'' => BlocksPost c ciph icb x (j + min ((c.n - 16 * j) / 16) 64) t t'' ∧
      t''.gpr .a7 = BitVec.ofNat 64 ((c.n - 16 * (j + min ((c.n - 16 * j) / 16) 64)) / 16) := by
  have hn := L.n_lt
  have hw := L.ww
  have hdw := L.dw
  generalize hkd : min ((c.n - 16 * j) / 16) 64 = k
  have hk1 : 1 ≤ k := by omega
  have hk : k ≤ 64 := by omega
  have hjk : 16 * (j + k) ≤ c.n := by omega
  have hk16 : ∀ i, (GcmSiv.ksBlock ciph icb i).length = 16 := fun i => by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  unfold cryptChunk
  refine WP.seq (WP.mono (chunkLen_wp (m := c.n - 16 * j) (by omega) P.s10) fun t₁ u₁ => ?_)
  rw [hkd] at u₁
  have E₁ := E.of_pk (PK.ofUpd u₁)
  have C₁ : CtrSt c.W icb j t₁.mem := by rw [u₁.mem]; exact P.ctr
  refine WP.seq (WP.mono (ctrBuild_wp L E₁ hk1 hk C₁ u₁.gpr) fun t₂ G => ?_)
  refine WP.seq (WP.mono (encArgs_wp L G.env hk G.s11) fun t₃ ⟨pk₃, m₃, k₃, bc⟩ => ?_)
  refine WP.seq (WP.mono (Proof.AesOcb.RISCV64.blk_call Proof.Aes.RISCV64.encryptBlocks_correct
    Proof.AesOcb.RISCV64.encryptBlocks_noFrames bc) fun t₄ B => ?_)
  have pk₄ : PK t₃ t₄ := PK.ofSaved B.rd B.wr B.sp B.saved
  have E₄ := G.env.of_pk (pk₃.trans pk₄)
  have g₄ : ∀ r ∈ [Reg.s9, .s10, .s11], t₄.gpr r = t₂.gpr r := fun r hr => by
    rw [B.saved r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;>
      decide), k₃ r hr]
  have s9₄ : t₄.gpr .s9 = c.D + BitVec.ofNat 64 (16 * j) := by
    rw [g₄ _ (by simp), G.s9, u₁.other _ (by decide), P.s9]
  have s10₄ : t₄.gpr .s10 = BitVec.ofNat 64 (c.n - 16 * j) := by
    rw [g₄ _ (by simp), G.s10, u₁.other _ (by decide), P.s10]
  have s11₄ : t₄.gpr .s11 = BitVec.ofNat 64 k := by rw [g₄ _ (by simp), G.s11]
  -- The schedule and the keystream.
  have fG : Frame [⟨c.W + BitVec.ofNat 64 96, 16⟩, ⟨c.W + BitVec.ofNat 64 496, 1024⟩] t'.mem t₂.mem := by
    rw [← u₁.mem]; exact G.frame
  have hc₃ : Spec.GcmSiv.ctxCiph t₃.mem (c.W + BitVec.ofNat 64 256) c.R = ciph := by
    rw [m₃, ← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.Cmac.bytesAt_frame fG (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (L.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rb)
      · exact (L.w_w (.inl (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rb))
      (by have := L.rb; omega)]
  have hks : ∀ q < k, bytesAt t₄.mem (c.W + BitVec.ofNat 64 496 + BitVec.ofNat 64 (16 * q)) 16 =
      GcmSiv.ksBlock ciph icb (j + q) := fun q hq => by
    rw [bytesAt_cipher B.out hq, Offset.add_add, m₃, G.blk q hq, ← m₃, ← hc₃]
    rfl
  -- The XOR.
  refine WP.seq (WP.mono (ksArgs_wp L E₄ hk1 hk hjk s9₄ s11₄) fun t₅ ⟨pk₅, m₅, k₅, lp⟩ => ?_)
  refine WP.seq (WP.mono (xorLoop_ok t₅ lp) fun t₆ ⟨hm₆, O⟩ => ?_)
  have k₆ : ∀ r ∈ [Reg.s9, .s10, .s11], t₆.gpr r = t₄.gpr r := fun r hr => by
    rw [O.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;>
      decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;>
      decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;>
      decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;>
      decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;>
      decide), k₅ r hr]
  refine WP.mono (chunkNext_wp L hjk O.a1 (by rw [k₆ _ (by simp), s10₄]) (by rw [k₆ _ (by simp), s11₄]))
    fun t₇ ⟨pk₇, m₇, s9₇, s10₇, a7₇⟩ => ?_
  -- What the call and the XOR wrote.
  have dQ : (⟨c.D + BitVec.ofNat 64 (16 * j), 16 * k⟩ : Region).Disjoint ⟨c.W, 3840⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega))
  have fX : Frame [⟨c.D + BitVec.ofNat 64 (16 * j), 16 * k⟩] t₄.mem t₇.mem := by
    rw [m₇, hm₆, m₅]
    exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [Proof.AesGcm.RISCV64.length_xorBytes]; exact Region.contains_self _ _)
  have fB : Frame [⟨c.W + BitVec.ofNat 64 496, 1024⟩, ⟨c.W + BitVec.ofNat 64 1792, 2048⟩] t₃.mem t₄.mem :=
    B.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  refine ⟨⟨?_, s9₇, s10₇, ?_, ?_, ?_⟩, a7₇⟩
  · exact P.pk.trans ((PK.ofUpd u₁).trans (G.pk.trans (pk₃.trans (pk₄.trans (pk₅.trans ((PK.ofLoop O).trans pk₇))))))
  · -- The counter block.
    refine ((G.ctr.of_frame (by rw [m₃] at fB; exact fB) fun r hr => ?_).of_frame fX fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dQ.sub_right (Lay.wSub (by decide))).symm
  · -- The data.
    have hD₄ : bytesAt t₄.mem c.D c.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
      rw [Proof.Cmac.bytesAt_frame fB (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact L.d_w' (by decide)) (by omega), m₃,
        Proof.Cmac.bytesAt_frame fG (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact L.d_w' (by decide)) (by omega), P.data]
    rw [← hxl] at hD₄ ⊢
    refine GcmSiv.ctrPart_stepN ciph icb x c.D (fun l _ => hk16 _) hD₄ ?_ fun l hl => ?_
    · rw [hxl]
      intro p hp ho
      refine frame_outside fX (len := c.n) (a := 16 * j) (n := 16 * k) (fun q hq => ?_) (by omega) (by omega) p hp
        (by omega)
      simp only [List.mem_singleton] at hq
      exact .inl hq
    · rw [m₇, hm₆, m₅, show c.D + BitVec.ofNat 64 (16 * (j + l)) =
          c.D + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 (16 * l) by rw [Offset.add_add, Nat.mul_add],
        xorBytes_block _ _ _ hl (by omega), ← hks l hl]
  · -- The frame.
    refine P.frame.trans ((?_ : Frame (cryR c.W c.D c.n) t'.mem t₂.mem).trans
      ((?_ : Frame (cryR c.W c.D c.n) t₂.mem t₄.mem).trans (?_ : Frame (cryR c.W c.D c.n) t₄.mem t₇.mem)))
    · exact fG.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    · rw [← m₃]; exact fB.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, fun _ h => h⟩
    · exact fX.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base _ (by omega)⟩

theorem blocks_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = c.n) (hb1 : 1 ≤ c.n / 16)
    (h9 : t.gpr .s9 = c.D) (h10 : t.gpr .s10 = BitVec.ofNat 64 c.n)
    (C : CtrSt c.W icb 0 t.mem) (hx : bytesAt t.mem c.D c.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R = ciph) :
    WP isa (.loop cryptChunk (.nonzero .a7)) t (BlocksPost c ciph icb x (c.n / 16) t) := by
  have hn := L.n_lt
  refine WP.loop (M := isa)
    (fun (m : Nat) (t' : State) => ∃ j, m = c.n / 16 - j ∧ j < c.n / 16 ∧ BlocksPost c ciph icb x j t t') ?_
    (c.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨PK.refl _, by rw [h9, Nat.mul_zero, BitVec.add_zero], by rw [h10, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro m t' ⟨j, rfl, hj, P⟩
  have hc' : Spec.GcmSiv.ctxCiph t'.mem (c.W + BitVec.ofNat 64 256) c.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptChunk_wp L hxl hj (E.of_pk P.pk) P hc') fun t'' ⟨Q, a7⟩ => ?_
  have ev := Steps.eval_nonzero_ofNat _ _ (by omega) a7
  by_cases he : j + min ((c.n - 16 * j) / 16) 64 = c.n / 16
  · left
    exact ⟨ev.trans (by simp; omega), he ▸ Q⟩
  · right
    exact ⟨ev.trans (by simp; omega), c.n / 16 - (j + min ((c.n - 16 * j) / 16) 64), by omega,
      j + min ((c.n - 16 * j) / 16) 64, rfl, by omega, Q⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (c : Cx) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  pk : PK t t'
  data : bytesAt t'.mem c.D c.n = GcmSiv.ctrPart ciph icb x c.n
  frame : Frame (cryR c.W c.D c.n) t.mem t'.mem

theorem cryptTail_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = c.n) {b r : Nat}
    (hn : c.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (h9 : t.gpr .s9 = c.D + BitVec.ofNat 64 (16 * b))
    (h10 : t.gpr .s10 = BitVec.ofNat 64 r) (C : CtrSt c.W icb b t.mem)
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
  refine WP.seq (wp_addi (by decide) fun t₃ u₃ => wp_mv fun t₄ u₄ => wp_mv fun t₅ u₅ => WP.block_nil ?_)
  have pk₅ : PK t₂ t₅ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans (PK.ofUpd u₅))
  have E₅ := E₂.of_pk pk₅
  have m₅ : t₅.mem = t₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  have dQ : (⟨c.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨c.W, 3840⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  have lp : LoopPre t₅ (c.W + BitVec.ofNat 64 240) (c.D + BitVec.ofNat 64 (16 * b)) r :=
    { a0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, E₂.s0] <;> rfl
      a1 := by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), T.s9, h9]
      a2 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), T.s10, h10]
      pos := hr1
      lt := by omega_arith
      rd := covers_prefix (E₅.perm.wCR (show 240 + 16 ≤ 3840 by decide)) (by omega_arith)
      wr := covers_off E₅.perm.d (by omega_arith) (by omega_arith)
      disj := ((dQ.sub_right (Lay.wSub (show 240 + 16 ≤ 3840 by decide))).sub_right
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
      have e := Proof.ChaCha20Poly1305.bytesAt_writeBytes_self t₂.mem (c.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 240) r) (by omega_arith)
      rw [hl, Proof.ChaCha20Poly1305.bytesAt_eq_aes] at e
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
  s9 : t₁.gpr .s9 = c.D
  s10 : t₁.gpr .s10 = BitVec.ofNat 64 c.n
  a7 : t₁.gpr .a7 = BitVec.ofNat 64 (c.n / 16)
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
  have g₂ : ∀ r, r ≠ .s9 → r ≠ .s10 → t₂.gpr r = t.gpr r := fun r h3 h4 => by rw [u₂.other _ h4, u₁.other _ h3]
  have rd₂ : t₂.rd ++ t₂.wr = t.rd ++ t.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine wp_ld (a := c.W + BitVec.ofNat 64 0) (by decide) (by rw [g₂ _ (by decide) (by decide), E.s0] <;> rfl)
    (L.wal8 (by decide) (by decide))
    (by rw [rd₂]; exact E.perm.wR (by decide)) fun t₃ u₃ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 0 + BitVec.ofNat 64 8) (by decide) (by rw [u₃.other _ (by decide), g₂ _ (by decide) (by decide), E.s0, Offset.add_add] <;> rfl)
    (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₃.rd, u₃.wr, rd₂, Offset.add_add]; exact E.perm.wR (by decide)) fun t₄ u₄ => ?_
  refine wp_li (by decide) fun t₅ u₅ => wp_sll (by decide) fun t₆ u₆ => wp_or fun t₇ u₇ => ?_
  have g₇ : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .s9 → r ≠ .s10 → t₇.gpr r = t.gpr r :=
    fun r h3 h4 h5 h9 h10 => by
      rw [u₇.other _ h4, u₆.other _ h5, u₅.other _ h5, u₄.other _ h4, u₃.other _ h3, g₂ _ h9 h10]
  have wr₇ : t₇.wr = t.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_sd (a := c.W + BitVec.ofNat 64 96) (by decide) (by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E.s0] <;> rfl)
    (L.wal8 (by decide) (by decide))
    (by rw [wr₇]; exact E.perm.wW (by decide)) fun t₈ u₈ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 96 + BitVec.ofNat 64 8) (by decide) (by rw [u₈.gpr, g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), E.s0, Offset.add_add] <;> rfl)
    (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₈.wr, wr₇, Offset.add_add]; exact E.perm.wW (by decide)) fun t₉ u₉ => ?_
  refine wp_srl (by decide) fun t₁₀ u₁₀ => WP.block_nil ?_
  have pk₁ : PK t t₁₀ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofMupd u₈).trans ((PK.ofMupd u₉).trans
    (PK.ofUpd u₁₀)))))))))
  have E₁ := E.of_pk pk₁
  have hm₁ : t₁₀.mem = headMem t.mem c.W := by
    rw [u₁₀.mem, u₉.mem, u₈.gpr, u₈.mem, u₇.gpr, u₇.other .a0 (by decide), u₇.mem, u₆.gpr, u₆.other .a0 (by decide),
      u₆.other .a1 (by decide), u₆.mem, u₅.gpr, u₅.other .a0 (by decide), u₅.other .a1 (by decide), u₅.mem, u₄.gpr,
      u₄.other .a0 (by decide), u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem]
    rfl
  have s9₁ : t₁₀.gpr .s9 = c.D := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.s6]
  have s10₁ : t₁₀.gpr .s10 = BitVec.ofNat 64 c.n := by
    rw [u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s7]
  have a7₁ : t₁₀.gpr .a7 = BitVec.ofNat 64 (c.n / 16) := by
    rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s7, ofNat_lsr 4 hn]
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
  exact ⟨pk₁, s9₁, s10₁, a7₁, f₁, C₀, hx₁, hc₁⟩

theorem crypt_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) : WP isa crypt t (CryptPost c t) := by
  have hw := L.ww
  have hn := L.n_lt
  unfold crypt
  refine WP.seq (WP.mono (cryptHead_wp L E) fun t₁₀ Hd => ?_)
  have pk₁ := Hd.pk
  have E₁ := E.of_pk pk₁
  have s9₁ := Hd.s9
  have s10₁ := Hd.s10
  have a7₁ := Hd.a7
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
  have hmid : WP isa (.ite (.zero .a7) (.block []) (.loop cryptChunk (.nonzero .a7))) t₁₀
      (BlocksPost c (Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem c.W 16)) (bytesAt t.mem c.D c.n) (c.n / 16) t₁₀) := by
    refine WP.ite (decide (c.n / 16 = 0)) (Steps.eval_zero_ofNat _ _ (by omega_arith) a7₁) (fun ht => ?_)
      (fun hf => ?_)
    · have h0 : c.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨PK.refl _, by rw [s9₁, Nat.mul_zero, BitVec.add_zero], by rw [s10₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : c.n / 16 ≠ 0 := by simpa using hf
      exact blocks_wp L E₁ hxl (by omega_arith) s9₁ s10₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  have s10₂ : t₂.gpr .s10 = BitVec.ofNat 64 (c.n % 16) := by rw [B.s10]; congr 1; omega_arith
  refine WP.ite (decide (c.n % 16 = 0)) (Steps.eval_zero_ofNat _ _ (by omega_arith) s10₂) (fun ht => ?_)
    (fun hf => ?_)
  · have h0 : c.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨pk₁.trans B.pk, (f₁.sub fC).trans B.frame, ?_⟩
    rw [B.data, show 16 * (c.n / 16) = c.n by omega_arith, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : c.n % 16 ≠ 0 := by simpa using hf
    have hc₂ : Spec.GcmSiv.ctxCiph t₂.mem (c.W + BitVec.ofNat 64 256) c.R =
        Spec.GcmSiv.ctxCiph t.mem (c.W + BitVec.ofNat 64 256) c.R := by
      rw [ciph_cryR L B.frame, hc₁]
    refine WP.mono (cryptTail_wp L (E₁.of_pk B.pk) hxl (b := c.n / 16) (r := c.n % 16) (by omega_arith)
      (by omega_arith) (by omega_arith) B.s9 s10₂ B.ctr B.data hc₂) fun t₃ T => ?_
    refine ⟨pk₁.trans (B.pk.trans T.pk), ((f₁.sub fC).trans B.frame).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.RISCV64
