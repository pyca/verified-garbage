module

import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
public import VerifiedGarbage.Proof.GcmSiv.Spec
public import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Callee
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Spec.Gcm

/-!
# AES-GCM-SIV on RISC-V: the message keys (`derive`)

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/AesGcmSiv/X86_64/Derive.lean`), with the nonce read from its copy
at `W + 1520`: `deriveBuild` writes the `rounds / 2 - 1` blocks
`little_endian_uint32(i) ‖ nonce` at `W + 496 + 16 i` (`build_wp`), which
one call of `vg_aes_encrypt_blocks` replaces by their ciphers (`call_wp`),
of which `deriveKeep` keeps the first 8 bytes at `W + 16 + 8 i`
(`keep_wp`): the halves of `derive_keys` (`derive_wp`, `DOut.keys`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_addi wp_li wp_ld wp_sd wp_lwu wp_sw wp_srl wp_subi wp_mv)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesOcb.RISCV64 (BCall BPost blk_call encryptBlocks_noFrames)

/-- The number of blocks of the message keys, `rounds / 2 - 1`. -/
abbrev cnt (c : Cx) : Nat := c.R / 2 - 1

theorem cnt_bounds {c : Cx} (L : Lay c) : 2 ≤ cnt c ∧ cnt c ≤ 6 := by
  rcases L.rounds with h | h <;> simp [cnt, h]

/-- Block `i` of the blocks at `W + 496`. -/
abbrev kbP (W : Addr) (i : Nat) : Addr := W + BitVec.ofNat 64 (496 + 16 * i)

/-! ## The blocks -/

/-- The memory after block `i` is written at `P`: `little_endian_uint32(i)`
and the nonce's three words. -/
def bldMem (m : Mem) (P W : Addr) (i : Nat) : Mem :=
  Proof.Cmac.store4 m P ((BitVec.ofNat 64 i).setWidth 32) (m.readW (nP W + BitVec.ofNat 64 0) 32)
    (m.readW (nP W + BitVec.ofNat 64 4) 32) (m.readW (nP W + BitVec.ofNat 64 8) 32)

theorem bldMem_bytes (m : Mem) (P W : Addr) (i : Nat) :
    bytesAt (bldMem m P W i) P 16 = Spec.GcmSiv.le32 i ++ bytesAt m (nP W) 12 := by
  rw [bldMem, Proof.Cmac.bytesAt_store4, GcmSiv.le4_le32, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add,
    Offset.add_add, BitVec.add_zero]
  simp only [List.append_assoc]

/-- After `i` blocks of `deriveBuild` from `σ`. -/
structure BInv (c : Cx) (σ : State) (i : Nat) (t : State) : Prop where
  env : Env c t
  pk : PK σ t
  s11 : t.gpr .s11 = BitVec.ofNat 64 i
  a5 : t.gpr .a5 = kbP c.W i
  a2 : t.gpr .a2 = BitVec.ofNat 64 (cnt c - i)
  le : i ≤ cnt c
  frame : Frame [⟨c.W + BitVec.ofNat 64 496, 1024⟩] σ.mem t.mem
  blk : ∀ l < i, bytesAt t.mem (kbP c.W l) 16 = Spec.GcmSiv.le32 l ++ bytesAt σ.mem (nP c.W) 12

/-- The nonce's copy, apart from the blocks. -/
theorem nonce_blocks {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame [⟨c.W + BitVec.ofNat 64 496, 1024⟩] m m') :
    bytesAt m' (nP c.W) 12 = bytesAt m (nP c.W) 12 :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
    (by decide)

theorem build0_wp {c : Cx} (L : Lay c) {σ : State} (E : Env c σ) :
    WP isa (.block [.li .s11 0, .addi .a5 .s0 (revO : Int), .shift .srl .d .a2 .s3 1, .addi .a2 .a2 (-1)]) σ
      (BInv c σ 0) := by
  have hc := cnt_bounds L
  have hR := L.rounds
  refine wp_li (by decide) fun t₁ u₁ => wp_addi (imm := revO) (by decide) fun t₂ u₂ =>
    wp_srl (by decide) fun t₃ u₃ => wp_subi (imm := 1) (by decide) fun t₄ u₄ => WP.block_nil ?_
  have pk : PK σ t₄ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)))
  refine ⟨E.of_pk pk, pk, ?_, ?_, ?_, Nat.zero_le _, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s0]; rfl
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s3,
      ofNat_lsr 1 (by rcases L.rounds with h | h <;> rw [h] <;> decide), ofNat_sub (by omega) (by omega),
      Nat.pow_one, Nat.sub_zero]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _

/-- A block of `deriveBuild`. -/
theorem buildStep_wp {c : Cx} (L : Lay c) {σ : State} {i : Nat} (hi : i < cnt c) {t : State}
    (I : BInv c σ i t) : WP isa (.block deriveBody) t (BInv c σ (i + 1)) := by
  have hc := cnt_bounds L
  have hw := L.ww
  have E := I.env
  have hP : 496 + 16 * i + 16 ≤ 1520 := by omega
  unfold deriveBody nO
  refine wp_lwu (a := nP c.W + BitVec.ofNat 64 0) (by decide) (by rw [E.s0, nP, Offset.add_add])
    (by rw [nP, Offset.add_add]; exact L.wal4 (by decide) (by decide))
    (by rw [nP, Offset.add_add]; exact E.perm.wR (by decide)) fun t₁ u₁ => ?_
  refine wp_lwu (a := nP c.W + BitVec.ofNat 64 4) (by decide) (by rw [u₁.other _ (by decide), E.s0, nP, Offset.add_add])
    (by rw [nP, Offset.add_add]; exact L.wal4 (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr, nP, Offset.add_add]; exact E.perm.wR (by decide)) fun t₂ u₂ => ?_
  refine wp_lwu (a := nP c.W + BitVec.ofNat 64 8) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.s0, nP, Offset.add_add])
    (by rw [nP, Offset.add_add]; exact L.wal4 (by decide) (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, nP, Offset.add_add]; exact E.perm.wR (by decide)) fun t₃ u₃ => ?_
  have g₃ : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a3 → t₃.gpr r = t.gpr r := fun r h0 h1 h3 => by
    rw [u₃.other _ h3, u₂.other _ h1, u₁.other _ h0]
  have wr₃ : t₃.wr = t.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have a5₃ : t₃.gpr .a5 = kbP c.W i := by rw [g₃ _ (by decide) (by decide) (by decide), I.a5]
  refine wp_sw (a := kbP c.W i) (by decide) (by rw [a5₃, BitVec.add_zero])
    (L.wal4 (by omega) (by omega)) (by rw [wr₃]; exact E.perm.wW (by omega)) fun t₄ u₄ => ?_
  refine wp_sw (a := kbP c.W i + BitVec.ofNat 64 4) (by decide) (by rw [u₄.gpr, a5₃])
    (by rw [Offset.add_add]; exact L.wal4 (by omega) (by omega))
    (by rw [u₄.wr, wr₃, Offset.add_add]; exact E.perm.wW (by omega)) fun t₅ u₅ => ?_
  refine wp_sw (a := kbP c.W i + BitVec.ofNat 64 8) (by decide) (by rw [u₅.gpr, u₄.gpr, a5₃])
    (by rw [Offset.add_add]; exact L.wal4 (by omega) (by omega))
    (by rw [u₅.wr, u₄.wr, wr₃, Offset.add_add]; exact E.perm.wW (by omega)) fun t₆ u₆ => ?_
  refine wp_sw (a := kbP c.W i + BitVec.ofNat 64 12) (by decide) (by rw [u₆.gpr, u₅.gpr, u₄.gpr, a5₃])
    (by rw [Offset.add_add]; exact L.wal4 (by omega) (by omega))
    (by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, Offset.add_add]; exact E.perm.wW (by omega)) fun t₇ u₇ => ?_
  refine wp_addi (imm := 1) (by decide) fun t₈ u₈ => wp_addi (imm := 16) (by decide) fun t₉ u₉ =>
    wp_subi (imm := 1) (by decide) fun t₁₀ u₁₀ => WP.block_nil ?_
  have pk : PK t t₁₀ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofMupd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofMupd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans (PK.ofUpd u₁₀)))))))))
  have g₇ : t₇.gpr = t₃.gpr := by rw [u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr]
  have hm : t₁₀.mem = bldMem t.mem (kbP c.W i) c.W i := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.gpr,
      u₃.other .a1 (by decide), u₃.other .a0 (by decide), u₃.other .s11 (by decide), u₃.mem, u₂.gpr,
      u₂.other .a0 (by decide), u₂.other .s11 (by decide), u₂.mem, u₁.gpr, u₁.other .s11 (by decide), u₁.mem,
      I.s11, setWidth_32_64, setWidth_32_64, setWidth_32_64]
    rfl
  have fS : Frame [⟨kbP c.W i, 16⟩] t.mem t₁₀.mem := by rw [hm]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine ⟨E.of_pk pk, I.pk.trans pk, ?_, ?_, ?_, by omega, ?_, fun l hl => ?_⟩
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, g₇, g₃ _ (by decide) (by decide) (by decide),
      I.s11, ofNat_add]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), g₇, a5₃, Offset.add_add,
      show 496 + 16 * i + 16 = 496 + 16 * (i + 1) by omega]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), g₇, g₃ _ (by decide) (by decide) (by decide),
      I.a2, ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · exact I.frame.trans (fS.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩)
  · by_cases e : l = i
    · subst e
      rw [hm, bldMem_bytes, nonce_blocks L I.frame]
    · rw [Proof.Cmac.bytesAt_frame fS (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.w_w (.inl (by omega)) (by omega) (by omega)) (by decide)]
      exact I.blk l (by omega)

/-- `deriveBuild`: the blocks `little_endian_uint32(i) ‖ nonce`. -/
theorem build_wp {c : Cx} (L : Lay c) {σ : State} (E : Env c σ) : WP isa deriveBuild σ (BInv c σ (cnt c)) := by
  have hc := cnt_bounds L
  unfold deriveBuild
  refine WP.seq (WP.mono (build0_wp L E) fun t₀ I₀ => ?_)
  refine WP.loop (M := isa) (fun m t => ∃ i, m = cnt c - i ∧ i < cnt c ∧ BInv c σ i t) ?_
    (cnt c - 0) _ ⟨0, rfl, by omega, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (buildStep_wp L hi I) fun t' I' => ?_
  have ev := Steps.eval_nonzero_ofNat _ _ (by omega) I'.a2
  by_cases he : i + 1 = cnt c
  · left; exact ⟨ev.trans (by simp; omega), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp; omega), cnt c - (i + 1), by omega, i + 1, rfl, by omega, I'⟩

/-! ## The call -/

theorem stateAt_ofFn (m : Mem) (p : Addr) :
    Spec.Aes.stateAt m p = Vector.ofFn fun i => (bytesAt m p 16).getD i.1 0 := by
  apply Vector.ext
  intro i hi
  simp [Spec.Aes.stateAt, bytesAt, List.getD_eq_getElem?_getD]

/-- A block `vg_aes_encrypt_blocks` replaced: the cipher of the old one. -/
theorem bytesAt_cipher {m m' : Mem} {D : Addr} {k : Nat} {R : Nat} {w : List Byte}
    (h : Spec.Aes.statesAt m' D k = (Spec.Aes.statesAt m D k).map (Spec.Aes.cipher R w)) {l : Nat} (hl : l < k) :
    bytesAt m' (D + BitVec.ofNat 64 (16 * l)) 16 =
      Spec.GcmSiv.aesWith R w (bytesAt m (D + BitVec.ofNat 64 (16 * l)) 16) := by
  rw [Proof.Ocb.bytesAt_toList, Proof.Ocb.stateAt_of_statesAt h hl, stateAt_ofFn]
  rfl

/-- What the call leaves: the ciphers of the blocks. -/
structure CallOut (c : Cx) (σ t : State) : Prop where
  env : Env c t
  pk : PK σ t
  s11 : t.gpr .s11 = BitVec.ofNat 64 (cnt c)
  frame : Frame [⟨c.W + BitVec.ofNat 64 496, 1024⟩, ⟨c.W + BitVec.ofNat 64 1792, 2048⟩] σ.mem t.mem
  blk : ∀ l < cnt c, bytesAt t.mem (kbP c.W l) 16 =
    Spec.GcmSiv.ctxCiph σ.mem c.K c.R (Spec.GcmSiv.le32 l ++ bytesAt σ.mem (nP c.W) 12)

/-- The schedule at `K` is kept by writes into `W`. -/
theorem ciph_k {c : Cx} (L : Lay c) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨c.W, 3840⟩) {m m' : Mem}
    (hf : Frame rs m m') : Spec.GcmSiv.ctxCiph m' c.K c.R = Spec.GcmSiv.ctxCiph m c.K c.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (L.k_w.sub_right (hrs r hr)).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega)]

/-- `deriveArgs`: the arguments of the call. -/
theorem dargs_wp {c : Cx} (L : Lay c) {t : State} (E : Env c t) (h11 : t.gpr .s11 = BitVec.ofNat 64 (cnt c)) :
    WP isa (.block deriveArgs) t fun t₅ => PK t t₅ ∧ t₅.mem = t.mem ∧ t₅.gpr .s11 = t.gpr .s11 ∧
      BCall t₅ c.K (c.W + BitVec.ofNat 64 496) (c.W + BitVec.ofNat 64 1792) c.R (cnt c) := by
  have hc := cnt_bounds L
  unfold deriveArgs
  refine wp_mv fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_addi (imm := revO) (by decide) fun t₃ u₃ =>
    wp_mv fun t₄ u₄ => wp_addi (imm := scrO) (by decide) fun t₅ u₅ => WP.block_nil ?_
  have pk : PK t t₅ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    (PK.ofUpd u₅))))
  have E₅ := E.of_pk pk
  refine ⟨pk, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)],
    bargs L E₅ E₅.perm.k (k := cnt c) (by omega) (L.k_w' (by omega)) (L.k_w' (by decide)) ?_ ?_ ?_ ?_ ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      E.s2]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide),
      E.s3]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      E.s0]; rfl
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h11]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      E.s0]; rfl

theorem call_wp {c : Cx} (L : Lay c) {σ t : State} (I : BInv c σ (cnt c) t) :
    WP isa (.seq (.block deriveArgs) encCall) t (CallOut c σ) := by
  have hc := cnt_bounds L
  have hw := L.ww
  refine WP.seq (WP.mono (dargs_wp L I.env I.s11) fun t₅ ⟨pk₅, m₅, s11₅, bc⟩ => ?_)
  refine WP.mono (blk_call Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames bc) fun t₆ B => ?_
  have pk₆ : PK t₅ t₆ := PK.ofSaved B.rd B.wr B.sp B.saved
  have fB : Frame [⟨c.W + BitVec.ofNat 64 496, 1024⟩, ⟨c.W + BitVec.ofNat 64 1792, 2048⟩] t₅.mem t₆.mem :=
    B.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  have hk : Spec.GcmSiv.ctxCiph t₅.mem c.K c.R = Spec.GcmSiv.ctxCiph σ.mem c.K c.R := by
    rw [m₅]; exact ciph_k L (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.wSub (by decide)) I.frame
  refine ⟨I.env.of_pk (pk₅.trans pk₆), I.pk.trans (pk₅.trans pk₆), ?_, ?_, fun l hl => ?_⟩
  · rw [B.saved _ (by decide), s11₅, I.s11]
  · rw [m₅] at fB
    exact (I.frame.mono fun r hr => by simp at hr; simp [hr]).trans fB
  · have e := bytesAt_cipher B.out hl
    rw [Offset.add_add] at e
    rw [e, m₅, I.blk l hl, ← m₅]
    exact congrFun hk _

/-! ## The halves kept -/

/-- After `j` steps of `deriveKeep`, from `σ` (the start of `derive`) and
`ρ` (after the call). -/
structure KInv (c : Cx) (σ ρ : State) (j : Nat) (t : State) : Prop where
  env : Env c t
  pk : PK ρ t
  s11 : t.gpr .s11 = BitVec.ofNat 64 (cnt c - j)
  a5 : t.gpr .a5 = kbP c.W j
  a1 : t.gpr .a1 = c.W + BitVec.ofNat 64 (16 + 8 * j)
  le : j ≤ cnt c
  frame : Frame [⟨c.W + BitVec.ofNat 64 16, 48⟩] ρ.mem t.mem
  out : bytesAt t.mem (c.W + BitVec.ofNat 64 16) (8 * j) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem c.K c.R) (bytesAt σ.mem (nP c.W) 12) j

theorem keep0_wp {c : Cx} (L : Lay c) {σ ρ : State} (C : CallOut c σ ρ) :
    WP isa (.block [.addi .a5 .s0 (revO : Int), .addi .a1 .s0 (akO : Int)]) ρ (KInv c σ ρ 0) := by
  have hc := cnt_bounds L
  refine wp_addi (imm := revO) (by decide) fun t₁ u₁ => wp_addi (imm := akO) (by decide) fun t₂ u₂ =>
    WP.block_nil ?_
  have pk : PK ρ t₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  refine ⟨C.env.of_pk pk, pk, by rw [u₂.other _ (by decide), u₁.other _ (by decide), C.s11, Nat.sub_zero],
    by rw [u₂.other _ (by decide), u₁.gpr, C.env.s0]; rfl, by rw [u₂.gpr, u₁.other _ (by decide), C.env.s0]; rfl,
    Nat.zero_le _, by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _, ?_⟩
  simp [bytesAt, GcmSiv.halves]

/-- A step of `deriveKeep`. -/
theorem keepStep_wp {c : Cx} (L : Lay c) {σ ρ : State} (C : CallOut c σ ρ) {j : Nat} (hj : j < cnt c) {t : State}
    (I : KInv c σ ρ j t) : WP isa (.block keepBody) t (KInv c σ ρ (j + 1)) := by
  have hc := cnt_bounds L
  have hw := L.ww
  have E := I.env
  unfold keepBody
  refine wp_ld (a := kbP c.W j) (by decide) (by rw [I.a5, BitVec.add_zero]) (L.wal8 (by omega) (by omega))
    (E.perm.wR (by omega)) fun t₁ u₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 (16 + 8 * j)) (by decide)
    (by rw [u₁.other _ (by decide), I.a1, BitVec.add_zero]) (L.wal8 (by omega) (by omega))
    (by rw [u₁.wr]; exact E.perm.wW (by omega)) fun t₂ u₂ => ?_
  refine wp_addi (imm := 16) (by decide) fun t₃ u₃ => wp_addi (imm := 8) (by decide) fun t₄ u₄ =>
    wp_subi (imm := 1) (by decide) fun t₅ u₅ => WP.block_nil ?_
  have pk : PK t t₅ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    (PK.ofUpd u₅))))
  have hm : t₅.mem = t.mem.writeW (c.W + BitVec.ofNat 64 (16 + 8 * j)) (t.mem.readW (kbP c.W j) 64) := by
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]
  have fW : Frame [⟨c.W + BitVec.ofNat 64 (16 + 8 * j), 8⟩] t.mem t₅.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨E.of_pk pk, I.pk.trans pk, ?_, ?_, ?_, by omega, ?_, ?_⟩
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), I.s11,
      ofNat_sub (by omega) (by omega), Nat.sub_sub]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), I.a5,
      Offset.add_add, show 496 + 16 * j + 16 = 496 + 16 * (j + 1) by omega]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), I.a1,
      Offset.add_add, show 16 + 8 * j + 8 = 16 + 8 * (j + 1) by omega]
  · exact I.frame.trans (fW.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩)
  · -- The bytes kept so far, and the first 8 of block `j`.
    have hb : bytesAt t.mem (kbP c.W j) 16 = bytesAt ρ.mem (kbP c.W j) 16 :=
      Proof.Cmac.bytesAt_frame I.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) (by omega) (by decide))
        (by decide)
    have e16 := Proof.Cmac.bytesAt_add t.mem (kbP c.W j) 8 8
    have last : bytesAt t₅.mem (c.W + BitVec.ofNat 64 (16 + 8 * j)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem c.K c.R (Spec.GcmSiv.le32 j ++ bytesAt σ.mem (nP c.W) 12)).take 8 := by
      rw [hm, ← Proof.Cmac.le8_readW, Mem.readW_writeW_self64, Proof.Cmac.le8_readW, ← C.blk j hj, ← hb, e16,
        List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    have keep : bytesAt t₅.mem (c.W + BitVec.ofNat 64 16) (8 * j) = bytesAt t.mem (c.W + BitVec.ofNat 64 16) (8 * j) :=
      Proof.Cmac.bytesAt_frame fW (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega)) (by omega) (by omega))
        (by omega)
    rw [show 8 * (j + 1) = 8 * j + 8 by omega, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      Offset.add_add, last]

/-- `deriveKeep`. -/
theorem keep_wp {c : Cx} (L : Lay c) {σ ρ : State} (C : CallOut c σ ρ) :
    WP isa deriveKeep ρ (KInv c σ ρ (cnt c)) := by
  have hc := cnt_bounds L
  unfold deriveKeep
  refine WP.seq (WP.mono (keep0_wp L C) fun t₀ I₀ => ?_)
  refine WP.loop (M := isa) (fun m t => ∃ j, m = cnt c - j ∧ j < cnt c ∧ KInv c σ ρ j t) ?_
    (cnt c - 0) _ ⟨0, rfl, by omega, I₀⟩
  rintro m t ⟨j, rfl, hj, I⟩
  refine WP.mono (keepStep_wp L C hj I) fun t' I' => ?_
  have ev := Steps.eval_nonzero_ofNat _ _ (by omega) I'.s11
  by_cases he : j + 1 = cnt c
  · left; exact ⟨ev.trans (by simp; omega), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp; omega), cnt c - (j + 1), by omega, j + 1, rfl, by omega, I'⟩

/-! ## `derive` -/

/-- What `derive` writes. -/
abbrev derR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 496, 1024⟩, ⟨W + BitVec.ofNat 64 1792, 2048⟩]

/-- Buffers apart from `W` are kept by `derive`. -/
theorem bytesAt_derR {c : Cx} {P : Addr} {len : Nat} (hP : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 3840⟩)
    (hl : len ≤ 2 ^ 64) {m m' : Mem} (hf : Frame (derR c.W) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hP.sub_right (Lay.wSub (by decide))) hl

/-- The nonce's copy is kept by `derive`. -/
theorem bytesAt_derN {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (derR c.W) m m') :
    bytesAt m' (nP c.W) 12 = bytesAt m (nP c.W) 12 :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact L.w_w (by decide) (by decide) (by decide)) (by decide)

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (derR c.W) m m') :
    Spec.GcmSiv.ctxCiph m' c.K c.R = Spec.GcmSiv.ctxCiph m c.K c.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_derR (L.k_w.sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega) hf]

/-- What `derive` leaves, from `σ`: the halves of `derive_keys` at `W + 16`. -/
structure DOut (c : Cx) (σ t : State) : Prop where
  env : Env c t
  pk : PK σ t
  frame : Frame (derR c.W) σ.mem t.mem
  out : bytesAt t.mem (c.W + BitVec.ofNat 64 16) (8 * cnt c) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem c.K c.R) (bytesAt σ.mem (nP c.W) 12) (cnt c)

theorem derive_wp {c : Cx} (L : Lay c) {σ : State} (E : Env c σ) : WP isa derive σ (DOut c σ) := by
  unfold derive
  refine WP.seq (WP.mono (build_wp L E) fun t₁ I => ?_)
  refine WP.assoc (WP.seq (WP.mono (call_wp L I) fun ρ C => ?_))
  refine WP.mono (keep_wp L C) fun t K => ⟨K.env, C.pk.trans K.pk, ?_, K.out⟩
  refine ((C.frame.sub fun r hr => ?_).trans (K.frame.sub fun r hr => ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_self, fun _ h => h⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DOut.keys {c : Cx} (L : Lay c) {σ t : State} (I : DOut c σ t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem c.K c.R) (Spec.GcmSiv.keyLen c.R) (bytesAt σ.mem (nP c.W) 12) =
      (bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (c.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen c.R)) := by
  have hR := L.rounds
  have hk : Spec.GcmSiv.keyLen c.R / 8 + 2 = cnt c := by unfold Spec.GcmSiv.keyLen cnt; omega
  have hl : 8 * cnt c = 16 + Spec.GcmSiv.keyLen c.R := by unfold Spec.GcmSiv.keyLen cnt; omega
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, Offset.add_add] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem _ c.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.RISCV64
