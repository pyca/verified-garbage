module

import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Wp
public import VerifiedGarbage.Proof.GcmSiv.Spec
public import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.AesGcmSiv.RISCV64
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.AesGcmSiv.RISCV64.Env
public import VerifiedGarbage.Spec.Gcm

/-!
# AES-GCM-SIV on RISC-V: the message keys (`derive`)

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Derive.lean`), with the nonce read from its copy
at `W + 1520`: each step of `derive` writes
`little_endian_uint32(i) ‖ nonce` at `W + 112` and a zero block at
`W + 240` (`derBlock_wp`), on which `vg_aes_ctr32` leaves
`CIPH_K(little_endian_uint32(i) ‖ nonce)`, of which the first 8 bytes are
kept at `W + 16 + 8 i` (`derPost_wp`): after the loop, the halves of
`derive_keys` (`derive_wp`, `DInv.keys`).
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.Impl.AesGcmSiv.RISCV64 VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_addi wp_li wp_ld wp_sd wp_lwu wp_sw wp_sll wp_srl wp_add wp_sub wp_subi
  wp_mv)
open VG.Proof.AesGcm.RISCV64 (CtrCall CtrPost ctr_call)
open VG.Spec.Aes (bytesAt)

/-- The memory after a step's block: the counter block and a zero block. -/
def derMem (m : Mem) (W : Addr) (i : Nat) : Mem :=
  Proof.Cmac.zero2 (Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) ((BitVec.ofNat 64 i).setWidth 32)
    (m.readW (nP W + BitVec.ofNat 64 0) 32) (m.readW (nP W + BitVec.ofNat 64 4) 32)
    (m.readW (nP W + BitVec.ofNat 64 8) 32))
    (W + BitVec.ofNat 64 240)

/-- The block of a step: the counter block, a zero block, and the arguments of
`vg_aes_ctr32` with the key-generating key's schedule. -/
theorem derBlock_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {i : Nat}
    (h25 : s.gpr .s11 = BitVec.ofNat 64 i) :
    WP isa (.block deriveBlock) s fun s' => PK s s' ∧ s'.mem = derMem s.mem c.W i ∧
      s'.gpr .a0 = c.K ∧ s'.gpr .a1 = BitVec.ofNat 64 c.R ∧ s'.gpr .a2 = c.W + BitVec.ofNat 64 112 ∧
      s'.gpr .a3 = c.W + BitVec.ofNat 64 240 ∧ s'.gpr .a4 = BitVec.ofNat 64 1 ∧
      s'.gpr .a5 = c.W + BitVec.ofNat 64 1792 ∧ s'.gpr .s11 = s.gpr .s11 := by
  unfold deriveBlock zero16 nO ccO bO scrO
  simp only [List.cons_append, List.nil_append]
  refine wp_lwu (a := nP c.W + BitVec.ofNat 64 0) (by decide) (by rw [E.s0, nP, Offset.add_add])
    (by rw [nP, Offset.add_add]; exact L.wal4 (by decide) (by decide)) (by rw [nP, Offset.add_add]; exact E.perm.wR (by decide))
    fun s₁ u₁ => ?_
  refine wp_lwu (a := nP c.W + BitVec.ofNat 64 4) (by decide) (by rw [u₁.other _ (by decide), E.s0, nP, Offset.add_add])
    (by rw [nP, Offset.add_add]; exact L.wal4 (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr, nP, Offset.add_add]; exact E.perm.wR (by decide)) fun s₂ u₂ => ?_
  refine wp_lwu (a := nP c.W + BitVec.ofNat 64 8) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), E.s0, nP, Offset.add_add])
    (by rw [nP, Offset.add_add]; exact L.wal4 (by decide) (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, nP, Offset.add_add]; exact E.perm.wR (by decide)) fun s₃ u₃ => ?_
  have g₃ : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₃.gpr r = s.gpr r := fun r h3 h4 h5 => by
    rw [u₃.other _ h5, u₂.other _ h4, u₁.other _ h3]
  have rw₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have w14 : s₃.gpr .s0 = c.W := by rw [g₃ _ (by decide) (by decide) (by decide), E.s0]
  refine wp_sw (a := c.W + BitVec.ofNat 64 112) (by decide) (by rw [w14]) (L.wal4 (by decide) (by decide))
    (by rw [rw₃]; exact E.perm.wW (by decide)) fun s₄ u₄ => ?_
  refine wp_sw (a := c.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 4) (by decide)
    (by rw [u₄.gpr, w14, Offset.add_add]) (by rw [Offset.add_add]; exact L.wal4 (by decide) (by decide))
    (by rw [u₄.wr, rw₃, Offset.add_add]; exact E.perm.wW (by decide)) fun s₅ u₅ => ?_
  refine wp_sw (a := c.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₅.gpr, u₄.gpr, w14, Offset.add_add]) (by rw [Offset.add_add]; exact L.wal4 (by decide) (by decide))
    (by rw [u₅.wr, u₄.wr, rw₃, Offset.add_add]; exact E.perm.wW (by decide)) fun s₆ u₆ => ?_
  refine wp_sw (a := c.W + BitVec.ofNat 64 112 + BitVec.ofNat 64 12) (by decide)
    (by rw [u₆.gpr, u₅.gpr, u₄.gpr, w14, Offset.add_add]) (by rw [Offset.add_add]; exact L.wal4 (by decide) (by decide))
    (by rw [u₆.wr, u₅.wr, u₄.wr, rw₃, Offset.add_add]; exact E.perm.wW (by decide)) fun s₇ u₇ => ?_
  refine wp_li (by decide) fun s₈ u₈ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 240) (by decide)
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, w14]) (L.wal8 (by decide) (by decide))
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, rw₃]; exact E.perm.wW (by decide)) fun s₉ u₉ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₉.gpr, u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, w14, Offset.add_add])
    (by rw [Offset.add_add]; exact L.wal8 (by decide) (by decide))
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, rw₃, Offset.add_add]; exact E.perm.wW (by decide))
    fun s₁₀ u₁₀ => ?_
  refine wp_mv fun s₁₁ u₁₁ => wp_mv fun s₁₂ u₁₂ => wp_addi (by decide) fun s₁₃ u₁₃ =>
    wp_addi (by decide) fun s₁₄ u₁₄ => wp_li (by decide) fun s₁₅ u₁₅ =>
    wp_addi (by decide) fun s₁₆ u₁₆ => WP.block_nil ?_
  have pk : PK s s₁₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofMupd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofMupd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofMupd u₉).trans
    ((PK.ofMupd u₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans ((PK.ofUpd u₁₃).trans ((PK.ofUpd u₁₄).trans
    ((PK.ofUpd u₁₅).trans (PK.ofUpd u₁₆)))))))))))))))
  have g₁₀ : ∀ r, r ≠ .t0 → s₁₀.gpr r = s₃.gpr r := fun r h0 => by
    rw [u₁₀.gpr, u₉.gpr, u₈.other _ h0, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr]
  have w14' : s₁₀.gpr .s0 = c.W := by rw [g₁₀ _ (by decide), w14]
  refine ⟨pk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.gpr, u₉.mem, u₈.gpr, u₈.mem,
      u₇.mem, u₆.gpr, u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other .a1 (by decide),
      u₃.other .a0 (by decide), u₃.other .s11 (by decide), u₃.mem, u₂.gpr, u₂.other .a0 (by decide),
      u₂.other .s11 (by decide), u₂.mem, u₁.gpr, u₁.other .s11 (by decide), u₁.mem, h25, setWidth_32_64,
      setWidth_32_64, setWidth_32_64]
    rfl
  · rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₁.gpr, g₁₀ _ (by decide), g₃ _ (by decide) (by decide) (by decide), E.s2]
  · rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.gpr, u₁₁.other _ (by decide), g₁₀ _ (by decide), g₃ _ (by decide) (by decide) (by decide), E.s3]
  · rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr,
      u₁₂.other _ (by decide), u₁₁.other _ (by decide), w14']
  · rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₁.other _ (by decide), w14']
  · rw [u₁₆.other _ (by decide), u₁₅.gpr]
  · rw [u₁₆.gpr, u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₁.other _ (by decide), w14']
  · rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
      u₁₂.other _ (by decide), u₁₁.other _ (by decide), g₁₀ _ (by decide), g₃ _ (by decide) (by decide) (by decide)]

theorem derMem_frame (m : Mem) (W : Addr) (i : Nat) :
    Frame [⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 240, 16⟩] m (derMem m W i) :=
  ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self).trans
    ((Proof.Cmac.frame_store2 _ _ _).mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ List.mem_cons_self)

/-- The counter block of a step: `little_endian_uint32(i) ‖ nonce`. -/
theorem derBlock_bytes (m : Mem) (W : Addr) (i : Nat) :
    bytesAt (derMem m W i) (W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt m (nP W) 12 := by
  rw [derMem, Proof.Cmac.zero2, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store2 _ _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide)),
    Proof.Cmac.bytesAt_store4, GcmSiv.le4_le32, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, show (12 : Nat) = 4 + (4 + 4) from rfl, Proof.Cmac.bytesAt_add, Proof.Cmac.bytesAt_add,
    Offset.add_add, BitVec.add_zero]
  simp only [List.append_assoc]

/-- The zero block of a step. -/
theorem derZero_block (W : Addr) (m : Mem) (i : Nat) :
    Spec.Gcm.blockAt (derMem m W i) (W + BitVec.ofNat 64 240) = 0 := by
  rw [derMem, Spec.Gcm.blockAt, Proof.Cmac.zero2_bytes]
  decide

/-- What the code after a step's call writes: the 8 bytes kept. -/
def postMem (m : Mem) (W : Addr) (i : Nat) : Mem :=
  m.writeW (W + BitVec.ofNat 64 (16 + 8 * i)) (m.readW (W + BitVec.ofNat 64 240) 64)

/-- The code after the call of a step. -/
theorem derPost_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {i : Nat} (hi : i < c.R / 2 - 1)
    (h25 : s.gpr .s11 = BitVec.ofNat 64 i) :
    WP isa (.block derivePost) s fun s' => PK s s' ∧ s'.mem = postMem s.mem c.W i ∧
      s'.gpr .s11 = BitVec.ofNat 64 (i + 1) ∧ s'.gpr .a2 = BitVec.ofNat 64 (c.R / 2 - 1 - (i + 1)) := by
  have hR := L.rounds
  have hi6 : i ≤ 5 := by rcases hR with h | h <;> rw [h] at hi <;> omega_arith
  unfold derivePost bO akO
  refine wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [E.s0]) (L.wal8 (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_sll (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => ?_
  have h4 : s₃.gpr .a1 = c.W + BitVec.ofNat 64 (8 * i) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), E.s0, h25,
      ofNat_shl]
  refine wp_sd (a := c.W + BitVec.ofNat 64 (16 + 8 * i)) (by decide)
    (by rw [h4, Offset.add_add, Nat.add_comm]) (L.wal8 (by omega_arith) (by omega_arith))
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by omega_arith)) fun s₄ u₄ => ?_
  refine wp_addi (by decide) fun s₅ u₅ => wp_srl (by decide) fun s₆ u₆ =>
    wp_subi (imm := 1) (by decide) fun s₇ u₇ => wp_sub fun s₈ u₈ => WP.block_nil ?_
  have pk : PK s s₈ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))))
  have s11 : s₈.gpr .s11 = BitVec.ofNat 64 (i + 1) := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h25, ofNat_add]
  refine ⟨pk, ?_, s11, ?_⟩
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.other .a0 (by decide),
      u₂.other .a0 (by decide), u₁.gpr]
    rfl
  · have hR2 : 2 ≤ c.R / 2 - 1 := by rcases hR with h | h <;> rw [h] <;> decide
    have e5 : s₇.gpr .a2 = BitVec.ofNat 64 c.R >>> 1 - BitVec.ofNat 64 1 := by
      rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), E.s3]
    have e25 : s₇.gpr .s11 = BitVec.ofNat 64 (i + 1) := (u₈.other _ (by decide)).symm.trans s11
    rw [u₈.gpr, e5, e25, ofNat_lsr 1 (by rcases hR with h | h <;> rw [h] <;> decide),
      ofNat_sub (by omega_arith) (by omega_arith), ofNat_sub (by omega_arith) (by omega_arith), Nat.pow_one]

theorem postMem_frame (m : Mem) (W : Addr) (i : Nat) :
    Frame [⟨W + BitVec.ofNat 64 (16 + 8 * i), 8⟩] m (postMem m W i) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- The 8 bytes a step keeps: the first 8 of the block at `W + 240`. -/
theorem postMem_bytes (m : Mem) (W : Addr) (i : Nat) :
    bytesAt (postMem m W i) (W + BitVec.ofNat 64 (16 + 8 * i)) 8 = bytesAt m (W + BitVec.ofNat 64 240) 8 := by
  rw [← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, postMem, Mem.readW_writeW_self64]

/-- What `derive` writes. -/
abbrev derR (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 48⟩, ⟨W + BitVec.ofNat 64 112, 16⟩, ⟨W + BitVec.ofNat 64 240, 16⟩,
    ⟨W + BitVec.ofNat 64 1792, 2048⟩]

/-- Buffers apart from `W` are kept by `derive`. -/
theorem bytesAt_derR {c : Cx} {P : Addr} {len : Nat} (hP : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 3840⟩)
    (hl : len ≤ 2 ^ 64) {m m' : Mem} (hf : Frame (derR c.W) m m') : bytesAt m' P len = bytesAt m P len :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hP.sub_right (Lay.wSub (by decide))) hl

/-- The nonce's copy is kept by `derive`. -/
theorem bytesAt_derN {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (derR c.W) m m') :
    bytesAt m' (nP c.W) 12 = bytesAt m (nP c.W) 12 :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact L.w_w (by decide) (by decide) (by decide)) (by decide)

/-- The key schedule is kept by `derive`. -/
theorem ciph_derR {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (derR c.W) m m') :
    Spec.GcmSiv.ctxCiph m' c.K c.R = Spec.GcmSiv.ctxCiph m c.K c.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [bytesAt_derR (L.k_w.sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega_arith) hf]

/-- After `i` steps of `derive` from `σ`: the first `8 i` bytes of the halves
at `W + 16`. -/
structure DInv (c : Cx) (σ : State) (i : Nat) (t : State) : Prop where
  env : Env c t
  pk : PK σ t
  s11 : t.gpr .s11 = BitVec.ofNat 64 i
  le : i ≤ c.R / 2 - 1
  frame : Frame (derR c.W) σ.mem t.mem
  out : bytesAt t.mem (c.W + BitVec.ofNat 64 16) (8 * i) =
    GcmSiv.halves (Spec.GcmSiv.ctxCiph σ.mem c.K c.R) (bytesAt σ.mem (nP c.W) 12) i

/-- A step of `derive`. -/
theorem derStep_wp {c : Cx} (L : Lay c) {σ : State} {i : Nat} (hi : i < c.R / 2 - 1) {t : State}
    (I : DInv c σ i t) :
    WP isa (.seq (.block deriveBlock) (.seq Impl.AesGcm.RISCV64.ctrCall (.block derivePost))) t fun t' =>
      DInv c σ (i + 1) t' ∧ t'.gpr .a2 = BitVec.ofNat 64 (c.R / 2 - 1 - (i + 1)) := by
  have hR := L.rounds
  have hw := L.ww
  have hi6 : i ≤ 5 := by rcases hR with h | h <;> rw [h] at hi <;> omega_arith
  have eN : bytesAt t.mem (nP c.W) 12 = bytesAt σ.mem (nP c.W) 12 := bytesAt_derN L I.frame
  have eK := ciph_derR L I.frame
  refine WP.seq (WP.mono (derBlock_wp L I.env I.s11) fun t₁ ⟨pk₁, hm₁, a0, a1, a2, a3, a4, a5, r25₁⟩ => ?_)
  have E₁ : Env c t₁ := I.env.of_pk pk₁
  have cc : CtrCall t₁ c.K (c.W + BitVec.ofNat 64 112) (c.W + BitVec.ofNat 64 240) (c.W + BitVec.ofNat 64 1792)
      c.R 1 :=
    cargs L E₁ E₁.perm.k (L.k_w' (by decide)) (L.k_w' (by decide)) (L.k_w' (by decide))
      (L.w_w (.inl (by decide)) (by decide) (by decide)) (L.w_w (.inl (by decide)) (by decide) (by decide))
      (E₁.perm.wC (by decide)) (by rw [L.wrapW (by decide)]; omega_arith) (by decide) a0 a1 a2 a3 a4 a5
  have hb₁ : bytesAt t₁.mem (c.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.le32 i ++ bytesAt t.mem (nP c.W) 12 := by
    rw [hm₁]; exact derBlock_bytes _ _ _
  have hz₁ : Spec.Gcm.blockAt t₁.mem (c.W + BitVec.ofNat 64 240) = 0 := by
    rw [hm₁]; exact derZero_block _ _ _
  have f₁ : Frame [⟨c.W + BitVec.ofNat 64 112, 16⟩, ⟨c.W + BitVec.ofNat 64 240, 16⟩] t.mem t₁.mem := by
    rw [hm₁]; exact derMem_frame _ _ _
  refine WP.seq (WP.mono (ctr_call cc) fun t₂ P => ?_)
  have pk₂ : PK t₁ t₂ := PK.ofSaved P.rd P.wr P.sp P.saved
  have E₂ : Env c t₂ := E₁.of_pk pk₂
  have r25₂ : t₂.gpr .s11 = BitVec.ofNat 64 i := by
    rw [P.saved _ (by decide), r25₁, I.s11]
  refine WP.mono (derPost_wp L E₂ hi r25₂) fun t₃ ⟨pk₃, hm₃, r25₃, r5₃⟩ => ⟨⟨E₂.of_pk pk₃,
    I.pk.trans (pk₁.trans (pk₂.trans pk₃)), r25₃, by omega_arith, ?_, ?_⟩, r5₃⟩
  · -- The frame.
    have mem : ∀ {r : Region}, r ∈ derR c.W → ∃ r' ∈ derR c.W, Region.Sub r r' :=
      fun {r} h => ⟨r, h, fun _ h => h⟩
    refine ((I.frame.trans (f₁.sub fun r hr => ?_)).trans (P.frame.sub fun r hr => ?_)).trans ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact mem (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Nat.mul_one] at hr
      rcases hr with rfl | rfl | rfl <;> exact mem (by simp)
    · rw [hm₃]
      exact (postMem_frame _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega_arith) (by omega_arith)⟩
  · -- The bytes.
    have dW : ∀ {d k : Nat}, d + k ≤ 3840 → 16 + 8 * i ≤ d ∨ d + k ≤ 16 →
        (⟨c.W + BitVec.ofNat 64 16, 8 * i⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ h₂ => L.w_w (by omega_arith) (by omega_arith) h₁
    have keep : bytesAt t₃.mem (c.W + BitVec.ofNat 64 16) (8 * i) = bytesAt t.mem (c.W + BitVec.ofNat 64 16) (8 * i) := by
      rw [hm₃, Proof.Cmac.bytesAt_frame (postMem_frame _ _ _)
          (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dW (by omega_arith) (by omega_arith)) (by omega_arith),
        Proof.Cmac.bytesAt_frame P.frame (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact dW (by decide) (by omega_arith)
          · exact dW (by decide) (by omega_arith)
          · exact dW (by decide) (by omega_arith)) (by omega_arith),
        Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact dW (by decide) (by omega_arith)) (by omega_arith)]
    have hout := P.out
    simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
    have last : bytesAt t₃.mem (c.W + BitVec.ofNat 64 (16 + 8 * i)) 8 =
        (Spec.GcmSiv.ctxCiph σ.mem c.K c.R (Spec.GcmSiv.le32 i ++ bytesAt σ.mem (nP c.W) 12)).take 8 := by
      have e16 : bytesAt t₂.mem (c.W + BitVec.ofNat 64 240) 16 =
          bytesAt t₂.mem (c.W + BitVec.ofNat 64 240) 8 ++
            bytesAt t₂.mem (c.W + BitVec.ofNat 64 240 + BitVec.ofNat 64 8) 8 :=
        Proof.Cmac.bytesAt_add _ _ 8 8
      have ek₁ : Spec.GcmSiv.ctxCiph t₁.mem c.K c.R = Spec.GcmSiv.ctxCiph t.mem c.K c.R := by
        unfold Spec.GcmSiv.ctxCiph
        rw [Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb))
          (by have := L.rb; omega_arith)]
      rw [hm₃, postMem_bytes,
        show bytesAt t₂.mem (c.W + BitVec.ofNat 64 240) 8 = (bytesAt t₂.mem (c.W + BitVec.ofNat 64 240) 16).take 8 by
          rw [e16, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)],
        Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt, hb₁,
        Proof.Cmac.aesWith_bytes _ _ (by rw [List.length_append, Proof.Cmac.bytesAt_length]; rfl),
        ← GcmSiv.aesWith_eq, show Spec.GcmSiv.aesWith c.R (bytesAt t₁.mem c.K (16 * (c.R + 1))) =
          Spec.GcmSiv.ctxCiph t₁.mem c.K c.R from rfl, ek₁, eK, eN]
    rw [show 8 * (i + 1) = 8 * i + 8 by omega_arith, Proof.Cmac.bytesAt_add, GcmSiv.halves_succ, ← I.out, keep,
      Offset.add_add, last]

/-- `derive`: the halves of `derive_keys` at `W + 16`. -/
theorem derive_wp {c : Cx} (L : Lay c) {σ : State} (E : Env c σ) :
    WP isa derive σ (DInv c σ (c.R / 2 - 1)) := by
  have hR := L.rounds
  unfold derive
  refine WP.seq (wp_li (by decide) fun t₀ u₀ => WP.block_nil ?_)
  have I₀ : DInv c σ 0 t₀ := ⟨E.of_pk (PK.ofUpd u₀), PK.ofUpd u₀, u₀.gpr, Nat.zero_le _,
    by rw [u₀.mem]; exact Frame.refl _ _, rfl⟩
  refine WP.loop (M := isa) (fun m t => ∃ i, m = (c.R / 2 - 1) - i ∧ i < c.R / 2 - 1 ∧ DInv c σ i t) ?_
    ((c.R / 2 - 1) - 0) _ ⟨0, rfl, by rcases hR with h | h <;> rw [h] <;> decide, I₀⟩
  rintro m t ⟨i, rfl, hi, I⟩
  refine WP.mono (derStep_wp L hi I) fun t' ⟨I', h5⟩ => ?_
  have ev := Steps.eval_nonzero_ofNat _ _ (by rcases hR with h | h <;> rw [h] <;> omega_arith) h5
  by_cases he : i + 1 = c.R / 2 - 1
  · left; exact ⟨ev.trans (by simp [he]), he ▸ I'⟩
  · right; exact ⟨ev.trans (by simp; omega_arith), (c.R / 2 - 1) - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, I'⟩

/-- After `derive`, the message keys: the authentication key at `W + 16`, the
encryption key at `W + 32`. -/
theorem DInv.keys {c : Cx} (L : Lay c) {σ t : State} (I : DInv c σ (c.R / 2 - 1) t) :
    Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph σ.mem c.K c.R) (Spec.GcmSiv.keyLen c.R) (bytesAt σ.mem (nP c.W) 12) =
      (bytesAt t.mem (c.W + BitVec.ofNat 64 16) 16,
        bytesAt t.mem (c.W + BitVec.ofNat 64 32) (Spec.GcmSiv.keyLen c.R)) := by
  have hR := L.rounds
  have hk : Spec.GcmSiv.keyLen c.R / 8 + 2 = c.R / 2 - 1 := by unfold Spec.GcmSiv.keyLen; omega_arith
  have hl : 8 * (c.R / 2 - 1) = 16 + Spec.GcmSiv.keyLen c.R := by unfold Spec.GcmSiv.keyLen; omega_arith
  have e := I.out
  rw [hl, Proof.Cmac.bytesAt_add, Offset.add_add] at e
  rw [GcmSiv.deriveKeys_eq (GcmSiv.ctxCiph_length σ.mem _ c.R), hk, ← e,
    List.take_left' (Proof.Cmac.bytesAt_length _ _ _), List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

end VG.Proof.AesGcmSiv.RISCV64
