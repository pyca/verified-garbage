module

import VerifiedGarbage.Proof.AesCcm.RISCV64.Tag
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
import VerifiedGarbage.Proof.AesCcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesCcm.RISCV64.B0
import VerifiedGarbage.Proof.AesCcm.RISCV64.Callee
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp

/-!
# AES-CCM on RISCV64: a chunk of counter mode (`ctrChunk`)

Untrusted: everything here is checked by Lean. After `b` whole blocks
(`CtrInv`), `ctrChunk` encrypts `k = min (n/16 − b, 2³² − (1 + b) mod 2³²)`
more by `vg_aes_ctr32` from `Ctr₁₊ᵦ`, whose counters do not wrap around in
their low 32 bits, so that they are CCM's (`chunk_wp`), as on AArch64.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Proof.AesCtr.RISCV64 (CtrPost ctr_call)
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (xorFrom xorFrom_append repeat_inc32_ctrBlock ctr32_ccm length_bytesAt bytesAt_prefix
  bytesAt_suffix)

/-- What `ctr` writes: `Ctrⱼ` and the keystream block at `W + 64`, the
working space of the functions called and the data. -/
abbrev crR (c : Cx) : List Region :=
  [⟨c.W + BitVec.ofNat 64 64, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩, ⟨c.D, c.n⟩]

theorem crR_mut (c : Cx) : ∀ r ∈ crR c, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)
  · exact sub_data

/-- The parts of `W` that `ctr` does not write. -/
theorem crR_disj {c : Cx} (L : Lay c) {d k : Nat} (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 384)) :
    ∀ r ∈ crR c, (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.w_w (by omega) (by omega) (by decide)
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.d_w' (by omega)).symm

theorem ciph_crR {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (crR c) m m') :
    Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R :=
  ciph_mut L (hf.sub (crR_mut c))

/-- The state of `ctr` after `b` whole blocks, from the state `s` it
started from: those encrypted, the rest of the data as it was. -/
structure CtrInv (c : Cx) (nonce : List Byte) (s : State) (b : Nat) (t : State) : Prop where
  pk : PK s t
  s5 : t.gpr .s5 = c.D + BitVec.ofNat 64 (16 * b)
  s6 : t.gpr .s6 = BitVec.ofNat 64 (c.n / 16 - b)
  s7 : t.gpr .s7 = BitVec.ofNat 64 (1 + b)
  le : b ≤ c.n / 16
  frame : Frame (crR c) s.mem t.mem
  done : bytesAt t.mem c.D (16 * b) = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D (16 * b))
  rest : bytesAt t.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.n - 16 * b) =
    bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.n - 16 * b)

theorem low32 (x : Nat) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x <<< 32) >>> 32 = BitVec.ofNat 64 (x % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := x % 2 ^ 32) (by omega)]
  rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide : 0 < 2 ^ 32)]

/-- `k = min (m, 2³² − (1 + b) mod 2³²)` in `s8`, for `m` blocks left. -/
theorem kSel_wp {t : State} {m b : Nat} (hs6 : t.gpr .s6 = BitVec.ofNat 64 m)
    (hs7 : t.gpr .s7 = BitVec.ofNat 64 (1 + b)) (hm : m < 2 ^ 60) (hb : 1 + b < 2 ^ 64) :
    WP isa (.seq (.block [.shift .sll .d .t1 .s7 32, .shift .srl .d .t1 .t1 32, .li .t2 1,
        .shift .sll .d .t2 .t2 32, .sub .t2 .t2 .t1, .sltu .t1 .s6 .t2])
      (.ite (.zero .t1) (.block [mov .s8 .t2]) (.block [mov .s8 .s6]))) t fun t₂ =>
      t₂.gpr .s8 = BitVec.ofNat 64 (min m (2 ^ 32 - (1 + b) % 2 ^ 32)) ∧ PK t t₂ ∧ t₂.mem = t.mem ∧
        ∀ r ∈ [Reg.s5, .s6, .s7], t₂.gpr r = t.gpr r := by
  have hj := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide)
  refine WP.seq (wp_sll (by decide) fun t₁ u₁ => wp_srl (by decide) fun t₂ u₂ => wp_li (imm := 1) (by decide)
    fun t₃ u₃ => wp_sll (by decide) fun t₄ u₄ => wp_sub fun t₅ u₅ => wp_sltu fun t₆ u₆ => WP.block_nil ?_)
  have pk₆ : PK t t₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have m₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have t2₅ : t₅.gpr .t2 = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) := by
    rw [u₅.gpr, u₄.gpr, u₄.other .t1 (by decide), u₃.gpr, u₃.other .t1 (by decide), u₂.gpr, u₁.gpr, hs7,
      low32 _ hb, show (BitVec.ofNat 64 1 <<< 32 : BitVec 64) = BitVec.ofNat 64 (2 ^ 32) by decide,
      ofNat_sub_ofNat' (by omega) (by decide)]
  have t2₆ : t₆.gpr .t2 = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) := by
    rw [u₆.other _ (by decide), t2₅]
  have s6₅ : t₅.gpr .s6 = BitVec.ofNat 64 m := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hs6]
  have s6₆ : t₆.gpr .s6 = BitVec.ofNat 64 m := by rw [u₆.other _ (by decide), s6₅]
  have t1₆ : t₆.gpr .t1 = BitVec.ofNat 64 (if m < 2 ^ 32 - (1 + b) % 2 ^ 32 then 1 else 0) := by
    rw [u₆.gpr, t2₅, s6₅, ofNat_ult (by omega) (by omega)]
  have k₆ : ∀ r ∈ [Reg.s5, .s6, .s7], t₆.gpr r = t.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine WP.ite (decide ((if m < 2 ^ 32 - (1 + b) % 2 ^ 32 then 1 else 0) = 0)) (eval_z t1₆ (by split <;> decide))
    (fun ht => ?_) (fun hf => ?_)
  · have hge : ¬ m < 2 ^ 32 - (1 + b) % 2 ^ 32 := by have := of_decide_eq_true ht; split at this <;> simp_all
    refine wp_mv fun t₈ u₈ => WP.block_nil ⟨?_, pk₆.trans (PK.ofUpd u₈), by rw [u₈.mem, m₆], fun r hr => ?_⟩
    · rw [u₈.gpr, t2₆, Nat.min_eq_right (by omega)]
    · have h1 : r ≠ .s8 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
      rw [u₈.other _ h1, k₆ r hr]
  · have hlt : m < 2 ^ 32 - (1 + b) % 2 ^ 32 := by have := of_decide_eq_false hf; split at this <;> simp_all
    refine wp_mv fun t₈ u₈ => WP.block_nil ⟨?_, pk₆.trans (PK.ofUpd u₈), by rw [u₈.mem, m₆], fun r hr => ?_⟩
    · rw [u₈.gpr, s6₆, Nat.min_eq_left (by omega)]
    · have h1 : r ≠ .s8 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
      rw [u₈.other _ h1, k₆ r hr]

/-- The state after a chunk of `k` blocks. -/
theorem chunk_inv {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} {b k : Nat}
    {t : State} (I : CtrInv c nonce s b t) (hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32) (hkb : b + k ≤ c.n / 16)
    {t₅ t₆ t₇ : State} (f₅ : Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] t.mem t₅.mem)
    (hc₅ : bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b))
    (h : CtrPost t₅ c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384) c.R k t₆)
    (hm₇ : t₇.mem = t₆.mem) :
    Frame (crR c) s.mem t₇.mem ∧
      bytesAt t₇.mem c.D (16 * (b + k)) =
        xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D (16 * (b + k))) ∧
      bytesAt t₇.mem (c.D + BitVec.ofNat 64 (16 * (b + k))) (c.n - 16 * (b + k)) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (b + k))) (c.n - 16 * (b + k)) := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  have hDn := L.dw
  have cR : Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩, ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩] t.mem t₇.mem := by
    rw [hm₇]
    refine (f₅.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have toR : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], ∃ r' ∈ crR c, Region.Sub r r' := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega)⟩
    · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  -- Separation of the data from what the chunk wrote.
  have sep : ∀ {a l : Nat}, (a + l ≤ 16 * b ∨ 16 * (b + k) ≤ a) → a + l ≤ c.n →
      ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
        ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l ha hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
    · exact Offset.disjoint c.D (by omega) (by omega) (by omega)
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  have hbk : 16 * (b + k) = 16 * b + 16 * k := Nat.mul_add _ _ _
  refine ⟨I.frame.trans (cR.sub toR), ?_, ?_⟩
  · -- The blocks done.
    have h₁ : bytesAt t₇.mem c.D (16 * b) = bytesAt t.mem c.D (16 * b) := by
      have := Proof.Cmac.bytesAt_frame cR (sep (a := 0) (l := 16 * b) (.inl (by omega)) (by omega)) (by omega)
      rwa [BitVec.add_zero] at this
    have hinc : ∀ i < k, Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt t₅.mem (c.W + BitVec.ofNat 64 64)) =
        Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce (1 + b + i)) := fun i hi => by
      show Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.ofBytes (bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16)) = _
      rw [hc₅]
      exact repeat_inc32_ctrBlock (by rw [hnl]; exact L.h7) (by rw [hnl]; exact L.h13) hk32
        (by rw [hnl]; have := Nat.lt_of_le_of_lt (Nat.div_le_self c.n 16) L.hn; omega) i hi
    have hx := ctr32_ccm (by rw [hnl]; have := L.h13; omega) hinc h.out
    have f₅' : Frame (crR c) s.mem t₅.mem := I.frame.trans (f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩)
    have hx₅ : bytesAt t₅.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) := by
      rw [bytesAt_prefix t₅.mem _ (show 16 * k ≤ c.n - 16 * b by omega),
        bytesAt_prefix s.mem _ (show 16 * k ≤ c.n - 16 * b by omega), ← I.rest,
        Proof.Cmac.bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (L.d_w.sub_left (Offset.sub_base c.D (by omega))).sub_right (Lay.wSub (by decide))) (by omega)]
    rw [hbk, Proof.Cmac.Stream.bytesAt_append, Proof.Cmac.Stream.bytesAt_append, h₁, I.done, hm₇, hx, hx₅,
      ciph_crR L f₅', xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 b]
  · -- The rest of the data.
    have hR' := Proof.Cmac.bytesAt_frame cR
      (sep (a := 16 * (b + k)) (l := c.n - 16 * (b + k)) (.inr (Nat.le_refl _)) (by omega)) (by omega)
    rw [hR', show c.D + BitVec.ofNat 64 (16 * (b + k)) = c.D + BitVec.ofNat 64 (16 * b) + BitVec.ofNat 64 (16 * k) by
        rw [Offset.add_add, hbk],
      show c.n - 16 * (b + k) = c.n - 16 * b - 16 * k by omega, bytesAt_suffix _ _ (show 16 * k ≤ c.n - 16 * b by omega),
      bytesAt_suffix _ _ (show 16 * k ≤ c.n - 16 * b by omega), I.rest]

/-- One chunk. -/
theorem chunk_wp {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} (E : Env c s)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {b : Nat}
    {t : State} (I : CtrInv c nonce s b t) (hb : b < c.n / 16) :
    WP isa ctrChunk t fun t' => ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) ∧ 1 ≤ k ∧
      b + k ≤ c.n / 16 ∧ CtrInv c nonce s (b + k) t' := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  unfold ctrChunk
  refine WP.assoc (WP.seq (WP.mono (kSel_wp (b := b) I.s6 I.s7 (by omega) (by omega))
    fun t₂ ⟨s8₂, pk₂, m₂, k₂⟩ => ?_))
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at s8₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega
  have hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32 := by
    rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega
  have pkt₂ : PK s t₂ := I.pk.trans pk₂
  have E₂ := E.of_pk pkt₂
  have hc0t : bytesAt t₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [m₂, Proof.Cmac.bytesAt_frame I.frame (crR_disj L (.inl (by decide))) (by decide), hc0]
  have hi : 1 + b < 256 ^ (15 - c.nl) := by have := Nat.lt_of_le_of_lt (Nat.div_le_self c.n 16) L.hn; omega
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_mv fun t₃ u₃ => ?_)
  refine ctrAt_wp L (E₂.of_pk (PK.ofUpd u₃)) hnl (by rw [u₃.mem]; exact hc0t) hi
    (by rw [u₃.gpr, k₂ .s7 (by simp), I.s7]) fun t₄ pk₄ kp₄ f₄ hc₄ => ?_
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₅ u₅ => wp_mv fun t₆ u₆ => wp_addi (by decide) fun t₇ u₇ =>
    wp_addi (by decide) fun t₈ u₈ => wp_mv fun t₉ u₉ => wp_mv fun t₁₀ u₁₀ => WP.block_nil ?_
  have pk₁₀ : PK t₄ t₁₀ := (PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans (PK.ofUpd u₁₀)))))
  have pkA : PK s t₁₀ := pkt₂.trans ((PK.ofUpd u₃).trans (pk₄.trans pk₁₀))
  have E₁₀ := E.of_pk pkA
  have m₁₀ : t₁₀.mem = t₄.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  -- The registers the pieces take, kept since `t₂`.
  have kr : ∀ r ∈ [Reg.s5, .s6, .s7, .s8], t₄.gpr r = t₂.gpr r := fun r hr => by
    have h9 : r ≠ .t3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [kp₄ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp [h]),
      u₃.other _ h9]
  have hB := (L.bufD E₁₀.perm).drop (k := 16 * b) (by omega)
  have hQ := hB.take (k := 16 * k) (by omega)
  have C := cargs L E₁₀ (o := 64) (by decide) (Q := c.D + BitVec.ofNat 64 (16 * b)) (k := k) hQ.src
    (hQ.wd (by decide)) (L.k_d.sub_right (Offset.sub_base c.D (by omega)))
    (covers_off E₁₀.perm.d (by omega) hn64)
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.gpr, (pkt₂.trans ((PK.ofUpd u₃).trans pk₄)).gpr .s3 (by decide), E.s3])
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.gpr, u₅.other _ (by decide), (pkt₂.trans ((PK.ofUpd u₃).trans pk₄)).gpr .s4 (by decide), E.s4])
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), u₅.other _ (by decide), (pkt₂.trans ((PK.ofUpd u₃).trans pk₄)).gpr .s1 (by decide),
      E.s1]; rfl)
    (by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), kr .s5 (by simp), k₂ .s5 (by simp), I.s5])
    (by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), kr .s8 (by simp), s8₂])
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), (pkt₂.trans ((PK.ofUpd u₃).trans pk₄)).gpr .s1 (by decide),
      E.s1]; rfl)
  refine WP.seq (WP.mono (ctr_call C) fun t₁₁ h => ?_)
  have sv : ∀ r ∈ [Reg.s5, .s6, .s7, .s8], t₁₁.gpr r = t₂.gpr r := fun r hr => by
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    have h1 : r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a5 ∧ r ≠ .a3 ∧ r ≠ .a4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [h.saved _ hp, u₁₀.other _ h1.2.2.2.2.2, u₉.other _ h1.2.2.2.2.1, u₈.other _ h1.2.2.2.1,
      u₇.other _ h1.2.2.1, u₆.other _ h1.2.1, u₅.other _ h1.1, kr r hr]
  refine wp_sub fun t₁₂ u₁₂ => wp_add fun t₁₃ u₁₃ => wp_sll (by decide) fun t₁₄ u₁₄ => wp_add fun t₁₅ u₁₅ =>
    WP.block_nil ⟨k, hk, hk1, hkb, ?_⟩
  have m₁₅ : t₁₅.mem = t₁₁.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem]
  have f₄' : Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] t.mem t₁₀.mem := by
    rw [m₁₀, ← m₂, ← u₃.mem]; exact f₄
  obtain ⟨fr, dn, rs⟩ := chunk_inv L hnl I hk32 hkb f₄' (by rw [m₁₀]; exact hc₄) h m₁₅
  have s8₁₁ : t₁₁.gpr .s8 = BitVec.ofNat 64 k := by rw [sv .s8 (by simp), s8₂]
  refine ⟨pkA.trans ((PK.ofSaved h.rd h.wr h.sp h.saved).trans ((PK.ofUpd u₁₂).trans ((PK.ofUpd u₁₃).trans
    ((PK.ofUpd u₁₄).trans (PK.ofUpd u₁₅))))), ?_, ?_, ?_, hkb, fr, dn, rs⟩
  · rw [u₁₅.gpr, u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), s8₁₁, u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₂.other _ (by decide), sv .s5 (by simp), k₂ .s5 (by simp), I.s5,
      ofNat_lsl4 (by omega), Offset.add_add, Nat.mul_add]
  · rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, s8₁₁,
      sv .s6 (by simp), k₂ .s6 (by simp), I.s6, ofNat_sub_ofNat' (by omega) (by omega), Nat.sub_sub]
  · rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other .s7 (by decide),
      u₁₂.other .s8 (by decide), s8₁₁, sv .s7 (by simp), k₂ .s7 (by simp), I.s7, BitVec.ofNat_add_ofNat,
      Nat.add_assoc]

end VG.Proof.AesCcm.RISCV64
