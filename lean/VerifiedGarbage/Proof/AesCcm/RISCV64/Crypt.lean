module

import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesCcm.RISCV64.B0
import VerifiedGarbage.Proof.AesCcm.RISCV64.Callee
import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call

/-! ### `AesCcm.RISCV64.Chunk`, which this module and modules that import it used -/

section

/-! ### `AesCcm.RISCV64.Tag`, which this module and modules that import it used -/

section

/-!
# AES-CCM on RISCV64: the MAC encrypted (`tag y`)

Untrusted: everything here is checked by Lean. `tag y` copies `Ctr₀` to
`W + 64` (`ctrAt` with `i = 0`) and calls `vg_aes_ctr32` on the MAC at
`W + y`: it XORs in `CIPH_K(Ctr₀)`, CCM's keystream from `Ctr₀`
(`tag_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Proof.AesCtr.RISCV64 (ctr_call)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (xorFrom)

/-- What `tag y` and a call of `vg_aes_ctr32` from a counter block leave. -/
abbrev ctrR (W : Addr) (y : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 y, 16⟩, ⟨W + BitVec.ofNat 64 384, 2048⟩]

theorem tag_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte} (hnl : nonce.length = c.nl)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (tag y) s fun s' => PK s s' ∧ (∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r) ∧
      Frame (ctrR c.W y) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 y) 16 =
        xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 0 (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16) := by
  unfold tag
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine ctrAt_wp L (E.of_pk (PK.ofUpd u₁)) hnl (by rw [u₁.mem]; exact hc0) (i := 0)
    (Nat.pow_pos (by decide : 0 < 256)) u₁.gpr
    fun s₂ pk₂ k₂ f₂ hc₂ => ?_
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_addi (by decide) fun s₆ u₆ => wp_addi (by omega_using [hy]) fun s₇ u₇ =>
    wp_li (by decide) fun s₈ u₈ => WP.block_nil ?_
  have pk₈ : PK s s₈ := (PK.ofUpd u₁).trans (pk₂.trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))))
  have E₈ := E.of_pk pk₈
  have m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have C := cargsW L E₈ (o := 64) (d := y) (by decide) (by omega_using [hy]) (by omega_using [hy])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, (PK.ofUpd u₁ |>.trans pk₂).gpr .s3 (by decide), E.s3])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), (PK.ofUpd u₁ |>.trans pk₂).gpr .s4 (by decide), E.s4])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), (PK.ofUpd u₁ |>.trans pk₂).gpr .s1 (by decide), E.s1]; rfl)
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), (PK.ofUpd u₁ |>.trans pk₂).gpr .s1 (by decide), E.s1])
    (by rw [u₈.gpr])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), (PK.ofUpd u₁ |>.trans pk₂).gpr .s1 (by decide), E.s1]; rfl)
  refine WP.mono (ctr_call C) fun s₉ h => ⟨pk₈.trans (PK.ofSaved h.rd h.wr h.sp h.saved), fun r hr => ?_, ?_, ?_⟩
  · have h1 : r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a5 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .t3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    have hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [h.saved _ hp, u₈.other _ h1.2.2.2.2.2.1, u₇.other _ h1.2.2.2.2.1, u₆.other _ h1.2.2.2.1,
      u₅.other _ h1.2.2.1, u₄.other _ h1.2.1, u₃.other _ h1.1,
      k₂ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp [h]),
      u₁.other _ h1.2.2.2.2.2.2]
  · rw [u₁.mem] at f₂
    rw [← m₈] at f₂
    refine (f₂.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  · have hx := Proof.AesCcm.ctr32_ccm (nonce := nonce) (k := 1) (j := 0) (by have := L.h13; omega_using [hnl, this])
      (fun i hi => by
        rw [show i = 0 by omega_using [hi], Nat.add_zero]
        show Spec.Gcm.ofBytes _ = _
        rw [m₈, hc₂]) h.out
    rw [Nat.mul_one] at hx
    rw [u₁.mem] at f₂
    have hK : Spec.Ccm.ctxCiph s₈.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by
      unfold Spec.Ccm.ctxCiph
      rw [m₈, Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega_using [this])]
    have hY : bytesAt s₈.mem (c.W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16 := by
      rw [m₈]
      exact Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rcases hy with rfl | rfl
        · exact L.w_w (.inl (by decide)) (by decide) (by decide)
        · exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
    rw [hx, hK, hY]

end VG.Proof.AesCcm.RISCV64

end

end

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
  · exact L.w_w (by omega_using [h]) (by omega_using [h]) (by decide)
  · exact L.w_w (.inl (by omega_using [h])) (by omega_using [h]) (by decide)
  · exact (L.d_w' (by omega_using [h])).symm

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
    Nat.mod_eq_of_lt hx, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (a := x % 2 ^ 32) (by omega_using [])]
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
  obtain hj := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide)
  refine WP.seq (wp_sll (by decide) fun t₁ u₁ => wp_srl (by decide) fun t₂ u₂ => wp_li (imm := 1) (by decide)
    fun t₃ u₃ => wp_sll (by decide) fun t₄ u₄ => wp_sub fun t₅ u₅ => wp_sltu fun t₆ u₆ => WP.block_nil ?_)
  obtain pk₆ : PK t t₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  obtain m₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain t2₅ : t₅.gpr .t2 = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) := by
    rw [u₅.gpr, u₄.gpr, u₄.other .t1 (by decide), u₃.gpr, u₃.other .t1 (by decide), u₂.gpr, u₁.gpr, hs7,
      low32 _ hb, show (BitVec.ofNat 64 1 <<< 32 : BitVec 64) = BitVec.ofNat 64 (2 ^ 32) by decide,
      ofNat_sub_ofNat' (by omega_using []) (by decide)]
  obtain t2₆ : t₆.gpr .t2 = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) := by
    rw [u₆.other _ (by decide), t2₅]
  obtain s6₅ : t₅.gpr .s6 = BitVec.ofNat 64 m := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hs6]
  obtain s6₆ : t₆.gpr .s6 = BitVec.ofNat 64 m := by rw [u₆.other _ (by decide), s6₅]
  obtain t1₆ : t₆.gpr .t1 = BitVec.ofNat 64 (if m < 2 ^ 32 - (1 + b) % 2 ^ 32 then 1 else 0) := by
    rw [u₆.gpr, t2₅, s6₅, ofNat_ult (by omega_using [hm]) (by omega_using [])]
  obtain k₆ : ∀ r ∈ [Reg.s5, .s6, .s7], t₆.gpr r = t.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine WP.ite (decide ((if m < 2 ^ 32 - (1 + b) % 2 ^ 32 then 1 else 0) = 0)) (eval_z t1₆ (by split <;> decide))
    (fun ht => ?_) (fun hf => ?_)
  · have hge : ¬ m < 2 ^ 32 - (1 + b) % 2 ^ 32 := by have := of_decide_eq_true ht; split at this <;> simp_all
    refine wp_mv fun t₈ u₈ => WP.block_nil ⟨?_, pk₆.trans (PK.ofUpd u₈), by rw [u₈.mem, m₆], fun r hr => ?_⟩
    · rw [u₈.gpr, t2₆, Nat.min_eq_right (by omega_using [hge])]
    · have h1 : r ≠ .s8 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide
      rw [u₈.other _ h1, k₆ r hr]
  · have hlt : m < 2 ^ 32 - (1 + b) % 2 ^ 32 := by have := of_decide_eq_false hf; split at this <;> simp_all
    refine wp_mv fun t₈ u₈ => WP.block_nil ⟨?_, pk₆.trans (PK.ofUpd u₈), by rw [u₈.mem, m₆], fun r hr => ?_⟩
    · rw [u₈.gpr, s6₆, Nat.min_eq_left (by omega_using [hlt])]
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
  obtain cR : Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩, ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩] t.mem t₇.mem := by
    rw [hm₇]
    refine (f₅.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  obtain toR : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], ∃ r' ∈ crR c, Region.Sub r r' := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega_using [hkb])⟩
    · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  -- Separation of the data from what the chunk wrote.
  obtain sep : ∀ {a l : Nat}, (a + l ≤ 16 * b ∨ 16 * (b + k) ≤ a) → a + l ≤ c.n →
      ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
        ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l ha hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
    · exact Offset.disjoint c.D (by omega_using [ha]) (by omega_using [hn64, hl]) (by omega_using [hkb, hn64])
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  obtain hbk : 16 * (b + k) = 16 * b + 16 * k := Nat.mul_add _ _ _
  refine ⟨I.frame.trans (cR.sub toR), ?_, ?_⟩
  · -- The blocks done.
    obtain h₁ : bytesAt t₇.mem c.D (16 * b) = bytesAt t.mem c.D (16 * b) := by
      have := Proof.Cmac.bytesAt_frame cR (sep (a := 0) (l := 16 * b) (.inl (by omega_using [])) (by omega_using [hkb])) (by omega_using [hkb, hn64])
      rwa [BitVec.add_zero] at this
    obtain hinc : ∀ i < k, Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt t₅.mem (c.W + BitVec.ofNat 64 64)) =
        Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce (1 + b + i)) := fun i hi => by
      show Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.ofBytes (bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16)) = _
      rw [hc₅]
      exact repeat_inc32_ctrBlock (by rw [hnl]; exact L.h7) (by rw [hnl]; exact L.h13) hk32
        (by rw [hnl]; have := Nat.lt_of_le_of_lt (Nat.div_le_self c.n 16) L.hn; omega_using [hkb, this]) i hi
    obtain hx := ctr32_ccm (by rw [hnl]; have := L.h13; omega_using [this]) hinc h.out
    obtain f₅' : Frame (crR c) s.mem t₅.mem := I.frame.trans (f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩)
    obtain hx₅ : bytesAt t₅.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) := by
      rw [bytesAt_prefix t₅.mem _ (show 16 * k ≤ c.n - 16 * b by omega_using [hkb]),
        bytesAt_prefix s.mem _ (show 16 * k ≤ c.n - 16 * b by omega_using [hkb]), ← I.rest,
        Proof.Cmac.bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (L.d_w.sub_left (Offset.sub_base c.D (by omega_using [hkb]))).sub_right (Lay.wSub (by decide))) (by omega_using [hn64])]
    rw [hbk, Proof.Cmac.Stream.bytesAt_append, Proof.Cmac.Stream.bytesAt_append, h₁, I.done, hm₇, hx, hx₅,
      ciph_crR L f₅', xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 b]
  · -- The rest of the data.
    obtain hR' := Proof.Cmac.bytesAt_frame cR
      (sep (a := 16 * (b + k)) (l := c.n - 16 * (b + k)) (.inr (Nat.le_refl _)) (by omega_using [hkb])) (by omega_using [hn64])
    rw [hR', show c.D + BitVec.ofNat 64 (16 * (b + k)) = c.D + BitVec.ofNat 64 (16 * b) + BitVec.ofNat 64 (16 * k) by
        rw [Offset.add_add, hbk],
      show c.n - 16 * (b + k) = c.n - 16 * b - 16 * k by omega_using [], bytesAt_suffix _ _ (show 16 * k ≤ c.n - 16 * b by omega_using [hkb]),
      bytesAt_suffix _ _ (show 16 * k ≤ c.n - 16 * b by omega_using [hkb]), I.rest]

/-- One chunk. -/
theorem chunk_wp {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} (E : Env c s)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {b : Nat}
    {t : State} (I : CtrInv c nonce s b t) (hb : b < c.n / 16) :
    WP isa ctrChunk t fun t' => ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) ∧ 1 ≤ k ∧
      b + k ≤ c.n / 16 ∧ CtrInv c nonce s (b + k) t' := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  unfold ctrChunk
  refine WP.assoc (WP.seq (WP.mono (kSel_wp (b := b) I.s6 I.s7 (by omega_using [hn64]) (by omega_using [hb, hn64]))
    fun t₂ ⟨s8₂, pk₂, m₂, k₂⟩ => ?_))
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at s8₂
  obtain hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_using [hb]
  obtain hkb : b + k ≤ c.n / 16 := by rw [hk]; omega_using [hb]
  obtain hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32 := by
    rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_using []
  obtain pkt₂ : PK s t₂ := I.pk.trans pk₂
  obtain E₂ := E.of_pk pkt₂
  obtain hc0t : bytesAt t₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [m₂, Proof.Cmac.bytesAt_frame I.frame (crR_disj L (.inl (by decide))) (by decide), hc0]
  obtain hi : 1 + b < 256 ^ (15 - c.nl) := by have := Nat.lt_of_le_of_lt (Nat.div_le_self c.n 16) L.hn; omega_using [hb, this]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_mv fun t₃ u₃ => ?_)
  refine ctrAt_wp L (E₂.of_pk (PK.ofUpd u₃)) hnl (by rw [u₃.mem]; exact hc0t) hi
    (by rw [u₃.gpr, k₂ .s7 (by simp), I.s7]) fun t₄ pk₄ kp₄ f₄ hc₄ => ?_
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₅ u₅ => wp_mv fun t₆ u₆ => wp_addi (by decide) fun t₇ u₇ =>
    wp_addi (by decide) fun t₈ u₈ => wp_mv fun t₉ u₉ => wp_mv fun t₁₀ u₁₀ => WP.block_nil ?_
  obtain pk₁₀ : PK t₄ t₁₀ := (PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans (PK.ofUpd u₁₀)))))
  obtain pkA : PK s t₁₀ := pkt₂.trans ((PK.ofUpd u₃).trans (pk₄.trans pk₁₀))
  obtain E₁₀ := E.of_pk pkA
  obtain m₁₀ : t₁₀.mem = t₄.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  -- The registers the pieces take, kept since `t₂`.
  obtain kr : ∀ r ∈ [Reg.s5, .s6, .s7, .s8], t₄.gpr r = t₂.gpr r := fun r hr => by
    obtain h9 : r ≠ .t3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [kp₄ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h <;> simp [h]),
      u₃.other _ h9]
  obtain hB := (L.bufD E₁₀.perm).drop (k := 16 * b) (by omega_using [hb])
  obtain hQ := hB.take (k := 16 * k) (by omega_using [hk])
  obtain C := cargs L E₁₀ (o := 64) (by decide) (Q := c.D + BitVec.ofNat 64 (16 * b)) (k := k) hQ.src
    (hQ.wd (by decide)) (L.k_d.sub_right (Offset.sub_base c.D (by omega_using [hb, hk])))
    (covers_off E₁₀.perm.d (by omega_using [hb, hk]) hn64)
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
  obtain sv : ∀ r ∈ [Reg.s5, .s6, .s7, .s8], t₁₁.gpr r = t₂.gpr r := fun r hr => by
    obtain hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    obtain h1 : r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a5 ∧ r ≠ .a3 ∧ r ≠ .a4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [h.saved _ hp, u₁₀.other _ h1.2.2.2.2.2, u₉.other _ h1.2.2.2.2.1, u₈.other _ h1.2.2.2.1,
      u₇.other _ h1.2.2.1, u₆.other _ h1.2.1, u₅.other _ h1.1, kr r hr]
  refine wp_sub fun t₁₂ u₁₂ => wp_add fun t₁₃ u₁₃ => wp_sll (by decide) fun t₁₄ u₁₄ => wp_add fun t₁₅ u₁₅ =>
    WP.block_nil ⟨k, hk, hk1, hkb, ?_⟩
  obtain m₁₅ : t₁₅.mem = t₁₁.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem]
  obtain f₄' : Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] t.mem t₁₀.mem := by
    rw [m₁₀, ← m₂, ← u₃.mem]; exact f₄
  obtain ⟨fr, dn, rs⟩ := chunk_inv L hnl I hk32 hkb f₄' (by rw [m₁₀]; exact hc₄) h m₁₅
  obtain s8₁₁ : t₁₁.gpr .s8 = BitVec.ofNat 64 k := by rw [sv .s8 (by simp), s8₂]
  refine ⟨pkA.trans ((PK.ofSaved h.rd h.wr h.sp h.saved).trans ((PK.ofUpd u₁₂).trans ((PK.ofUpd u₁₃).trans
    ((PK.ofUpd u₁₄).trans (PK.ofUpd u₁₅))))), ?_, ?_, ?_, hkb, fr, dn, rs⟩
  · rw [u₁₅.gpr, u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), s8₁₁, u₁₄.other _ (by decide),
      u₁₃.other _ (by decide), u₁₂.other _ (by decide), sv .s5 (by simp), k₂ .s5 (by simp), I.s5,
      ofNat_lsl4 (by omega_using [hk]), Offset.add_add, Nat.mul_add]
  · rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, s8₁₁,
      sv .s6 (by simp), k₂ .s6 (by simp), I.s6, ofNat_sub_ofNat' (by omega_using [hk]) (by omega_using [hn64]), Nat.sub_sub]
  · rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.other .s7 (by decide),
      u₁₂.other .s8 (by decide), s8₁₁, sv .s7 (by simp), k₂ .s7 (by simp), I.s7, BitVec.ofNat_add_ofNat,
      Nat.add_assoc]

end VG.Proof.AesCcm.RISCV64

end

end

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
  obtain I₀ : CtrInv c nonce s 0 s₃ :=
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
  refine WP.ite (decide (c.n / 16 = 0)) (eval_z (a := c.n / 16) (by rw [I₀.s6, Nat.sub_zero]) (by omega_using [hn64]))
    (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n / 16 = 0 := of_decide_eq_true ht
    exact WP.block_nil (by rw [h0]; exact I₀)
  · have h0 : c.n / 16 ≠ 0 := of_decide_eq_false hf
    refine WP.loop (M := isa) (fun m t => ∃ b, m = c.n / 16 - b ∧ b < c.n / 16 ∧ CtrInv c nonce s b t) ?_
      (c.n / 16 - 0) s₃ ⟨0, rfl, by omega_using [h0], I₀⟩
    rintro m t ⟨b, rfl, hb, I⟩
    refine WP.mono (chunk_wp L hnl E hc0 I hb) fun t' ⟨k, _, hk1, hkb, I'⟩ => ?_
    obtain ev := eval_nz (r := .s6) (a := c.n / 16 - (b + k)) I'.s6 (by omega_using [hn64])
    by_cases he : b + k = c.n / 16
    · left; exact ⟨by rw [ev]; simp [he], by rw [← he]; exact I'⟩
    · right; exact ⟨by rw [ev]; simp; omega_arith, c.n / 16 - (b + k), by omega_arith, b + k, rfl, by omega_arith, I'⟩

/-- The last `n mod 16` (not 0) bytes, XORed with `CIPH_K(Ctr₁₊ₙ/₁₆)`. -/
theorem tail_wp {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} (E : Env c s)
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {t : State}
    (I : CtrInv c nonce s (c.n / 16) t) (hs8 : t.gpr .s8 = BitVec.ofNat 64 (c.n % 16)) (h0 : c.n % 16 ≠ 0) :
    WP isa ctrTail t fun t' => PK s t' ∧ Frame (crR c) s.mem t'.mem ∧
      bytesAt t'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  obtain Et := E.of_pk I.pk
  obtain hc0t : bytesAt t.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [Proof.Cmac.bytesAt_frame I.frame (crR_disj L (.inl (by decide))) (by decide), hc0]
  obtain hi : 1 + c.n / 16 < 256 ^ (15 - c.nl) := by have := L.hn; omega_using [h0, this]
  unfold ctrTail
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_mv fun t₁ u₁ => ?_)
  refine ctrAt_wp L (Et.of_pk (PK.ofUpd u₁)) hnl (by rw [u₁.mem]; exact hc0t) hi
    (by rw [u₁.gpr, I.s7]) fun t₂ pk₂ kp₂ f₂ hc₂ => ?_
  unfold zero16 ctrArgs
  simp only [List.cons_append, List.nil_append]
  obtain pk₂' : PK s t₂ := I.pk.trans ((PK.ofUpd u₁).trans pk₂)
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
  obtain pk₁₁ : PK t₂ t₁₁ := (PK.ofUpd u₃).trans ((PK.ofMupd u₄).trans ((PK.ofMupd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans (PK.ofUpd u₁₁))))))))
  obtain E₁₁ := E.of_pk (pk₂'.trans pk₁₁)
  obtain m₁₁ : t₁₁.mem = (t₂.mem.writeW (c.W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₃.gpr]; rfl
  obtain r_ : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a5 → r ≠ .a3 → r ≠ .a4 → t₁₁.gpr r = t₂.gpr r :=
    fun r h0 h3 h4 h5 h8 h6 h7 => by
      rw [u₁₁.other _ h7, u₁₀.other _ h6, u₉.other _ h8, u₈.other _ h5, u₇.other _ h4, u₆.other _ h3, u₅.gpr,
        u₄.gpr, u₃.other _ h0]
  obtain C := cargsW L E₁₁ (o := 64) (d := 80) (by decide) (by decide) (by decide)
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
  obtain sv : ∀ r ∈ [Reg.s5, .s8], t₁₂.gpr r = t.gpr r := fun r hr => by
    obtain hp : r ∈ preserved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [h.saved _ hp, r_ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        kp₂ _ (by simp), u₁.other _ (by decide)]
  refine WP.seq (wp_addi (by decide) fun t₁₃ u₁₃ => wp_mv fun t₁₄ u₁₄ => wp_mv fun t₁₅ u₁₅ =>
    WP.block_nil ?_)
  obtain pk₁₅ : PK s t₁₅ := pk₂'.trans (pk₁₁.trans ((PK.ofSaved h.rd h.wr h.sp h.saved).trans ((PK.ofUpd u₁₃).trans
    ((PK.ofUpd u₁₄).trans (PK.ofUpd u₁₅)))))
  obtain E₁₅ := E.of_pk pk₁₅
  obtain m₁₅ : t₁₅.mem = t₁₂.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem]
  obtain hS := (L.bufD E₁₅.perm).drop (k := 16 * (c.n / 16)) (by omega_using [])
  rw [show c.n - 16 * (c.n / 16) = c.n % 16 by omega_using []] at hS
  obtain xp : BytesPre t₁₅ (c.W + BitVec.ofNat 64 80) (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) :=
    { a0 := by rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.gpr, h.saved .s1 (by decide),
        (pk₁₁).gpr .s1 (by decide), pk₂'.gpr .s1 (by decide), E.s1]; rfl
      a1 := by rw [u₁₅.other _ (by decide), u₁₄.gpr, u₁₃.other _ (by decide), sv .s5 (by simp), I.s5]
      a2 := by rw [u₁₅.gpr, u₁₄.other _ (by decide), u₁₃.other _ (by decide), sv .s8 (by simp), hs8]
      pos := by omega_using [h0]
      lt := by omega_using []
      rd := E₁₅.perm.wCR (by omega_using [])
      wr := covers_off E₁₅.perm.d (by omega_using []) hn64
      disj := (hS.wd (by omega_using [])).symm }
  refine WP.mono (xorBytes_wp t₁₅ xp) fun t₁₆ ⟨hm₁₆, _, k₁₆⟩ => ?_
  -- What the tail wrote in `W`.
  obtain s64 : Region.Sub ⟨c.W + BitVec.ofNat 64 64, 16⟩ ⟨c.W + BitVec.ofNat 64 64, 32⟩ := Region.sub_prefix (by decide)
  obtain s80 : Region.Sub ⟨c.W + BitVec.ofNat 64 80, 16⟩ ⟨c.W + BitVec.ofNat 64 64, 32⟩ :=
    Offset.sub c.W (by decide) (by decide)
  rw [u₁.mem] at f₂
  obtain fz : Frame [⟨c.W + BitVec.ofNat 64 80, 16⟩] t₂.mem t₁₁.mem := by rw [m₁₁]; exact Proof.Cmac.frame_store2 _ _ _
  obtain cT : Frame [⟨c.W + BitVec.ofNat 64 64, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩] t.mem t₁₅.mem := by
    rw [m₁₅]
    refine ((f₂.sub fun r hr => ?_).trans (fz.sub fun r hr => ?_)).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s64⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s80⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, s64⟩
      · exact ⟨_, by simp, s80⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  obtain toR : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region), ⟨c.W + BitVec.ofNat 64 384, 2048⟩],
      ∃ r' ∈ crR c, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  obtain sep : ∀ {a l : Nat}, a + l ≤ c.n → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region),
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorL (bytesAt t₁₅.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16))
      (bytesAt t₁₅.mem (c.W + BitVec.ofNat 64 80) (c.n % 16)) := ⟨_, rfl⟩
  rw [← hxs] at hm₁₆
  obtain hxl : xs.length = c.n % 16 := by simp [hxs, xorL, length_bytesAt]
  obtain fw : Frame [⟨c.D + BitVec.ofNat 64 (16 * (c.n / 16)), c.n % 16⟩] t₁₅.mem t₁₆.mem := by
    rw [hm₁₆]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  refine ⟨pk₁₅.trans (PK.ofKeeps k₁₆), ?_, ?_⟩
  · refine I.frame.trans ((cT.sub toR).trans (fw.sub fun r hr => ?_))
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega_using [])⟩
  · have h₁ : bytesAt t₁₅.mem c.D (16 * (c.n / 16)) = bytesAt t.mem c.D (16 * (c.n / 16)) := by
      have := Proof.Cmac.bytesAt_frame cT (sep (a := 0) (l := 16 * (c.n / 16)) (by omega_using [])) (by omega_using [hn64])
      rwa [BitVec.add_zero] at this
    obtain h₂ : bytesAt t₁₅.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) := by
      rw [Proof.Cmac.bytesAt_frame cT (sep (by omega_using [])) (by omega_using []),
        show c.n % 16 = c.n - 16 * (c.n / 16) by omega_using [], I.rest]
    obtain f₁₁ : Frame (crR c) s.mem t₁₁.mem := I.frame.trans ((f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s64⟩).trans (fz.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, s80⟩))
    obtain hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem c.K c.R) := fun x => Proof.Cmac.aesWith_length _ _ x
    obtain hc₁₁ : bytesAt t₁₁.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + c.n / 16) := by
      rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide), hc₂]
    obtain hz₁₁ : bytesAt t₁₁.mem (c.W + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 := by
      rw [m₁₁]; exact zeros16_bytes _ _
    obtain hks : bytesAt t₁₅.mem (c.W + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph s.mem c.K c.R (Spec.Ccm.ctrBlock nonce (1 + c.n / 16)) := by
      obtain hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 1 + c.n / 16) (by rw [hnl]; have := L.h13; omega_using [this])
        (fun i hi => by
          rw [show i = 0 by omega_using [hi], Nat.add_zero]
          show Spec.Gcm.ofBytes _ = _
          rw [hc₁₁]) h.out
      rw [Nat.mul_one] at hx
      rw [m₁₅, hx, hz₁₁, ciph_crR L f₁₁, xorFrom_zeros hBC]
    obtain ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem c.K c.R) nonce (1 + c.n / 16)
      (d := bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16)) (by rw [length_bytesAt]; omega_using [])
    rw [length_bytesAt, hBC] at ht
    obtain ht' := ht.resolve_right (by omega_using [])
    rw [hm₁₆, Proof.AesCcm.bytesAt_writeBytes_at t₁₅.mem c.D xs (by rw [hxl]; omega_using []) hn64,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega_using []), List.append_nil,
      ← bytesAt_prefix t₁₅.mem c.D (show 16 * (c.n / 16) ≤ c.n by omega_using []), h₁, I.done, hxs, xorL, h₂,
      bytesAt_prefix t₁₅.mem (c.W + BitVec.ofNat 64 80) (show c.n % 16 ≤ 16 by omega_using []), hks, ht']
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
  obtain pk₂ : PK t t₂ := PK.ofUpd u₂
  obtain m₂ : t₂.mem = t.mem := by rw [u₂.mem]
  obtain s8₂ : t₂.gpr .s8 = BitVec.ofNat 64 (c.n % 16) := by
    rw [u₂.gpr, I.pk.gpr .s10 (by decide), E.s10, show BitVec.ofInt 64 15 = BitVec.ofNat 64 15 from rfl,
      ofNat_and15 hn64]
  refine WP.ite (decide (c.n % 16 = 0)) (eval_z s8₂ (by omega_using [])) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨I.pk.trans pk₂, by rw [m₂]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (c.n / 16) = c.n by omega_using [h0]] at hd
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
