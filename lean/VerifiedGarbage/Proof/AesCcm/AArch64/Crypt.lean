module

import VerifiedGarbage.Proof.AesCcm.AArch64.Blocks
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesCcm.AArch64
public import VerifiedGarbage.Proof.AesCcm.AArch64.Env
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.AesCcm.AArch64.Header

/-! ### `AesCcm.AArch64.Chunk`, which this module and modules that import it used -/

section

/-!
# AES-CCM on AArch64: a chunk of counter mode (`ctrChunk`)

Untrusted: everything here is checked by Lean. After `b` whole blocks
(`CtrInv`), `ctrChunk` encrypts `k = min (n/16 − b, 2³² − (1 + b) mod 2³²)`
more by `vg_aes_ctr32` from `Ctr₁₊ᵦ`, whose counters do not wrap around in
their low 32 bits, so that they are CCM's (`chunk_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (CtrCall CtrPost ctr_call Others add_ofNat_assoc eval_zero eval_nonzero ofNat_sub
  toNat_ofNat_of_lt ofNat_add_ofNat lsl4_ofNat covers_off)
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.AesCcm (xorFrom xorFrom_append repeat_inc32_ctrBlock ctr32_ccm length_bytesAt bytesAt_prefix
  bytesAt_suffix)

/-- What `ctr` writes: `Ctrⱼ` and the keystream block at `W + 64`, the
working space of the functions called and the data. -/
abbrev ctrR (c : Cx) : List Region :=
  [⟨c.W + BitVec.ofNat 64 64, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩, ⟨c.D, c.n⟩]

theorem ctrR_mut (c : Cx) : ∀ r ∈ ctrR c, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_hi (by decide) (by decide)
  · exact sub_data

/-- The parts of `W` that `ctr` does not write. -/
theorem ctrR_disj {c : Cx} (L : Lay c) {d k : Nat} (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 384)) :
    ∀ r ∈ ctrR c, (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (L.d_w' (by omega_arith)).symm

theorem ctrR_k {c : Cx} (L : Lay c) : ∀ r ∈ ctrR c, (⟨c.K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w' (by decide)
  · exact L.k_w' (by decide)
  · exact L.k_d

theorem ciph_ctrR {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (ctrR c) m m') :
    Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => (ctrR_k L r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega_arith)]

/-- The state of `ctr` after `b` whole blocks, from the state `s` it
started from: those encrypted, the rest of the data as it was. -/
structure CtrInv (c : Cx) (nonce : List Byte) (s : State) (b : Nat) (t : State) : Prop where
  env : Env c t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  x23 : t.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b)
  x24 : t.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (1 + b)
  le : b ≤ c.n / 16
  frame : Frame (ctrR c) s.mem t.mem
  done : bytesAt t.mem c.D (16 * b) = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D (16 * b))
  rest : bytesAt t.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.n - 16 * b) =
    bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * b)) (c.n - 16 * b)

/-- `k = min (m, 2³² − (1 + b) mod 2³²)` in `x26`, for `m` blocks left. -/
theorem kSel_ok {b m : Nat} {t : State} (h24 : t.gpr .x24 = BitVec.ofNat 64 m)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 (1 + b)) (hm : m < 2 ^ 60) :
    WP isa (.seq (.block [.addImm .w .x9 .x25 0, .movz .x .x10 1 2, .sub .x .x10 .x10 .x9, .sub .x .x11 .x24 .x10,
        .lsr .x .x11 .x11 63]) (.ite (.zero .x .x11) (.block [mov .x26 .x10]) (.block [mov .x26 .x24]))) t
      fun t₂ => t₂.gpr .x26 = BitVec.ofNat 64 (min m (2 ^ 32 - (1 + b) % 2 ^ 32)) ∧
        Others [.x9, .x10, .x11, .x26] t t₂ ∧ t₂.mem = t.mem ∧ t₂.sp = t.sp ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  obtain hj := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide)
  obtain ⟨t₁, run₁, x10₁, x11₁, hg₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      [.addImm .w .x9 .x25 0, .movz .x .x10 1 2, .sub .x .x10 .x10 .x9, .sub .x .x11 .x24 .x10,
        .lsr .x .x11 .x11 63] t = some t₁ ∧
      t₁.gpr .x10 = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) ∧
      t₁.gpr .x11 = BitVec.ofNat 64 (if m < 2 ^ 32 - (1 + b) % 2 ^ 32 then 1 else 0) ∧
      Others [.x9, .x10, .x11] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    obtain k1 : (BitVec.setWidth 64 (1 : BitVec 16) <<< 32 : BitVec 64) = BitVec.ofNat 64 (2 ^ 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rfl
    obtain hx10 : BitVec.ofNat 64 (2 ^ 32) - BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (1 + b))) =
        BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat]
      omega_arith
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h25, k1, hx10]
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h25, h24, k1, hx10]
      exact sign63 (by omega_arith) (by omega_arith)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_zero x11₁ (by split <;> decide)) (fun ht => ?_) (fun hf => ?_)
  · have h : ¬ m < 2 ^ 32 - (1 + b) % 2 ^ 32 := by
      have := of_decide_eq_true ht; split at this <;> simp_all
    refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₂ ht₂ => ?_
    subst ht₂
    refine ⟨?_, fun r hr => ?_, hm₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, x10₁]; rw [Nat.min_eq_right (by omega_arith)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.2.2.2, hg₁ r (by simp [hr.1, hr.2.1, hr.2.2.1])]
  · have h : m < 2 ^ 32 - (1 + b) % 2 ^ 32 := by
      have := of_decide_eq_false hf; split at this <;> simp_all
    refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₂ ht₂ => ?_
    subst ht₂
    refine ⟨?_, fun r hr => ?_, hm₁, sp₁, rd₁, wr₁⟩
    · simp only [gpr_write, BitVec.setWidth_eq, ite_true, hg₁ .x24 (by decide), h24]; rw [Nat.min_eq_left (by omega_arith)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr.2.2.2, hg₁ r (by simp [hr.1, hr.2.1, hr.2.2.1])]


/-- The arguments of `vg_aes_ctr32` for a chunk, and `Ctr₁₊ᵦ`. -/
theorem setup_ok {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {b k : Nat}
    (hb : b + k ≤ c.n / 16) (hk : 1 ≤ k) {t : State} (E : Env c t)
    (hc0 : bytesAt t.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    (h23 : t.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b)) (h25 : t.gpr .x25 = BitVec.ofNat 64 (1 + b))
    (h26 : t.gpr .x26 = BitVec.ofNat 64 k) :
    WP isa (.block (([mov .x9 .x25] : List Instr) ++ ctrAt ++ ctrArgs ++ ([mov .x3 .x23, mov .x4 .x26] : List Instr))) t
      fun t₅ => Env c t₅ ∧
        CtrCall t₅ c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384) c.R k ∧
        Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] t.mem t₅.mem ∧
        bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b) ∧
        Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] t t₅ ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr := by
  obtain h7 : 7 ≤ nonce.length := by rw [hnl]; exact L.h7
  obtain h13 : nonce.length ≤ 13 := by rw [hnl]; exact L.h13
  obtain hq16 : c.n / 16 < 256 ^ (15 - nonce.length) := by
    rw [hnl]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) L.hn
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₁ ht₁ => ?_)
  obtain hg₁ : Others [.x9] t t₁ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]
  obtain E₁ : Env c t₁ := E.others hg₁ (by decide) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl)
  obtain h9 : t₁.gpr .x9 = BitVec.ofNat 64 (1 + b) := by rw [← ht₁]; simp [gpr_write, h25]
  obtain hm₁ : t₁.mem = t.mem := by rw [← ht₁]; rfl
  refine WP.block_append (WP.mono (ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (i := 1 + b) (by omega_arith) h9)
    fun t₂ ⟨f₂, hc₂, hg₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain E₂ : Env c t₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [ctrArgs], rfl⟩ fun t₅ ht₅ => ?_
  obtain hg₅ : Others [.x0, .x1, .x2, .x3, .x4, .x5] t₂ t₅ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; rw [← ht₅]; simp [gpr_write, hr]
  obtain E₅ : Env c t₅ := E₂.others hg₅ (by decide) (by rw [← ht₅]; rfl) (by rw [← ht₅]; rfl) (by rw [← ht₅]; rfl)
  obtain hm₅ : t₅.mem = t₂.mem := by rw [← ht₅]; rfl
  obtain g₂ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → t₂.gpr r = t.gpr r := fun r a b' c' => by
    rw [hg₂ r (by simp [a, b', c']), hg₁ r (by simp [a])]
  obtain hS := (L.bufD E₂.perm).slice (a := 16 * b) (k := 16 * k) (by omega_arith)
  obtain hqo : (⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 64, 16⟩ :=
    hS.wd (by decide)
  obtain hqk : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩ :=
    L.k_d.sub_right (Offset.sub_base c.D (by omega_arith))
  obtain hqw : Covers [⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩] t₅.wr :=
    covers_off E₅.perm.d (by omega_arith) L.n_lt
  obtain hS₅ := hS.of_eq (s' := t₅) (by rw [← ht₅]; rfl) (by rw [← ht₅]; rfl)
  refine ⟨E₅, ?_, by rw [hm₅, ← hm₁]; exact f₂, by rw [hm₅]; exact hc₂, ?_, by rw [← ht₅]; simp only [rd_write]; rw [rd₂, ← ht₁]; rfl,
    by rw [← ht₅]; simp only [wr_write]; rw [wr₂, ← ht₁]; rfl⟩
  · refine cargs L E₅ (o := 64) (by decide) hS₅.src hqo hqk hqw (by have := L.n_lt; omega_arith) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← ht₅]; simp [gpr_write, E₂.x21]
    · rw [← ht₅]; simp [gpr_write, E₂.x22]
    · rw [← ht₅]; simp [gpr_write, E₂.x19]
    · rw [← ht₅]; simp [gpr_write, g₂ .x23 (by decide) (by decide) (by decide), h23]
    · rw [← ht₅]; simp [gpr_write, g₂ .x26 (by decide) (by decide) (by decide), h26]
    · rw [← ht₅]; simp [gpr_write, E₂.x19]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg₅ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1]),
      g₂ r hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2]

/-- What follows the call: `k` blocks past them. -/
theorem step_ok {c : Cx} {t : State} {b k : Nat} (h23 : t.gpr .x23 = c.D + BitVec.ofNat 64 (16 * b))
    (h24 : t.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - b)) (h25 : t.gpr .x25 = BitVec.ofNat 64 (1 + b))
    (h26 : t.gpr .x26 = BitVec.ofNat 64 k) (hkb : b + k ≤ c.n / 16) (hn : c.n < 2 ^ 64) :
    WP isa (.block [.sub .x .x24 .x24 .x26, .add .x .x25 .x25 .x26, .lsl .x .x9 .x26 4, .add .x .x23 .x23 .x9]) t
      fun t' => t'.gpr .x24 = BitVec.ofNat 64 (c.n / 16 - (b + k)) ∧
        t'.gpr .x25 = BitVec.ofNat 64 (1 + (b + k)) ∧ t'.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (b + k)) ∧
        Others [.x9, .x23, .x24, .x25] t t' ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t' ht' => ?_
  subst ht'
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h24, h26]
    rw [show c.n / 16 - (b + k) = c.n / 16 - b - k by omega_arith]
    exact ofNat_sub (by omega_arith) (by omega_arith)
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h25, h26]
    rw [ofNat_add_ofNat, Nat.add_assoc]
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, h23, h26, lsl4_ofNat]
    rw [BitVec.add_assoc, ofNat_add_ofNat, Nat.mul_add]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr]

/-- The state after a chunk of `k` blocks. -/
theorem chunk_inv {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State} {b k : Nat}
    {t : State} (I : CtrInv c nonce s b t) (hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32) (hkb : b + k ≤ c.n / 16)
    {t₅ t₆ t₇ : State} (f₅ : Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩] t.mem t₅.mem)
    (hc₅ : bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b))
    (h : CtrPost t₅ c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384) c.R k t₆)
    (hm₇ : t₇.mem = t₆.mem) :
    Frame (ctrR c) s.mem t₇.mem ∧
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
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], ∃ r' ∈ ctrR c, Region.Sub r r' := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega_arith)⟩
    · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  -- Separation of the data from what the chunk wrote.
  obtain sep : ∀ {a l : Nat}, (a + l ≤ 16 * b ∨ 16 * (b + k) ≤ a) → a + l ≤ c.n →
      ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
        ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l ha hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
    · exact Offset.disjoint c.D (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  obtain hbk : 16 * (b + k) = 16 * b + 16 * k := Nat.mul_add _ _ _
  refine ⟨I.frame.trans (cR.sub toR), ?_, ?_⟩
  · -- The blocks done.
    obtain h₁ : bytesAt t₇.mem c.D (16 * b) = bytesAt t.mem c.D (16 * b) := by
      have := Proof.AesGcm.AArch64.bytesAt_frame cR (sep (a := 0) (l := 16 * b) (.inl (by omega_arith)) (by omega_arith))
        (by omega_arith)
      rwa [BitVec.add_zero] at this
    obtain hinc : ∀ i < k, Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt t₅.mem (c.W + BitVec.ofNat 64 64)) =
        Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce (1 + b + i)) := fun i hi => by
      show Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.ofBytes (bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16)) = _
      rw [hc₅]
      exact repeat_inc32_ctrBlock (by rw [hnl]; exact L.h7) (by rw [hnl]; exact L.h13) hk32
        (by rw [hnl]; have := Nat.lt_of_le_of_lt (Nat.div_le_self c.n 16) L.hn; omega_arith) i hi
    obtain hx := ctr32_ccm (by rw [hnl]; have := L.h13; omega_arith) hinc h.out
    obtain f₅' : Frame (ctrR c) s.mem t₅.mem := I.frame.trans (f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩)
    obtain hx₅ : bytesAt t₅.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) := by
      rw [bytesAt_prefix t₅.mem _ (show 16 * k ≤ c.n - 16 * b by omega_arith),
        bytesAt_prefix s.mem _ (show 16 * k ≤ c.n - 16 * b by omega_arith), ← I.rest,
        Proof.AesGcm.AArch64.bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (L.d_w.sub_left (Offset.sub_base c.D (by omega_arith))).sub_right (Lay.wSub (by decide))) (by omega_arith)]
    rw [hbk, Proof.Cmac.Stream.bytesAt_append, Proof.Cmac.Stream.bytesAt_append, h₁, I.done, hm₇, hx, hx₅,
      ciph_ctrR L f₅', xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 b]
  · -- The rest of the data.
    obtain hR' := Proof.AesGcm.AArch64.bytesAt_frame cR
      (sep (a := 16 * (b + k)) (l := c.n - 16 * (b + k)) (.inr (Nat.le_refl _)) (by omega_arith)) (by omega_arith)
    rw [hR', show c.D + BitVec.ofNat 64 (16 * (b + k)) = c.D + BitVec.ofNat 64 (16 * b) + BitVec.ofNat 64 (16 * k) by
        rw [add_ofNat_assoc, hbk],
      show c.n - 16 * (b + k) = c.n - 16 * b - 16 * k by omega_arith, bytesAt_suffix _ _ (show 16 * k ≤ c.n - 16 * b by omega_arith),
      bytesAt_suffix _ _ (show 16 * k ≤ c.n - 16 * b by omega_arith), I.rest]

/-- One chunk. -/
theorem chunk_ok (v : Ctr32Impl) {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl)
    {s : State} (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {b : Nat}
    {t : State} (I : CtrInv c nonce s b t) (hb : b < c.n / 16) :
    WP isa (ctrChunk v.callee) t fun t' => ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) ∧ 1 ≤ k ∧
      b + k ≤ c.n / 16 ∧ CtrInv c nonce s (b + k) t' := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  refine WP.assoc (WP.seq (WP.mono (kSel_ok (b := b) I.x24 I.x25 (by omega_arith))
    fun t₂ ⟨x26₂, hg₂, hm₂, sp₂, rd₂, wr₂⟩ => ?_))
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at x26₂
  obtain hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_arith
  obtain hkb : b + k ≤ c.n / 16 := by rw [hk]; omega_arith
  obtain hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32 := by
    rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_arith
  obtain E₂ : Env c t₂ := I.env.others hg₂ (by decide) sp₂ rd₂ wr₂
  obtain hc0t : bytesAt t₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [hm₂, Proof.AesGcm.AArch64.bytesAt_frame I.frame (ctrR_disj L (.inl (by decide))) (by decide), hc0]
  refine WP.seq (WP.mono (setup_ok L hnl hkb hk1 E₂ hc0t (by rw [hg₂ _ (by decide), I.x23])
    (by rw [hg₂ _ (by decide), I.x25]) x26₂) fun t₅ ⟨E₅, C₅, f₅, hc₅, hg₅, rd₅, wr₅⟩ => ?_)
  refine WP.seq (WP.mono (ctr_call v C₅) fun t₆ h => ?_)
  obtain E₆ : Env c t₆ := E₅.of_saved h.saved h.sp h.rd h.wr
  obtain sv : ∀ r ∈ [Reg.x23, .x24, .x25, .x26], t₆.gpr r = t₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.saved r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      hg₅ r (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  refine WP.mono (step_ok (c := c) (b := b) (k := k) (by rw [sv .x23 (by simp), hg₂ _ (by decide), I.x23])
    (by rw [sv .x24 (by simp), hg₂ _ (by decide), I.x24]) (by rw [sv .x25 (by simp), hg₂ _ (by decide), I.x25])
    (by rw [sv .x26 (by simp), x26₂]) hkb hn64) fun t₇ ⟨x24₇, x25₇, x23₇, hg₇, hm₇, sp₇, rd₇, wr₇⟩ => ?_
  obtain ⟨fr, dn, rs⟩ := chunk_inv L hnl I hk32 hkb (by rw [← hm₂]; exact f₅) hc₅ h hm₇
  exact ⟨k, hk, hk1, hkb, ⟨E₆.others hg₇ (by decide) sp₇ rd₇ wr₇, by rw [rd₇, h.rd, rd₅, rd₂, I.rd],
    by rw [wr₇, h.wr, wr₅, wr₂, I.wr], x23₇, x24₇, x25₇, hkb, fr, dn, rs⟩⟩

end VG.Proof.AesCcm.AArch64

end

end

/-!
# AES-CCM on AArch64: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctr` encrypts the whole
blocks of the data in chunks (`ctrHead_ok`, by `chunk_ok`), then its last
`n mod 16` bytes with `CIPH_K(Ctr₁₊ₙ/₁₆)`, which `vg_aes_ctr32` writes over a
zero block (`tail_ok`): the data XORed with CCM's keystream from `Ctr₁`
(`ctr_ok`), which is its encryption (`Proof.AesCcm.crypt_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm xorLoop)
open VG.Proof.AesGcm.AArch64 (CtrCall CtrPost ctr_call Others add_ofNat_assoc eval_zero eval_nonzero
  LoopPre xorLoop_ok xorBytes loopRegs lsr_ofNat and15 toNat_ofNat_of_lt covers_off covers_left)
open VG.Proof.Aes.AArch64 (Ctr32Impl)
open VG.Proof.AesCcm (xorFrom xorFrom_append xorFrom_tail xorFrom_zeros ctr32_ccm length_bytesAt
  bytesAt_prefix bytesAt_writeBytes_at BlockCipher)

/-- `x23`, `x24` and `x25` for the first chunk. -/
theorem ctrHeadBlk_ok {c : Cx} (L : Lay c) {nonce : List Byte} {s : State} (E : Env c s) :
    WP isa (.block [mov .x23 .x27, .lsr .x .x24 .x28 4, imm .x25 1]) s (CtrInv c nonce s 0) := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun s₁ hs₁ => ?_
  subst hs₁
  refine ⟨E.others (rs := [.x23, .x24, .x25]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]) (by decide)
      rfl rfl rfl, rfl, rfl, ?_, ?_, ?_, Nat.zero_le _, Frame.refl _ _, rfl, by simp [mem_write]⟩
  · simp [gpr_write, E.x27]
  · simp [gpr_write, E.x28, lsr_ofNat c.n 4 L.n_lt]
  · simp [gpr_write]

/-- The whole blocks, in chunks. -/
theorem ctrHead_ok (v : Ctr32Impl) {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl)
    {s : State} (E : Env c s) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    WP isa (.seq (.block [mov .x23 .x27, .lsr .x .x24 .x28 4, imm .x25 1])
      (.ite (.zero .x .x24) (.block []) (.loop (ctrChunk v.callee) (.nonzero .x .x24)))) s
      (CtrInv c nonce s (c.n / 16)) := by
  have hn64 := L.n_lt
  refine WP.seq (WP.mono (ctrHeadBlk_ok L (nonce := nonce) E) fun s₁ I₀ => ?_)
  refine WP.ite (decide (c.n / 16 = 0)) (eval_zero (a := c.n / 16) (by rw [I₀.x24, Nat.sub_zero]) (by omega_arith))
    (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n / 16 = 0 := of_decide_eq_true ht
    exact WP.block_nil (by rw [h0]; exact I₀)
  · have h0 : c.n / 16 ≠ 0 := of_decide_eq_false hf
    refine WP.loop (M := isa) (fun m t => ∃ b, m = c.n / 16 - b ∧ b < c.n / 16 ∧ CtrInv c nonce s b t) ?_
      (c.n / 16 - 0) s₁ ⟨0, rfl, by omega_arith, I₀⟩
    rintro m t ⟨b, rfl, hb, I⟩
    refine WP.mono (chunk_ok v L hnl hc0 I hb) fun t' ⟨k, _, hk1, hkb, I'⟩ => ?_
    obtain ev := eval_nonzero (r := .x24) (a := c.n / 16 - (b + k)) I'.x24 (by omega_arith)
    by_cases he : b + k = c.n / 16
    · left; exact ⟨by rw [ev]; simp [he], by rw [← he]; exact I'⟩
    · right; exact ⟨by rw [ev]; simp; omega_arith, c.n / 16 - (b + k), by omega_arith, b + k, rfl, by omega_arith, I'⟩

/-- The arguments of the call for the last bytes: `Ctrⱼ` and a zero block at
`W + 80`. -/
theorem tailSetup_ok {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {t : State}
    (E : Env c t) (hc0 : bytesAt t.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {j : Nat}
    (hj : j < 256 ^ (15 - c.nl)) (h25 : t.gpr .x25 = BitVec.ofNat 64 j) :
    WP isa (.block (([mov .x9 .x25] : List Instr) ++ ctrAt ++ zero16 ksO ++ ctrArgs ++
        ([ptr .x3 .x19 ksO, imm .x4 1] : List Instr))) t fun t' =>
      Env c t' ∧ CtrCall t' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80) (c.W + BitVec.ofNat 64 384) c.R 1 ∧
      Frame [⟨c.W + BitVec.ofNat 64 64, 32⟩] t.mem t'.mem ∧
      bytesAt t'.mem (c.W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce j ∧
      bytesAt t'.mem (c.W + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9, .x10, .x11] t t' ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  obtain h7 : 7 ≤ nonce.length := by rw [hnl]; exact L.h7
  obtain h13 : nonce.length ≤ 13 := by rw [hnl]; exact L.h13
  rw [List.append_assoc, List.append_assoc, List.append_assoc]
  refine WP.block_append (Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₁ ht₁ => ?_)
  obtain hg₁ : Others [.x9] t t₁ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]
  obtain E₁ : Env c t₁ := E.others hg₁ (by decide) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl)
  obtain h9 : t₁.gpr .x9 = BitVec.ofNat 64 j := by rw [← ht₁]; simp [gpr_write, h25]
  obtain hm₁ : t₁.mem = t.mem := by rw [← ht₁]; rfl
  refine WP.block_append (WP.mono (ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (i := j) (by rw [hnl]; exact hj) h9)
    fun t₂ ⟨f₂, hc₂, hg₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain E₂ : Env c t₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  obtain w₁ := E₂.perm.wW (show 80 + 8 ≤ 2560 by decide)
  obtain w₂ := E₂.perm.wW (show 88 + 8 ≤ 2560 by decide)
  obtain ⟨t₃, run₃, hm₃, x0, x1, x2, x3, x4, x5, hg₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa
      (zero16 ksO ++ ctrArgs ++ [ptr .x3 .x19 ksO, imm .x4 1]) t₂ = some t₃ ∧
      t₃.mem = (t₂.mem.writeW (c.W + BitVec.ofNat 64 80) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 88)
        (0 : BitVec 64) ∧
      t₃.gpr .x0 = c.K ∧ t₃.gpr .x1 = BitVec.ofNat 64 c.R ∧ t₃.gpr .x2 = c.W + BitVec.ofNat 64 64 ∧
      t₃.gpr .x3 = c.W + BitVec.ofNat 64 80 ∧ t₃.gpr .x4 = BitVec.ofNat 64 1 ∧
      t₃.gpr .x5 = c.W + BitVec.ofNat 64 384 ∧
      Others [.x0, .x1, .x2, .x3, .x4, .x5, .x9] t₂ t₃ ∧ t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by carun [ctrArgs, E₂.x19, w₁, w₂], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp only [mem_write]; rfl
    · simp [gpr_write, E₂.x21]
    · simp [gpr_write, E₂.x22]
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write]
    · simp [gpr_write, E₂.x19]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.of_runBlock ⟨t₃, by simpa only [List.append_assoc] using run₃, ?_⟩
  obtain E₃ : Env c t₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  obtain e88 : c.W + BitVec.ofNat 64 88 = c.W + BitVec.ofNat 64 80 + BitVec.ofNat 64 8 := by rw [add_ofNat_assoc]
  obtain c80 : ∀ d, 80 ≤ d → d + 8 ≤ 96 →
      (⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => Offset.contains c.W (by omega_arith) (by omega_arith) (by decide)
  obtain fz : Frame [⟨c.W + BitVec.ofNat 64 80, 16⟩] t₂.mem t₃.mem := by
    rw [hm₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 80) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains c.W (d := 88) (n := 8) (e := 80) (k := 16) (by decide) (by decide) (by decide))
  refine ⟨E₃, cargsW L E₃ (o := 64) (d := 80) (by decide) (by decide) (by decide) x0 x1 x2 x3 x4 x5, ?_, ?_, ?_,
    fun r hr => ?_, by rw [rd₃, rd₂, ← ht₁]; rfl, by rw [wr₃, wr₂, ← ht₁]; rfl⟩
  · rw [hm₃, ← hm₁]
    exact ((f₂.sub fun r hr => ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 80 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) (0 : BitVec 64) (c80 88 (by decide) (by decide))
  · rw [Proof.AesGcm.AArch64.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c.W (.inl (by decide)) (by decide) (by decide)) (by decide), hc₂]
  · rw [hm₃, e88, Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_zero]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hg₃ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      hg₂ r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
    exact hg₁ r (by simp [hr.2.2.2.2.2.2.1])

/-- The last `n mod 16` bytes, after the whole blocks. -/
theorem tail_ok (v : Ctr32Impl) {c : Cx} (L : Lay c) {nonce : List Byte} (hnl : nonce.length = c.nl) {s : State}
    (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {t t₀ : State}
    (I : CtrInv c nonce s (c.n / 16) t) (E₀ : Env c t₀) (hm₀ : t₀.mem = t.mem)
    (h23 : t₀.gpr .x23 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
    (h25 : t₀.gpr .x25 = BitVec.ofNat 64 (1 + c.n / 16)) (h26 : t₀.gpr .x26 = BitVec.ofNat 64 (c.n % 16))
    (hrd₀ : t₀.rd = t.rd) (hwr₀ : t₀.wr = t.wr) (h0 : c.n % 16 ≠ 0) :
    WP isa (ctrTail v.callee) t₀ fun t' => Env c t' ∧ t'.rd = s.rd ∧ t'.wr = s.wr ∧ Frame (ctrR c) s.mem t'.mem ∧
      bytesAt t'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  obtain hq16 : c.n / 16 < 256 ^ (15 - c.nl) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) L.hn
  obtain hc0₀ : bytesAt t₀.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [hm₀, Proof.AesGcm.AArch64.bytesAt_frame I.frame (ctrR_disj L (.inl (by decide))) (by decide), hc0]
  refine WP.seq (WP.mono (tailSetup_ok L hnl E₀ hc0₀ (j := 1 + c.n / 16) (by have := L.hn; omega_arith) h25)
    fun t₁ ⟨E₁, C₁, f₁, hc₁, hz₁, hg₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (ctr_call v C₁) fun t₂ h => ?_)
  obtain E₂ : Env c t₂ := E₁.of_saved h.saved h.sp h.rd h.wr
  obtain sv : ∀ r ∈ [Reg.x23, .x26], t₂.gpr r = t₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.saved r (by rcases hr with rfl | rfl <;> decide) (by rcases hr with rfl | rfl <;> decide),
      hg₁ r (by rcases hr with rfl | rfl <;> decide)]
  obtain ⟨t₃, run₃, x11₃, x12₃, x13₃, hg₃, hm₃, sp₃, rd₃, wr₃⟩ : ∃ t₃, runBlock isa
      [ptr .x11 .x19 ksO, mov .x12 .x23, mov .x13 .x26] t₂ = some t₃ ∧
      t₃.gpr .x11 = c.W + BitVec.ofNat 64 80 ∧ t₃.gpr .x12 = c.D + BitVec.ofNat 64 (16 * (c.n / 16)) ∧
      t₃.gpr .x13 = BitVec.ofNat 64 (c.n % 16) ∧ Others [.x11, .x12, .x13] t₂ t₃ ∧ t₃.mem = t₂.mem ∧
      t₃.sp = t₂.sp ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by carun [], ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp [gpr_write, E₂.x19]
    · simp [gpr_write, sv .x23 (by simp), h23]
    · simp [gpr_write, sv .x26 (by simp), h26]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [gpr_write, hr]
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  obtain E₃ : Env c t₃ := E₂.others hg₃ (by decide) sp₃ rd₃ wr₃
  obtain rd₃' : t₃.rd = s.rd := by rw [rd₃, h.rd, rd₁, hrd₀, I.rd]
  obtain wr₃' : t₃.wr = s.wr := by rw [wr₃, h.wr, wr₁, hwr₀, I.wr]
  obtain hS := (L.bufD E₃.perm).slice (a := 16 * (c.n / 16)) (k := c.n % 16) (by omega_arith)
  obtain lp : LoopPre t₃ (c.W + BitVec.ofNat 64 80) (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) :=
    ⟨by omega_arith, E₃.perm.wCR (by omega_arith), covers_off E₃.perm.d (by omega_arith) hn64, (hS.wd (by omega_arith)).symm⟩
  refine WP.mono (xorLoop_ok t₃ x11₃ x12₃ x13₃ (by omega_arith) lp) fun t₄ ⟨hm₄, hg₄, sp₄, rd₄, wr₄⟩ => ?_
  -- What the tail wrote.
  obtain cT : Frame [⟨c.W + BitVec.ofNat 64 64, 32⟩, ⟨c.W + BitVec.ofNat 64 384, 2048⟩] t.mem t₃.mem := by
    rw [hm₃, ← hm₀]
    refine (f₁.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub c.W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
  obtain sep : ∀ {a l : Nat}, a + l ≤ c.n → ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 32⟩ : Region),
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  obtain ⟨xs, hxs⟩ : ∃ xs, xs = xorBytes t₃.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16)))
      (c.W + BitVec.ofNat 64 80) (c.n % 16) := ⟨_, rfl⟩
  rw [← hxs] at hm₄
  obtain hxl : xs.length = c.n % 16 := by simp [hxs, xorBytes, length_bytesAt]
  obtain fw : Frame [⟨c.D + BitVec.ofNat 64 (16 * (c.n / 16)), c.n % 16⟩] t₃.mem t₄.mem := by
    rw [hm₄]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
  refine ⟨E₃.others hg₄ (by decide) sp₄ rd₄ wr₄, by rw [rd₄, rd₃'], by rw [wr₄, wr₃'], ?_, ?_⟩
  · refine I.frame.trans ((cT.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega_arith)⟩
  · -- The bytes.
    obtain h₁ : bytesAt t₃.mem c.D (16 * (c.n / 16)) = bytesAt t.mem c.D (16 * (c.n / 16)) := by
      have := Proof.AesGcm.AArch64.bytesAt_frame cT (sep (a := 0) (l := 16 * (c.n / 16)) (by omega_arith)) (by omega_arith)
      rwa [BitVec.add_zero] at this
    obtain h₂ : bytesAt t₃.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16) := by
      rw [Proof.AesGcm.AArch64.bytesAt_frame cT (sep (by omega_arith)) (by omega_arith),
        show c.n % 16 = c.n - 16 * (c.n / 16) by omega_arith, I.rest]
    obtain f₁' : Frame (ctrR c) s.mem t₁.mem := I.frame.trans (by
      rw [← hm₀]; exact f₁.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩)
    obtain hBC : BlockCipher (Spec.Ccm.ctxCiph s.mem c.K c.R) := fun x => Proof.Cmac.aesWith_length _ _ x
    obtain hks : bytesAt t₃.mem (c.W + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph s.mem c.K c.R (Spec.Ccm.ctrBlock nonce (1 + c.n / 16)) := by
      obtain hx := ctr32_ccm (nonce := nonce) (k := 1) (j := 1 + c.n / 16) (by rw [hnl]; have := L.h13; omega_arith)
        (fun i hi => by
          rw [show i = 0 by omega_arith, Nat.add_zero]
          show Spec.Gcm.ofBytes _ = _
          rw [hc₁]) h.out
      rw [Nat.mul_one] at hx
      rw [hm₃, hx, hz₁, ciph_ctrR L f₁', xorFrom_zeros hBC]
    obtain ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph s.mem c.K c.R) nonce (1 + c.n / 16)
      (d := bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * (c.n / 16))) (c.n % 16)) (by rw [length_bytesAt]; omega_arith)
    rw [length_bytesAt, hBC] at ht
    obtain ht' := ht.resolve_right (by omega_arith)
    rw [hm₄, bytesAt_writeBytes_at t₃.mem c.D xs (by rw [hxl]; omega_arith) hn64,
      List.drop_eq_nil_of_le (by rw [length_bytesAt, hxl]; omega_arith), List.append_nil,
      ← bytesAt_prefix t₃.mem c.D (show 16 * (c.n / 16) ≤ c.n by omega_arith), h₁, I.done, hxs, xorBytes, h₂,
      bytesAt_prefix t₃.mem (c.W + BitVec.ofNat 64 80) (show c.n % 16 ≤ 16 by omega_arith), hks, ht']
    conv => rhs; rw [show c.n = 16 * (c.n / 16) + c.n % 16 from (Nat.div_add_mod c.n 16).symm]
    rw [Proof.Cmac.Stream.bytesAt_append, xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 (c.n / 16)]

/-- `x26 = n mod 16`. -/
theorem lastLen_ok {c : Cx} (L : Lay c) {t : State} (E : Env c t) :
    WP isa (.block [imm .x9 15, .logic .and .x .x26 .x28 .x9]) t fun t₀ =>
      t₀.gpr .x26 = BitVec.ofNat 64 (c.n % 16) ∧ Others [.x9, .x26] t t₀ ∧ t₀.mem = t.mem ∧ t₀.sp = t.sp ∧
        t₀.rd = t.rd ∧ t₀.wr = t.wr := by
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₀ ht₀ => ?_
  subst ht₀
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, E.x28]
    rw [and15, toNat_ofNat_of_lt L.n_lt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp [gpr_write, hr]

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok (v : Ctr32Impl) {c : Cx} (L : Lay c) {s : State} (E : Env c s) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) :
    WP isa (ctr v.callee) s fun s' => Env c s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame (ctrR c) s.mem s'.mem ∧
      bytesAt s'.mem c.D c.n = xorFrom (Spec.Ccm.ctxCiph s.mem c.K c.R) nonce 1 (bytesAt s.mem c.D c.n) := by
  have hn64 := L.n_lt
  refine WP.assoc (WP.seq (WP.mono (ctrHead_ok v L hnl E hc0) fun t I => ?_))
  refine WP.seq (WP.mono (lastLen_ok L I.env) fun t₀ ⟨x26₀, hg₀, hm₀, sp₀, rd₀, wr₀⟩ => ?_)
  obtain E₀ : Env c t₀ := I.env.others hg₀ (by decide) sp₀ rd₀ wr₀
  refine WP.ite (decide (c.n % 16 = 0)) (eval_zero x26₀ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n % 16 = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨E₀, by rw [rd₀, I.rd], by rw [wr₀, I.wr], by rw [hm₀]; exact I.frame, ?_⟩
    have hd := I.done
    rw [show 16 * (c.n / 16) = c.n by omega_arith] at hd
    rw [hm₀, hd]
  · exact tail_ok v L hnl hc0 I E₀ hm₀ (by rw [hg₀ _ (by decide), I.x23]) (by rw [hg₀ _ (by decide), I.x25]) x26₀
      rd₀ wr₀ (of_decide_eq_false hf)

end VG.Proof.AesCcm.AArch64
