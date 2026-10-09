import VerifiedGarbage.Proof.AesCcm.AArch64.Tag

/-!
# AES-CCM on AArch64: a chunk of counter mode (`ctrChunk`)

Untrusted: everything here is checked by Lean. After `b` whole blocks
(`CtrInv`), `ctrChunk` encrypts `k = min (n/16 − b, 2³² − (1 + b) mod 2³²)`
more by `vg_aes_ctr32` from `Ctr₁₊ᵦ`, whose counters do not wrap around in
their low 32 bits, so that they are CCM's (`chunk_ok`).
-/

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

theorem low32 (x : Nat) : (BitVec.ofNat 64 x).setWidth 32 + BitVec.ofNat 32 0 = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- `k = min (m, 2³² − (1 + b) mod 2³²)` in `x26`, for `m` blocks left. -/
theorem kSel_ok {b m : Nat} {t : State} (h24 : t.gpr .x24 = BitVec.ofNat 64 m)
    (h25 : t.gpr .x25 = BitVec.ofNat 64 (1 + b)) (hm : m < 2 ^ 60) :
    WP isa (.seq (.block [.addImm .w .x9 .x25 0, .movz .x .x10 1 2, .sub .x .x10 .x10 .x9, .sub .x .x11 .x24 .x10,
        .lsr .x .x11 .x11 63]) (.ite (.zero .x .x11) (.block [mov .x26 .x10]) (.block [mov .x26 .x24]))) t
      fun t₂ => t₂.gpr .x26 = BitVec.ofNat 64 (min m (2 ^ 32 - (1 + b) % 2 ^ 32)) ∧
        Others [.x9, .x10, .x11, .x26] t t₂ ∧ t₂.mem = t.mem ∧ t₂.sp = t.sp ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  have hj := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide)
  obtain ⟨t₁, run₁, x10₁, x11₁, hg₁, hm₁, sp₁, rd₁, wr₁⟩ : ∃ t₁, runBlock isa
      [.addImm .w .x9 .x25 0, .movz .x .x10 1 2, .sub .x .x10 .x10 .x9, .sub .x .x11 .x24 .x10,
        .lsr .x .x11 .x11 63] t = some t₁ ∧
      t₁.gpr .x10 = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) ∧
      t₁.gpr .x11 = BitVec.ofNat 64 (if m < 2 ^ 32 - (1 + b) % 2 ^ 32 then 1 else 0) ∧
      Others [.x9, .x10, .x11] t t₁ ∧ t₁.mem = t.mem ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    have k1 : (BitVec.setWidth 64 (1 : BitVec 16) <<< 32 : BitVec 64) = BitVec.ofNat 64 (2 ^ 32) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rfl
    have hx10 : BitVec.ofNat 64 (2 ^ 32) - BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (1 + b))) =
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
  have h7 : 7 ≤ nonce.length := by rw [hnl]; exact L.h7
  have h13 : nonce.length ≤ 13 := by rw [hnl]; exact L.h13
  have hq16 : c.n / 16 < 256 ^ (15 - nonce.length) := by
    rw [hnl]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) L.hn
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (Proof.AesGcm.AArch64.WP.run ⟨_, by carun [], rfl⟩ fun t₁ ht₁ => ?_)
  have hg₁ : Others [.x9] t t₁ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [← ht₁]; simp [gpr_write, hr]
  have E₁ : Env c t₁ := E.others hg₁ (by decide) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl) (by rw [← ht₁]; rfl)
  have h9 : t₁.gpr .x9 = BitVec.ofNat 64 (1 + b) := by rw [← ht₁]; simp [gpr_write, h25]
  have hm₁ : t₁.mem = t.mem := by rw [← ht₁]; rfl
  refine WP.block_append (WP.mono (ctrAt_ok E₁ h7 h13 (by rw [hm₁]; exact hc0) (i := 1 + b) (by omega_arith) h9)
    fun t₂ ⟨f₂, hc₂, hg₂, sp₂, rd₂, wr₂⟩ => ?_)
  have E₂ : Env c t₂ := E₁.others hg₂ (by decide) sp₂ rd₂ wr₂
  refine Proof.AesGcm.AArch64.WP.run ⟨_, by carun [ctrArgs], rfl⟩ fun t₅ ht₅ => ?_
  have hg₅ : Others [.x0, .x1, .x2, .x3, .x4, .x5] t₂ t₅ := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; rw [← ht₅]; simp [gpr_write, hr]
  have E₅ : Env c t₅ := E₂.others hg₅ (by decide) (by rw [← ht₅]; rfl) (by rw [← ht₅]; rfl) (by rw [← ht₅]; rfl)
  have hm₅ : t₅.mem = t₂.mem := by rw [← ht₅]; rfl
  have g₂ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → t₂.gpr r = t.gpr r := fun r a b' c' => by
    rw [hg₂ r (by simp [a, b', c']), hg₁ r (by simp [a])]
  have hS := (L.bufD E₂.perm).slice (a := 16 * b) (k := 16 * k) (by omega_arith)
  have hqo : (⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 64, 16⟩ :=
    hS.wd (by decide)
  have hqk : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩ :=
    L.k_d.sub_right (Offset.sub_base c.D (by omega_arith))
  have hqw : Covers [⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩] t₅.wr :=
    covers_off E₅.perm.d (by omega_arith) L.n_lt
  have hS₅ := hS.of_eq (s' := t₅) (by rw [← ht₅]; rfl) (by rw [← ht₅]; rfl)
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
  have cR : Frame [⟨c.W + BitVec.ofNat 64 64, 16⟩, ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩] t.mem t₇.mem := by
    rw [hm₇]
    refine (f₅.sub fun r hr => ?_).trans (h.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have toR : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨c.W + BitVec.ofNat 64 384, 2048⟩], ∃ r' ∈ ctrR c, Region.Sub r r' := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨c.D, c.n⟩, by simp, Offset.sub_base c.D (by omega_arith)⟩
    · exact ⟨⟨c.W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
  -- Separation of the data from what the chunk wrote.
  have sep : ∀ {a l : Nat}, (a + l ≤ 16 * b ∨ 16 * (b + k) ≤ a) → a + l ≤ c.n →
      ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨c.D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
        ⟨c.W + BitVec.ofNat 64 384, 2048⟩], (⟨c.D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l ha hl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
    · exact Offset.disjoint c.D (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (L.d_w.sub_left (Offset.sub_base c.D hl)).sub_right (Lay.wSub (by decide))
  have hbk : 16 * (b + k) = 16 * b + 16 * k := Nat.mul_add _ _ _
  refine ⟨I.frame.trans (cR.sub toR), ?_, ?_⟩
  · -- The blocks done.
    have h₁ : bytesAt t₇.mem c.D (16 * b) = bytesAt t.mem c.D (16 * b) := by
      have := Proof.AesGcm.AArch64.bytesAt_frame cR (sep (a := 0) (l := 16 * b) (.inl (by omega_arith)) (by omega_arith))
        (by omega_arith)
      rwa [BitVec.add_zero] at this
    have hinc : ∀ i < k, Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt t₅.mem (c.W + BitVec.ofNat 64 64)) =
        Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce (1 + b + i)) := fun i hi => by
      show Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.ofBytes (bytesAt t₅.mem (c.W + BitVec.ofNat 64 64) 16)) = _
      rw [hc₅]
      exact repeat_inc32_ctrBlock (by rw [hnl]; exact L.h7) (by rw [hnl]; exact L.h13) hk32
        (by rw [hnl]; have := Nat.lt_of_le_of_lt (Nat.div_le_self c.n 16) L.hn; omega_arith) i hi
    have hx := ctr32_ccm (by rw [hnl]; have := L.h13; omega_arith) hinc h.out
    have f₅' : Frame (ctrR c) s.mem t₅.mem := I.frame.trans (f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨c.W + BitVec.ofNat 64 64, 32⟩, by simp, Region.sub_prefix (by decide)⟩)
    have hx₅ : bytesAt t₅.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) =
        bytesAt s.mem (c.D + BitVec.ofNat 64 (16 * b)) (16 * k) := by
      rw [bytesAt_prefix t₅.mem _ (show 16 * k ≤ c.n - 16 * b by omega_arith),
        bytesAt_prefix s.mem _ (show 16 * k ≤ c.n - 16 * b by omega_arith), ← I.rest,
        Proof.AesGcm.AArch64.bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (L.d_w.sub_left (Offset.sub_base c.D (by omega_arith))).sub_right (Lay.wSub (by decide))) (by omega_arith)]
    rw [hbk, Proof.Cmac.Stream.bytesAt_append, Proof.Cmac.Stream.bytesAt_append, h₁, I.done, hm₇, hx, hx₅,
      ciph_ctrR L f₅', xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 b]
  · -- The rest of the data.
    have hR' := Proof.AesGcm.AArch64.bytesAt_frame cR
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
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_arith
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega_arith
  have hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32 := by
    rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_arith
  have E₂ : Env c t₂ := I.env.others hg₂ (by decide) sp₂ rd₂ wr₂
  have hc0t : bytesAt t₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [hm₂, Proof.AesGcm.AArch64.bytesAt_frame I.frame (ctrR_disj L (.inl (by decide))) (by decide), hc0]
  refine WP.seq (WP.mono (setup_ok L hnl hkb hk1 E₂ hc0t (by rw [hg₂ _ (by decide), I.x23])
    (by rw [hg₂ _ (by decide), I.x25]) x26₂) fun t₅ ⟨E₅, C₅, f₅, hc₅, hg₅, rd₅, wr₅⟩ => ?_)
  refine WP.seq (WP.mono (ctr_call v C₅) fun t₆ h => ?_)
  have E₆ : Env c t₆ := E₅.of_saved h.saved h.sp h.rd h.wr
  have sv : ∀ r ∈ [Reg.x23, .x24, .x25, .x26], t₆.gpr r = t₂.gpr r := fun r hr => by
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
