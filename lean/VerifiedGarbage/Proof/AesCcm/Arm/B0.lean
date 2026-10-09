import VerifiedGarbage.Proof.AesCcm.Arm.Aad

/-!
# AES-CCM on ARMv7: `B₀` (`b0 y`)

Untrusted: everything here is checked by Lean. `flagsCode` computes the
flags `64 [a > 0] + 4 (t − 2) + q − 1` (which is A.2.1's for an even `t`);
`b0Block y` writes `B₀` to `W + 32` from `Ctr₀`, its first byte `q − 1`
replaced by the flags (`le4_flags`) and `[p]₃₂` ORed into its last word, and
zeroes the MAC state at `W + y`; `b0 y` then chains `B₀` into it (`b0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4 store4)
open VG.Impl.AesGcm.Arm (imm addI zero16)
open VG.Proof.AesGcm.Arm (bytesAt_frame runBlock_app_of toNat32 ofNat_sub32 ofNat_add32 z_cmp eval_eq' Keeps
  z_subFlags gpr_subFlags mem_store gpr_store store4_eq add_ofNat_assoc bytes_words sepW)
open VG.Proof.AesCcm (ctxCiph_frame ctrBlock_split length_bytesAt)

/-- The first word of `Ctr₀`, its first byte `c` replaced by `f`. -/
theorem le4_flags (x : BitVec 32) {c f : Nat} (hc : c < 256) (hf : f < 256)
    (h0 : x.extractLsb' 0 8 = BitVec.ofNat 8 c) :
    le4 ((x ^^^ BitVec.ofNat 32 c) ||| BitVec.ofNat 32 f) = BitVec.ofNat 8 f :: (le4 x).drop 1 := by
  have hi : ∀ o j, 8 ≤ o → o + j < 32 → (BitVec.ofNat 32 c).getLsbD (o + j) = false ∧
      (BitVec.ofNat 32 f).getLsbD (o + j) = false := fun o j h₁ h₂ => by
    have hp : 256 ≤ 2 ^ (o + j) := Nat.pow_le_pow_right (n := 2) (i := 8) (by decide) (by omega_arith)
    simp only [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hf hp), Bool.and_false, and_self]
  have ek : ∀ o, 8 ≤ o → o + 8 ≤ 32 →
      ((x ^^^ BitVec.ofNat 32 c) ||| BitVec.ofNat 32 f).extractLsb' o 8 = x.extractLsb' o 8 := fun o h₁ h₂ => by
    ext j hj
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_xor, (hi o j h₁ (by omega_arith)).1,
      (hi o j h₁ (by omega_arith)).2, Bool.xor_false, Bool.or_false]
  have e0 : ((x ^^^ BitVec.ofNat 32 c) ||| BitVec.ofNat 32 f).extractLsb' 0 8 = BitVec.ofNat 8 f := by
    ext j hj
    have hx := congrArg (fun b : BitVec 8 => b.getLsbD j) h0
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, Nat.zero_add,
      BitVec.getLsbD_ofNat] at hx
    simp only [BitVec.getElem_extractLsb', Nat.zero_add, BitVec.getLsbD_or,
      BitVec.getLsbD_xor, hx, BitVec.getLsbD_ofNat, show j < 32 by omega_arith, decide_true, Bool.true_and,
      Bool.xor_self, Bool.false_or]
    rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat]; simp [hj]
  rw [le4_eq, le4_eq, e0, ek 8 (by decide) (by decide), ek 16 (by decide) (by decide),
    ek 24 (by decide) (by decide)]
  rfl

theorem flags_val {tl nl al : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (h7 : 7 ≤ nl)
    (h13 : nl ≤ 13) :
    BitVec.ofNat 8 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64) = Spec.Ccm.flags tl (15 - nl) al := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Spec.Ccm.flags]
  by_cases h : al = 0
  · subst h; simp only [ite_true, Nat.add_zero, show ¬ (0 > 0) by omega_arith, ite_false, Nat.zero_add]; omega_arith
  · simp only [h, ite_false, show al > 0 by omega_arith, ite_true]; omega_arith

theorem shl2 {n : Nat} (hn : n < 2 ^ 30) : BitVec.ofNat 32 n <<< 2 = BitVec.ofNat 32 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

/-- The bytes of `B₀`, as `b0Block` builds them from `Ctr₀`. -/
theorem b0_bytes {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {w₀ w₁ w₂ w₃ : BitVec 32}
    (hc : le4 w₀ ++ le4 w₁ ++ le4 w₂ ++ le4 w₃ = Spec.Ccm.ctrBlock nonce 0) {n f : Nat} (hf : f < 256)
    (hn : n < 256 ^ min (15 - nonce.length) 4) (hn4 : n < 2 ^ 32) :
    le4 ((w₀ ^^^ BitVec.ofNat 32 (14 - nonce.length)) ||| BitVec.ofNat 32 f) ++ le4 w₁ ++ le4 w₂ ++
      le4 (w₃ ||| rev (BitVec.ofNat 32 n)) = BitVec.ofNat 8 f :: (Spec.Ccm.ctrBlock nonce n).drop 1 := by
  have l := Proof.Cmac.length_le4
  have h0 : w₀.extractLsb' 0 8 = BitVec.ofNat 8 (14 - nonce.length) := by
    have := congrArg List.head? hc
    rw [le4_eq w₀] at this
    simp only [List.cons_append, List.head?_cons, Spec.Ccm.ctrBlock, Option.some.injEq] at this
    rw [this]; congr 1; omega_arith
  rw [le4_flags w₀ (by omega_arith) hf h0]
  have hl : (le4 w₀ ++ le4 w₁ ++ le4 w₂).length = 12 := by simp [l]
  rw [ctrBlock_split h7 h13 hn, ← hc, Proof.AesCcm.le4_or, le4_rev_ofNat hn4, List.take_left' hl,
    List.drop_left' hl]
  rw [le4_eq w₀]; rfl

section
variable {k w sp : BitVec 32} {R : Nat} (L : Lay k w sp)
include L

omit L in
/-- The flags of `B₀` in `r0`. -/
theorem flags_ok {s₀ s : State} {nl : Nat} (he : Env k w sp R (14 - nl) s) (hk : Stk w s₀ s) {tl al : Nat}
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (ht4 : 4 ≤ tl)
    (ht16 : tl ≤ 16) (h13 : nl ≤ 13) (hal : al < 2 ^ 32) :
    WP isa flagsCode s fun s' =>
      s'.gpr .r0 = BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨i5, v5⟩ := hk.at 5 (by decide) (show 4 * 5 = 20 from rfl)
  obtain ⟨i1, v1⟩ := hk.at 1 (by decide) (show 4 * 1 = 4 from rfl)
  have h10 := he.r10
  obtain ⟨s₁, run₁, h0₁, hz, g₁, k₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r0 20, .mov .r0 (.shifted .r0 .lsl 2),
      .dp .sub .r0 .r0 (imm 8), .dp .add .r0 .r0 (.reg .r10), .ldrSp .r1 4, .cmp .r1 (imm 0)] s = some s₁ ∧
      s₁.gpr .r0 = BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl)) ∧ s₁.z = decide (al = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [i5, v5, i1, v1], ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v5, etl, h10, imm,
        shl2 (show tl < 2 ^ 30 by omega_arith), ofNat_sub32 (show 8 ≤ 4 * tl by omega_arith) (show 4 * tl < 2 ^ 32 by omega_arith),
        ofNat_add32]
      congr 1; omega_arith
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v1, eal, imm]
      rw [z_cmp hal (by decide)]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (al = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : al = 0 := by simpa using ht
    exact WP.block_nil ⟨by rw [h0₁, h0]; rfl, g₁, k₁⟩
  · have h0 : al ≠ 0 := by simpa using hf
    refine Proof.AesGcm.Arm.WP.run (Q := fun s' => s' = s₁.setReg .r0 (s₁.gpr .r0 + BitVec.ofNat 32 64)) ⟨_, by arun [], rfl⟩
      fun s' hs' => ?_
    subst hs'
    refine ⟨?_, fun r a b => ?_, k₁.trans ⟨rfl, rfl, rfl, rfl⟩⟩
    · simp only [gpr_setReg_self, h0₁, ofNat_add32, h0, ite_false]
    · simp only [gpr_setReg, a, ite_false]; exact g₁ r a b

/-- `B₀` in `B` and the MAC state at `W + y` zeroed. -/
theorem b0Pre_ok {s₀ s : State} {nl : Nat} (he : Env k w sp R (14 - nl) s) (hk : Stk w s₀ s)
    {tl al n : Nat} (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al)
    (en : stackArg s₀ 3 = BitVec.ofNat 32 n) {nonce : List Byte} (hnl : nonce.length = nl) (h7 : 7 ≤ nl)
    (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (hal : al < 2 ^ 32) (hn4 : n < 2 ^ 32)
    (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (.seq flagsCode (.block (b0Block y))) s fun s' =>
      Env k w sp R (14 - nl) s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 32, 16⟩, ⟨State.addr w + BitVec.ofNat 64 y, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 y) 16 = Spec.Cmac.zeros 16 ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 32) 16 = Spec.Ccm.b0 tl nonce al n := by
  refine WP.seq (WP.mono (flags_ok he hk etl eal ht4 ht16 h13 hal) fun s₁ ⟨h0₁, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  obtain ⟨i3, v3⟩ := hk₁.at 3 (by decide) (show 4 * 3 = 12 from rfl)
  have h10 := he₁.r10
  have h11 := he₁.r11
  have r₀ := he₁.perm.wR (show 48 + 4 ≤ 2560 by decide)
  have r₁ := he₁.perm.wR (show 52 + 4 ≤ 2560 by decide)
  have r₂ := he₁.perm.wR (show 56 + 4 ≤ 2560 by decide)
  have r₃ := he₁.perm.wR (show 60 + 4 ≤ 2560 by decide)
  have w₀ := he₁.perm.wW (show 32 + 4 ≤ 2560 by decide)
  have w₁ := he₁.perm.wW (show 36 + 4 ≤ 2560 by decide)
  have w₂ := he₁.perm.wW (show 40 + 4 ≤ 2560 by decide)
  have w₃ := he₁.perm.wW (show 44 + 4 ≤ 2560 by decide)
  have q : ∀ a d, a + 4 ≤ d ∨ d + 4 ≤ a → a + 4 ≤ 2560 → d + 4 ≤ 2560 →
      (⟨State.addr w + BitVec.ofNat 64 a, 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 4⟩ :=
    fun a d h₁ h₂ h₃ => L.w_w h₁ h₂ h₃
  have p₁ := fun m v => sepW (m := m) (v := v) (q 52 32 (by decide) (by decide) (by decide))
  have p₂ := fun m v => sepW (m := m) (v := v) (q 56 32 (by decide) (by decide) (by decide))
  have p₃ := fun m v => sepW (m := m) (v := v) (q 56 36 (by decide) (by decide) (by decide))
  have p₄ := fun m v => sepW (m := m) (v := v) (q 60 32 (by decide) (by decide) (by decide))
  have p₅ := fun m v => sepW (m := m) (v := v) (q 60 36 (by decide) (by decide) (by decide))
  have p₆ := fun m v => sepW (m := m) (v := v) (q 60 40 (by decide) (by decide) (by decide))
  have e := fun d (hd : d < 2560) => L.wA (d := d) hd
  have p₇ := fun m v => sepW (m := m) (v := v) (hk₁.slot_w 3 (by decide) (show 4 * 3 = 12 from rfl)
    (d := 32) (by decide))
  have p₈ := fun m v => sepW (m := m) (v := v) (hk₁.slot_w 3 (by decide) (show 4 * 3 = 12 from rfl)
    (d := 36) (by decide))
  have p₉ := fun m v => sepW (m := m) (v := v) (hk₁.slot_w 3 (by decide) (show 4 * 3 = 12 from rfl)
    (d := 40) (by decide))
  let m := s₁.mem
  let W := State.addr w
  let f := 4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64
  have hf : f < 256 := by simp only [f]; split <;> omega_arith
  obtain ⟨s₂, run₂, hm₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldr .r1 .r11 c0O, .dp .eor .r1 .r1 (.reg .r10),
      .dp .orr .r1 .r1 (.reg .r0), .str .r1 .r11 bO, .ldr .r1 .r11 (c0O + 4), .str .r1 .r11 (bO + 4),
      .ldr .r1 .r11 (c0O + 8), .str .r1 .r11 (bO + 8), .ldr .r1 .r11 (c0O + 12), .ldrSp .r2 12, .rev .r2 .r2,
      .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r11 (bO + 12)] s₁ = some s₂ ∧
      s₂.mem = store4 m (W + BitVec.ofNat 64 32)
        ((m.readW (W + BitVec.ofNat 64 48) 32 ^^^ BitVec.ofNat 32 (14 - nl)) ||| BitVec.ofNat 32 f)
        (m.readW (W + BitVec.ofNat 64 52) 32) (m.readW (W + BitVec.ofNat 64 56) 32)
        (m.readW (W + BitVec.ofNat 64 60) 32 ||| rev (BitVec.ofNat 32 n)) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧ (s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.sp = s₁.sp) := by
    refine ⟨_, by simp only [c0O, bO]; arun [h10, h11, i3, v3, e, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃,
      p₄, p₅, p₆, p₇, p₈, p₉], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h10, h0₁, v3, en,
        store4_eq, add_ofNat_assoc, m, W, f]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) k₂.2.2 k₂.1 k₂.2.1
  obtain ⟨s₃, run₃, hm₃, g₃, rd₃, wr₃, sp₃, -⟩ := zero16_ok L he₂ (d := y) (by omega_arith) (by omega_arith)
  refine WP.of_runBlock ⟨s₃, by
    rw [show b0Block y = [.ldr .r1 .r11 c0O, .dp .eor .r1 .r1 (.reg .r10),
      .dp .orr .r1 .r1 (.reg .r0), .str .r1 .r11 bO, .ldr .r1 .r11 (c0O + 4), .str .r1 .r11 (bO + 4),
      .ldr .r1 .r11 (c0O + 8), .str .r1 .r11 (bO + 8), .ldr .r1 .r11 (c0O + 12), .ldrSp .r2 12, .rev .r2 .r2,
      .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r11 (bO + 12)] ++ zero16 y from rfl]
    exact runBlock_app_of run₂ run₃, ?_⟩
  have dY : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [hm₂, show m = s.mem from k₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have f₃ : Frame [⟨W + BitVec.ofNat 64 y, 16⟩] s₂.mem s₃.mem := by
    rw [hm₃]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) sp₃ rd₃ wr₃,
    by rw [rd₃, k₂.1, k₁.rd], by rw [wr₃, k₂.2.1, k₁.wr], by rw [sp₃, k₂.2.2, k₁.sp],
    (f₂.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_), ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · rw [hm₃]; exact store4_zero_bytes' _ _
  · rw [bytesAt_frame f₃ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dY) (by decide),
      hm₂, Proof.Cmac.bytesAt_store4]
    have hw := hc0
    rw [bytes_words] at hw
    simp only [add_ofNat_assoc] at hw
    rw [← k₁.mem] at hw
    have hnm : n < 256 ^ min (15 - nonce.length) 4 := by
      rw [hnl]
      rcases Nat.le_total (15 - nl) 4 with h | h
      · rw [Nat.min_eq_left h]; exact hn
      · rw [Nat.min_eq_right h]; exact Nat.lt_of_lt_of_le hn4 (by decide)
    have hb := b0_bytes (f := f) (by omega_arith) (by omega_arith) hw hf hnm hn4
    rw [hnl] at hb
    rw [hb]
    simp only [Spec.Ccm.b0, Spec.Ccm.ctrBlock, List.drop_succ_cons, List.drop_zero, hnl, f]
    rw [flags_val ht4 ht16 hte h7 h13, List.cons_append, List.drop_succ_cons, List.drop_zero, List.cons_append]

end

end VG.Proof.AesCcm.Arm
