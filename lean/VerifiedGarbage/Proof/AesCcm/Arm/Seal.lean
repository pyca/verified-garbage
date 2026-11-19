module

import VerifiedGarbage.Proof.AesGcm.Arm.Entry
import VerifiedGarbage.Proof.AesCcm.Bytes
public import VerifiedGarbage.Proof.AesCcm.Arm.Aad
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesCcm.Arm.Crypt
import VerifiedGarbage.Proof.AesGcm.Arm.Env
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.AesGcm.Arm.Run
public import VerifiedGarbage.Proof.AesGcm.Arm.Fn
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.AesGcm.Arm.Tag
import VerifiedGarbage.Proof.Cmac.Frame

/-! ### `AesCcm.Arm.Mac`, which this module and modules that import it used -/

section

/-! ### `AesCcm.Arm.B0`, which this module and modules that import it used -/

section

/-!
# AES-CCM on ARMv7: `B₀` (`b0 y`)

Untrusted: everything here is checked by Lean. `flagsCode` computes the
flags `64 [a > 0] + 4 (t − 2) + q − 1` (which is A.2.1's for an even `t`);
`b0Block y` writes `B₀` to `W + 32` from `Ctr₀`, its first byte `q − 1`
replaced by the flags (`le4_flags`) and `[p]₃₂` ORed into its last word, and
zeroes the MAC state at `W + y`; `b0 y` then chains `B₀` into it (`b0_ok`).
-/

@[expose] public section

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
  obtain hi : ∀ o j, 8 ≤ o → o + j < 32 → (BitVec.ofNat 32 c).getLsbD (o + j) = false ∧
      (BitVec.ofNat 32 f).getLsbD (o + j) = false := fun o j h₁ h₂ => by
    obtain hp : 256 ≤ 2 ^ (o + j) := Nat.pow_le_pow_right (n := 2) (i := 8) (by decide) (by omega_arith)
    simp only [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hf hp), Bool.and_false, and_self]
  obtain ek : ∀ o, 8 ≤ o → o + 8 ≤ 32 →
      ((x ^^^ BitVec.ofNat 32 c) ||| BitVec.ofNat 32 f).extractLsb' o 8 = x.extractLsb' o 8 := fun o h₁ h₂ => by
    ext j hj
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_xor, (hi o j h₁ (by omega_arith)).1,
      (hi o j h₁ (by omega_arith)).2, Bool.xor_false, Bool.or_false]
  obtain e0 : ((x ^^^ BitVec.ofNat 32 c) ||| BitVec.ofNat 32 f).extractLsb' 0 8 = BitVec.ofNat 8 f := by
    ext j hj
    obtain hx := congrArg (fun b : BitVec 8 => b.getLsbD j) h0
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
  obtain h0 : w₀.extractLsb' 0 8 = BitVec.ofNat 8 (14 - nonce.length) := by
    have := congrArg List.head? hc
    rw [le4_eq w₀] at this
    simp only [List.cons_append, List.head?_cons, Spec.Ccm.ctrBlock, Option.some.injEq] at this
    rw [this]; congr 1; omega_arith
  rw [le4_flags w₀ (by omega_arith) hf h0]
  obtain hl : (le4 w₀ ++ le4 w₁ ++ le4 w₂).length = 12 := by simp [l]
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
  obtain he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  obtain hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  obtain ⟨i3, v3⟩ := hk₁.at 3 (by decide) (show 4 * 3 = 12 from rfl)
  have h10 := he₁.r10
  have h11 := he₁.r11
  obtain r₀ := he₁.perm.wR (show 48 + 4 ≤ 2560 by decide)
  obtain r₁ := he₁.perm.wR (show 52 + 4 ≤ 2560 by decide)
  obtain r₂ := he₁.perm.wR (show 56 + 4 ≤ 2560 by decide)
  obtain r₃ := he₁.perm.wR (show 60 + 4 ≤ 2560 by decide)
  obtain w₀ := he₁.perm.wW (show 32 + 4 ≤ 2560 by decide)
  obtain w₁ := he₁.perm.wW (show 36 + 4 ≤ 2560 by decide)
  obtain w₂ := he₁.perm.wW (show 40 + 4 ≤ 2560 by decide)
  obtain w₃ := he₁.perm.wW (show 44 + 4 ≤ 2560 by decide)
  obtain q : ∀ a d, a + 4 ≤ d ∨ d + 4 ≤ a → a + 4 ≤ 2560 → d + 4 ≤ 2560 →
      (⟨State.addr w + BitVec.ofNat 64 a, 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 4⟩ :=
    fun a d h₁ h₂ h₃ => L.w_w h₁ h₂ h₃
  obtain p₁ := fun m v => sepW (m := m) (v := v) (q 52 32 (by decide) (by decide) (by decide))
  obtain p₂ := fun m v => sepW (m := m) (v := v) (q 56 32 (by decide) (by decide) (by decide))
  obtain p₃ := fun m v => sepW (m := m) (v := v) (q 56 36 (by decide) (by decide) (by decide))
  obtain p₄ := fun m v => sepW (m := m) (v := v) (q 60 32 (by decide) (by decide) (by decide))
  obtain p₅ := fun m v => sepW (m := m) (v := v) (q 60 36 (by decide) (by decide) (by decide))
  obtain p₆ := fun m v => sepW (m := m) (v := v) (q 60 40 (by decide) (by decide) (by decide))
  obtain e := fun d (hd : d < 2560) => L.wA (d := d) hd
  obtain p₇ := fun m v => sepW (m := m) (v := v) (hk₁.slot_w 3 (by decide) (show 4 * 3 = 12 from rfl)
    (d := 32) (by decide))
  obtain p₈ := fun m v => sepW (m := m) (v := v) (hk₁.slot_w 3 (by decide) (show 4 * 3 = 12 from rfl)
    (d := 36) (by decide))
  obtain p₉ := fun m v => sepW (m := m) (v := v) (hk₁.slot_w 3 (by decide) (show 4 * 3 = 12 from rfl)
    (d := 40) (by decide))
  let m := s₁.mem
  let W := State.addr w
  let f := 4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64
  obtain hf : f < 256 := by simp only [f]; split <;> omega_arith
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
  obtain he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide)) k₂.2.2 k₂.1 k₂.2.1
  obtain ⟨s₃, run₃, hm₃, g₃, rd₃, wr₃, sp₃, -⟩ := zero16_ok L he₂ (d := y) (by omega_arith) (by omega_arith)
  refine WP.of_runBlock ⟨s₃, by
    rw [show b0Block y = [.ldr .r1 .r11 c0O, .dp .eor .r1 .r1 (.reg .r10),
      .dp .orr .r1 .r1 (.reg .r0), .str .r1 .r11 bO, .ldr .r1 .r11 (c0O + 4), .str .r1 .r11 (bO + 4),
      .ldr .r1 .r11 (c0O + 8), .str .r1 .r11 (bO + 8), .ldr .r1 .r11 (c0O + 12), .ldrSp .r2 12, .rev .r2 .r2,
      .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r11 (bO + 12)] ++ zero16 y from rfl]
    exact runBlock_app_of run₂ run₃, ?_⟩
  obtain dY : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 y, 16⟩ := by
    rcases hy with rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₂.mem := by
    rw [hm₂, show m = s.mem from k₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  obtain f₃ : Frame [⟨W + BitVec.ofNat 64 y, 16⟩] s₂.mem s₃.mem := by
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
    obtain hnm : n < 256 ^ min (15 - nonce.length) 4 := by
      rw [hnl]
      rcases Nat.le_total (15 - nl) 4 with h | h
      · rw [Nat.min_eq_left h]; exact hn
      · rw [Nat.min_eq_right h]; exact Nat.lt_of_lt_of_le hn4 (by decide)
    obtain hb := b0_bytes (f := f) (by omega_arith) (by omega_arith) hw hf hnm hn4
    rw [hnl] at hb
    rw [hb]
    simp only [Spec.Ccm.b0, Spec.Ccm.ctrBlock, List.drop_succ_cons, List.drop_zero, hnl, f]
    rw [flags_val ht4 ht16 hte h7 h13, List.cons_append, List.drop_succ_cons, List.drop_zero, List.cons_append]

end

end VG.Proof.AesCcm.Arm

end

end

/-!
# AES-CCM on ARMv7: the MAC (`mac y`)

Untrusted: everything here is checked by Lean. `b0 y` chains `B₀` into a
zeroed MAC state at `W + y` (`b0_ok`); `mac y` then chains the formatted
associated data and the payload padded: CBC-MAC of the formatted blocks
(`mac_ok`), whose first `t` bytes are CCM's MAC (`Proof.AesCcm.mac_eq`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (Keeps)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt format_eq)

section
variable {k w sp : BitVec 32} {R : Nat} (L : Lay k w sp)
include L

/-- `B₀` chained into a zeroed MAC state at `W + y`. -/
theorem b0_ok {s₀ s : State} {nl : Nat} (he : Env k w sp R (14 - nl) s) (hk : Stk w s₀ s)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {tl al n : Nat} (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (en : stackArg s₀ 3 = BitVec.ofNat 32 n) {nonce : List Byte}
    (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 32) (hn4 : n < 2 ^ 32) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) :
    WP isa (b0 y) s (MacStep k w sp R (14 - nl) s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (Spec.Cmac.zeros 16) [Spec.Ccm.b0 tl nonce al n])) := by
  refine seq_assoc (WP.seq (WP.mono (b0Pre_ok L he hk etl eal en hnl h7 h13 ht4 ht16 hte hal hn4 hn hc0 hy)
    fun s₃ ⟨he₃, rd₃, wr₃, _, f₃, hz, hB⟩ => ?_))
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.mono (updBlock_ok L he₃ hR hy) fun s₄ ⟨he₄, rd₄, wr₄, _, f₄, o₄⟩ =>
    ⟨he₄, ?_, ?_, by rw [rd₄, rd₃], by rw [wr₄, wr₃]⟩
  · refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact sub_mac (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact sub_mac (by simp)
  · rw [o₄, hz, hB, ctxCiph_frame f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.k_w' (by decide)
      · exact L.k_w' (by omega_using [hy])) hRb]

/-- CBC-MAC of the formatted nonce, associated data and payload into `W + y`. -/
theorem mac_ok {s₀ s : State} {nl : Nat} (he : Env k w sp R (14 - nl) s) (hk : Stk w s₀ s) (hsp₀ : s₀.sp = sp)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {A D : BitVec 32} {tl al n : Nat} (eA : stackArg s₀ 0 = A)
    (eal : stackArg s₀ 1 = BitVec.ofNat 32 al) (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n)
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) {nonce : List Byte}
    (hnl : nonce.length = nl) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0)
    (hal : al < 2 ^ 32) (hn4 : n < 2 ^ 32) (hn : n < 256 ^ (15 - nl))
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0) {y : Nat}
    (hy : y = 0 ∨ y = 112) (hA : Buf w sp s A al) (hD : Buf w sp s D n) :
    WP isa (mac y) s (MacStep k w sp R (14 - nl) s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (State.addr k) R) (Spec.Cmac.zeros 16)
        (Spec.Ccm.format tl nonce (bytesAt s.mem (State.addr A) al) (bytesAt s.mem (State.addr D) n)))) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hy16 : y + 16 ≤ 2560 := by omega_using [hy]
  refine WP.seq (WP.mono (b0_ok L he hk hR etl eal en hnl h7 h13 ht4 ht16 hte hal hn4 hn hc0 hy)
    fun s₁ M₁ => ?_)
  have hk₁ := hk.mac hsp₀ hy16 M₁.frame (by rw [M₁.env.sp, he.sp]) M₁.rd M₁.wr
  refine WP.seq (WP.mono (aad_ok L M₁.env hR hy hk₁ eA eal hal (hA.of_eq M₁.rd M₁.wr)) fun s₂ M₂ => ?_)
  have hk₂ := hk₁.mac hsp₀ hy16 M₂.frame (by rw [M₂.env.sp, M₁.env.sp]) M₂.rd M₂.wr
  obtain ⟨s₃, run₃, h4₃, h5₃, g₃, k₃⟩ := dataLd_ok hk₂ eD en
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have he₃ := M₂.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) k₃.sp k₃.rd k₃.wr
  have rd₃ : s₃.rd = s.rd := by rw [k₃.rd, M₂.rd, M₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [k₃.wr, M₂.wr, M₁.wr]
  refine WP.mono (absorbPad_ok L he₃ hR hy (fun _ => hD.of_eq rd₃ wr₃) hn4 h4₃ h5₃) fun s₄ A₄ => ?_
  have f₂ : Frame (macR w sp y) s.mem s₂.mem := M₁.frame.trans M₂.frame
  have f₃ : Frame (macR w sp y) s.mem s₃.mem := by rw [k₃.mem]; exact f₂
  have hkm := k_macR L hy16
  refine ⟨A₄.env, f₃.trans A₄.frame, ?_, by rw [A₄.rd, rd₃], by rw [A₄.wr, wr₃]⟩
  have hl : nonce.length ≤ 15 := by omega_using [hnl, h13]
  rw [A₄.out, k₃.mem, M₂.out, M₁.out, ctxCiph_frame f₂ hkm hRb, ctxCiph_frame M₁.frame hkm hRb,
    buf_kept hD hy16 f₂, buf_kept hA hy16 M₁.frame, format_eq tl hl, length_bytesAt, length_bytesAt,
    Proof.Cmac.chain_append, Proof.Cmac.chain_append]

end

end VG.Proof.AesCcm.Arm

end

end

/-! ### `AesCcm.Arm.Args`, which this module and modules that import it used -/

section

/-!
# AES-CCM on ARMv7: the arguments, and what the pieces write

Untrusted: everything here is checked by Lean. What the contracts'
preconditions give about the arguments (`Args`, `TagB`, `args_of_seal`,
`args_of_open`), and the regions
the pieces after the entry write (`mutR`: `W` but for our caller's saved
registers, the stack below `sp` and the data), which miss the saved
registers, the key schedule, the stack arguments, the nonce and the
associated data.
-/

@[expose] public section

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (covers_left covers_of_mem savedR bytesAt_frame ArgsKeep)

/-- What the arguments of `seal` and `open` are. -/
structure Args (s : State) (k w N A D : BitVec 32) (R nl al n tl : Nat) : Prop where
  lay : Lay k w s.sp
  perm : Perm k w s
  stk : Stk w s s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf w s.sp s N nl
  aad : Buf w s.sp s A al
  data : Dat k w s.sp s D n
  nd : (⟨State.addr N, nl⟩ : Region).Disjoint ⟨State.addr D, n⟩
  ad : (⟨State.addr A, al⟩ : Region).Disjoint ⟨State.addr D, n⟩
  da : (⟨State.addr D, n⟩ : Region).Disjoint (args s 7)
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  n32 : n < 2 ^ 32
  al32 : al < 2 ^ 32

/-- The tag, the `tl` bytes at `T`: apart from the data, `W` and the stack
below `sp`. -/
structure TagB (w sp D : BitVec 32) (n : Nat) (T : BitVec 32) (tl : Nat) : Prop where
  d : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr D, n⟩
  w : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk : (blw sp).Disjoint ⟨State.addr T, tl⟩
  wrap : T.toNat + tl ≤ 2 ^ 32

/-- `Args` and `TagB` from the layout, with the buffers covered as each
function's permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨State.addr (s.gpr .r0), 240⟩] (s.rd ++ s.wr))
    (hN : Covers [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨State.addr (arg s 0), (arg s 1).toNat⟩] (s.rd ++ s.wr)) (ha : args s 7 ∈ s.rd)
    (hD : Covers [⟨State.addr (arg s 2), (arg s 3).toNat⟩] s.wr) (hW : Covers [⟨State.addr (arg s 6), 2560⟩] s.wr) :
    Args s (s.gpr .r0) (arg s 6) (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
        (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat ∧
      TagB (arg s 6) s.sp (arg s 2) (arg s 3).toNat (arg s 4) (arg s 5).toNat := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, b1, b2, b3, b4, b5, f1, f2, f3, f4, f5, sp16, sp28, hR,
    hv, t1, t2, t3, t4⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact ⟨{
    lay := ⟨f1, f5, sp16, d2, b1, b5⟩
    perm := ⟨hk, hW⟩
    stk := ⟨ArgsKeep.refl 7 s, sp28, ha, d9.symm⟩
    rounds := hR
    nonce := ⟨hN, f2, d4, b2⟩
    aad := ⟨hA, f3, d6, b3⟩
    data := ⟨⟨covers_left hD, f4, d7, b4⟩, hD, d1⟩
    nd := d3
    ad := d5
    da := d8
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    n32 := BitVec.isLt _
    al32 := BitVec.isLt _ }, ⟨t1, t2, t3, t4⟩⟩

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    (Args s (s.gpr .r0) (arg s 6) (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
        (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat ∧
      TagB (arg s 6) s.sp (arg s 2) (arg s 3).toNat (arg s 4) (arg s 5).toNat) ∧
      Covers [⟨State.addr (arg s 4), (arg s 5).toNat⟩] s.wr ∧
      (⟨State.addr (arg s 4), (arg s 5).toNat⟩ : Region).Disjoint (args s 7) := by
  obtain ⟨hrd, hwr, hl, ht⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
      ⟨State.addr (arg s 0), (arg s 1).toNat⟩, args s 7], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region), ⟨State.addr (arg s 4), (arg s 5).toNat⟩,
      ⟨State.addr (arg s 6), 2560⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (by rw [hrd]; simp)
    (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp), ht⟩

/-- `open`'s arguments, and its received tag, to read. -/
theorem args_of_open {s : State} (h : openPre s) :
    (Args s (s.gpr .r0) (arg s 6) (s.gpr .r2) (arg s 0) (arg s 2) (s.gpr .r1).toNat (s.gpr .r3).toNat
        (arg s 1).toNat (arg s 3).toNat (arg s 5).toNat ∧
      TagB (arg s 6) s.sp (arg s 2) (arg s 3).toNat (arg s 4) (arg s 5).toNat) ∧
      Covers [⟨State.addr (arg s 4), (arg s 5).toNat⟩] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨State.addr (s.gpr .r0), 240⟩ : Region), ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩,
      ⟨State.addr (arg s 0), (arg s 1).toNat⟩, ⟨State.addr (arg s 4), (arg s 5).toNat⟩, args s 7],
      Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨State.addr (arg s 2), (arg s 3).toNat⟩ : Region), ⟨State.addr (arg s 6), 2560⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (by rw [hrd]; simp)
    (mwr _ (by simp)) (mwr _ (by simp)), mrd _ (by simp)⟩

/-- What the pieces after the entry write: `W` but for the saved registers,
the stack below `sp` and the data. -/
abbrev mutR (w sp D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr w, 128⟩, ⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, blw sp, ⟨State.addr D, n⟩]

theorem w_mut {w sp D : BitVec 32} {n a l : Nat} (h : a + l ≤ 128 ∨ (164 ≤ a ∧ a + l ≤ 2560)) :
    ∃ r' ∈ mutR w sp D n, Region.Sub ⟨State.addr w + BitVec.ofNat 64 a, l⟩ r' := by
  rcases h with h | h
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, by simp, Offset.sub _ h.1 (by omega_using [h])⟩

theorem blw_mut {w sp D : BitVec 32} {n : Nat} : ∃ r' ∈ mutR w sp D n, Region.Sub (blw sp) r' :=
  ⟨_, by simp, fun _ h => h⟩

theorem macR_mut {w sp D : BitVec 32} {n y : Nat} (hy : y = 0 ∨ y = 112) :
    ∀ r ∈ macR w sp y, ∃ r' ∈ mutR w sp D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_mut (.inl (by omega_using [hy]))
  · exact w_mut (.inl (by decide))
  · exact w_mut (.inr ⟨by decide, by decide⟩)
  · exact blw_mut

theorem ctrR_mut {w sp D : BitVec 32} {n : Nat} : ∀ r ∈ ctrR w sp D n, ∃ r' ∈ mutR w sp D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_mut (.inl (by decide))
  · exact w_mut (.inr ⟨by decide, by decide⟩)
  · exact blw_mut
  · exact ⟨_, by simp, fun _ h => h⟩

section
variable {s : State} {k w N A D : BitVec 32} {R nl al n tl : Nat} (Ar : Args s k w N A D R nl al n tl)
include Ar

theorem saved_mut : ∀ r ∈ mutR w s.sp D n, (savedR w).Disjoint r := by
  have L := Ar.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa using L.w_w (a := 128) (n := 36) (d := 0) (m := 128) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm
  · exact (Ar.data.buf.w.sub_right (Lay.wSub (by decide))).symm

theorem k_mut : ∀ r ∈ mutR w s.sp D n, (⟨State.addr k, 240⟩ : Region).Disjoint r := by
  have L := Ar.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w' (by decide)
  · exact L.stk_k.symm
  · exact Ar.data.k

theorem args_mut : ∀ r ∈ mutR w s.sp D n, (args s 7).Disjoint r := by
  have L := Ar.lay
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Ar.stk.aw.sub_right (Region.sub_prefix (by decide))
  · exact Ar.stk.aw.sub_right (Lay.wSub (by decide))
  · exact Ar.stk.blw_args rfl
  · exact Ar.da.symm

theorem aad_mut : ∀ r ∈ mutR w s.sp D n, (⟨State.addr A, al⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Ar.aad.w.sub_right (Region.sub_prefix (by decide))
  · exact Ar.aad.w.sub_right (Lay.wSub (by decide))
  · exact Ar.aad.stk.symm
  · exact Ar.ad

end

/-- The tag misses what the pieces write. -/
theorem tag_mut {w sp D T : BitVec 32} {n tl : Nat} (hT : TagB w sp D n T tl) :
    ∀ r ∈ mutR w sp D n, (⟨State.addr T, tl⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hT.w.sub_right (Region.sub_prefix (by decide))
  · exact hT.w.sub_right (Lay.wSub (by decide))
  · exact hT.stk.symm
  · exact hT.d

end VG.Proof.AesCcm.Arm

end

end

/-! ### `AesCcm.Arm.Mask`, which the modules that import this one used -/

section

/-!
# AES-CCM on ARMv7: masking the data (`mask`)

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of
the data with `0 − ok`, for `ok ∈ {0, 1}` in `r7`: the data is kept if
`ok = 1` and zeroed if `ok = 0` (`mask_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (Keeps z_subFlags gpr_subFlags z_cmp eval_eq' eval_ne' addr_i dec32 z_dec in_of_covers
  bytesAt_succ mem_store gpr_store add32_ofNat_assoc in_left add_ofNat_zero mem_subFlags)

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, addI .r4 .r4 1, .subs .r5 .r5 (imm 1)]

theorem maskStep_ok (s : State) {D : BitVec 32} {i n : Nat} {c : Bool} (h4 : s.gpr .r4 = D + BitVec.ofNat 32 i)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - i)) (h1 : s.gpr .r1 = 0 - (if c then 1 else 0))
    (r : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        ((if c then s.mem (State.addr (D + BitVec.ofNat 32 i)) else 0 : Byte)) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r5 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [h4, h5, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h1,
      mask_byte]
  · simp [gpr_setReg, h4, add32_ofNat_assoc]
  · simp [gpr_setReg, h5]
  · simp [z_setReg, h5]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, Proof.AesCcm.length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {k w sp : BitVec 32} {R q1 : Nat} {s₀ s : State} (he : Env k w sp R q1 s) (hk : Stk w s₀ s)
    {D : BitVec 32} {n : Nat} (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n)
    (hD : Dat k w sp s D n) (hn32 : n < 2 ^ 32) {c : Bool} (h7 : s.gpr .r7 = if c then 1 else 0) :
    WP isa mask s fun s' => Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (State.addr D) (if c then bytesAt s.mem (State.addr D) n else zeros n) := by
  have hn := hD.buf.fit
  obtain ⟨i2, v2⟩ := hk.at 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk.at 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₁, run₁, h4₁, h5₁, h1₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r4 8, .ldrSp .r5 12, .mov .r1 (imm 0),
      .dp .sub .r1 .r1 (.reg .r7), .cmp .r5 (imm 0)] s = some s₁ ∧
      s₁.gpr .r4 = D ∧ s₁.gpr .r5 = BitVec.ofNat 32 n ∧ s₁.gpr .r1 = 0 - (if c then 1 else 0) ∧
      s₁.z = decide (n = 0) ∧ (∀ r, r ≠ .r1 → r ≠ .r4 → r ≠ .r5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [i2, v2, i3, v3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v2, eD]
    · simp [gpr_setReg, v3, en]
    · simp [gpr_setReg, h7, imm]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v3, en, imm]
      rw [z_cmp hn32 (by decide)]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := by simpa using hb
    subst hn0
    refine ⟨he₁, k₁.rd, k₁.wr, fun r hr a b _ => g₁ r ?_ a b, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := by have : n ≠ 0 := by simpa using hb
                         omega_using [this]
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .r4 = D + BitVec.ofNat 32 j ∧
      t.gpr .r5 = BitVec.ofNat 32 (n - j) ∧
      t.mem = writeBytes s.mem (State.addr D) (if c then bytesAt s.mem (State.addr D) j else zeros j) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) ?_
    (n - 0) _
    ⟨0, rfl, hn0, by rw [h4₁, add_ofNat_zero], by rw [h5₁]; rfl,
      by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], fun r _ _ _ => rfl, k₁.rd, k₁.wr, k₁.sp⟩
  rintro m t ⟨j, rfl, hj, r4, r5, mem, g, rd, wr, sp⟩
  have aD := addr_i hn hj
  obtain ⟨t', run', mem', r4', r5', z', g', rd', wr', sp'⟩ := maskStep_ok t (c := c) r4 r5
    (by rw [g _ (by decide) (by decide) (by decide), h1₁])
    (by rw [rd, wr, aD]; exact in_of_covers hD.buf.rd hj (by omega_using [hn32]))
    (by rw [wr, aD]; exact in_of_covers hD.wr hj (by omega_using [hn32]))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨State.addr D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (State.addr D + BitVec.ofNat 64 j) = s.mem (State.addr D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (State.addr D) (show j < 2 ^ 64 by omega_using [hn32, hj])] at hcon; omega_using [eD, en, hn32, h7, hn, v2, v3, h4₁, h5₁, h1₁, hn0, hj, r4, r5, sp, r4', r5', sp', hcon]
  have hmem : t'.mem = writeBytes s.mem (State.addr D)
      (if c then bytesAt s.mem (State.addr D) (j + 1) else zeros (j + 1)) := by
    rw [mem', aD, hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_using [hn32, hj]), length_mask]
  have hz : t'.z = decide (j + 1 = n) := by rw [z', dec32 hj hn32, z_dec hj hn32]
  have gg : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t'.gpr r = s₁.gpr r := fun r a b d => by
    rw [g' r a b d, g r a b d]
  have ev : isa.eval .ne t' = some !decide (j + 1 = n) := eval_ne' hz
  by_cases hjn : j + 1 = n
  · left
    refine ⟨by rw [ev]; simp [hjn], he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact gg _ (by decide) (by decide) (by decide))
      (by rw [sp', sp, ← k₁.sp]) (by rw [rd', rd, k₁.rd]) (by rw [wr', wr, k₁.wr]), by rw [rd', rd],
      by rw [wr', wr], fun r hr a b _ => ?_, by rw [hmem, hjn]⟩
    have hr12 : r ≠ .r12 ∧ r ≠ .r1 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gg r a b hr12.1, g₁ r hr12.2 a b]
  · right
    refine ⟨by rw [ev]; simp [hjn], n - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hj, hjn], r4',
      by rw [r5', dec32 hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

end VG.Proof.AesCcm.Arm

end

end

/-!
# AES-CCM on ARMv7: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. The entry saves our caller's
registers in `W` and keeps `W`, the key schedule and the rounds in
registers (`entry_wp`); `Ctr₀` (`ctrs`) and `mac y` followed by `tag y`
leave the MAC of the payload, encrypted, at `W + y` (`front_wp`); `seal` then
encrypts the data (`ctr`), copies the tag to `tag` (`tagOut_ok`) and restores
the registers (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.Arm (savedR SavedAt restore_ok entry_ok covers_left bytesAt_frame Keeps LoopPre LoopOut
  copyLoop_ok covers_prefix writeBytes_frame' bytesAt_writeBytes_prefix)
open VG.Impl.AesGcm.Arm (copyLoop)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt xorFrom length_xorFrom crypt_eq take_xorFrom_zero mac_eq
  BlockCipher bytesAt_prefix)

/-- What the pieces before the data is written change: `W` but for the
saved registers, and the stack below `sp`. -/
abbrev wR (w sp : BitVec 32) : List Region :=
  [⟨State.addr w, 128⟩, ⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, blw sp]

theorem w_wR {w sp : BitVec 32} {a l : Nat} (h : a + l ≤ 128 ∨ (164 ≤ a ∧ a + l ≤ 2560)) :
    ∃ r' ∈ wR w sp, Region.Sub ⟨State.addr w + BitVec.ofNat 64 a, l⟩ r' := by
  rcases h with h | h
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ h⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 164, 2396⟩, by simp, Offset.sub _ h.1 (by omega_using [h])⟩

theorem wR_mut {w sp D : BitVec 32} {n : Nat} : ∀ r ∈ wR w sp, ∃ r' ∈ mutR w sp D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩

theorem macR_wR {w sp : BitVec 32} {y : Nat} (hy : y = 0 ∨ y = 112) :
    ∀ r ∈ macR w sp y, ∃ r' ∈ wR w sp, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact w_wR (.inl (by omega_using [hy]))
  · exact w_wR (.inl (by decide))
  · exact w_wR (.inr ⟨by decide, by decide⟩)
  · exact ⟨_, by simp, fun _ h => h⟩

/-- A buffer apart from `W` and the stack below `sp` keeps its bytes. -/
theorem buf_wR {w sp : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : Buf w sp s P len) {m m' : Mem}
    (hf : Frame (wR w sp) m m') : bytesAt m' (State.addr P) len = bytesAt m (State.addr P) len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega_using [this])

/-- The entry: our caller's registers saved in `W`, and `W`, the key schedule
and the rounds in `r11`, `r9` and `r8`. -/
theorem entry_wp {s₀ : State} {k w N A D : BitVec 32} {R nl al n tl : Nat} (Ar : Args s₀ k w N A D R nl al n tl)
    (h0 : s₀.gpr .r0 = k) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 R) (eW : stackArg s₀ 6 = w) :
    WP isa (.block entry) s₀ fun s₁ => Env k w s₀.sp R (s₁.gpr .r10).toNat s₁ ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r11 → r ≠ .r12 → s₁.gpr r = s₀.gpr r) ∧
      s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ SavedAt s₁.mem w s₀ ∧ Frame [savedR w] s₀.mem s₁.mem := by
  obtain ⟨i4, v4⟩ := Ar.stk.at 6 (by decide) (show 4 * 6 = 24 from rfl)
  rw [eW] at v4
  refine entry_ok (off := 24) (by decide) i4 (by rw [v4]; exact Ar.lay.ww) (by rw [v4]; exact Ar.perm.w)
    fun s' g12 g rd wr sp sv fr => ?_
  rw [v4] at g12 sv fr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine ⟨⟨by simp [gpr_setReg, g .r1 (by decide), h1], by simp [gpr_setReg, g .r0 (by decide), h0],
    by simp [gpr_setReg], by simp [gpr_setReg, g12], sp, Perm.of_eq Ar.perm rd wr⟩, ?_, rd, wr, sv, fr⟩
  intro r a b c d; simp [gpr_setReg, a, b, c, g r d]

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T`, the
stack argument at `sp + 16`. -/
theorem tagOut_ok {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp) {s : State} (he : Env k w sp R q1 s)
    {T : BitVec 32} {tl : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16)
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 16)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 16)) 32 = T)
    (hli : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 20)) 4)
    (hlv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 20)) 32 = BitVec.ofNat 32 tl)
    (hTw : Covers [⟨State.addr T, tl⟩] s.wr) (hTf : T.toNat + tl ≤ 2 ^ 32)
    (hTW : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w, 2560⟩) :
    WP isa tagOut s fun s' => Env k w sp R q1 s' ∧
      s'.mem = writeBytes s.mem (State.addr T) (bytesAt s.mem (State.addr w) tl) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, h1₁, h2₁, h3₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.mov .r1 (.reg .r11), .ldrSp .r2 16, .ldrSp .r3 20]
      s = some s₁ ∧ s₁.gpr .r1 = w ∧ s₁.gpr .r2 = T ∧ s₁.gpr .r3 = BitVec.ofNat 32 tl ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [hTi, hTv, hli, hlv], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he.r11]
    · simp [gpr_setReg, hTv]
    · simp [gpr_setReg, hlv]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have ww := L.ww
  obtain lp : LoopPre s₁ w T tl :=
    ⟨h1₁, h2₁, h3₁, by omega_using [ht4], by omega_using [ht16], by omega_using [ht16, ww], hTf, covers_left (covers_prefix he₁.perm.w (by omega_using [ht16])),
      by rw [k₁.wr]; exact hTw, (hTW.sub_right (Region.sub_prefix (by omega_using [ht16]))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s₂ ⟨hm₂, lo⟩ => ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
        (by decide)) lo.sp lo.rd lo.wr, by rw [hm₂, k₁.mem], by rw [lo.rd, k₁.rd], by rw [lo.wr, k₁.wr]⟩

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' {s₀ : State} {k w N A D T : BitVec 32} {R nl al n tl : Nat} (Ar : Args s₀ k w N A D R nl al n tl)
    (Tb : TagB w s₀.sp D n T tl) (hTw : Covers [⟨State.addr T, tl⟩] s₀.wr)
    (h0 : s₀.gpr .r0 = k) (h1 : s₀.gpr .r1 = BitVec.ofNat 32 R) (h2 : s₀.gpr .r2 = N)
    (h3 : s₀.gpr .r3 = BitVec.ofNat 32 nl) (eA : stackArg s₀ 0 = A) (eal : stackArg s₀ 1 = BitVec.ofNat 32 al)
    (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n) (eT : stackArg s₀ 4 = T)
    (etl : stackArg s₀ 5 = BitVec.ofNat 32 tl) (eW : stackArg s₀ 6 = w) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s₀.mem (State.addr k) R) tl (bytesAt s₀.mem (State.addr N) nl)
        (bytesAt s₀.mem (State.addr D) n) (bytesAt s₀.mem (State.addr A) al) =
        (bytesAt s'.mem (State.addr D) n, bytesAt s'.mem (State.addr T) tl) := by
  have L := Ar.lay
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  obtain hsavedK : (⟨State.addr k, 240⟩ : Region).Disjoint (savedR w) := L.k_w' (by decide)
  refine WP.seq (WP.mono (entry_wp Ar h0 h1 eW) fun s₁ ⟨he₁, g₁, rd₁, wr₁, sv₁, f₁⟩ => ?_)
  obtain hent : ∀ {P : BitVec 32} {len : Nat}, Buf w s₀.sp s₀ P len →
      bytesAt s₁.mem (State.addr P) len = bytesAt s₀.mem (State.addr P) len := fun hP =>
    bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega_using [this])
  obtain hK₁ : Spec.Ccm.ctxCiph s₁.mem (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R :=
    ctxCiph_frame f₁ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsavedK) hRb
  obtain hk₁ : Stk w s₀ s₁ := Ar.stk.frame f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Ar.stk.aw.sub_right (Lay.wSub (by decide)))
    he₁.sp rd₁ wr₁
  -- `Ctr₀`.
  obtain hN₁ := Ar.nonce.of_eq rd₁ wr₁
  refine WP.seq (WP.mono (ctrs_ok L he₁ hN₁ (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h2])
    (by rw [g₁ _ (by decide) (by decide) (by decide) (by decide), h3]) Ar.h7 Ar.h13)
    fun s₂ ⟨c₂, h10₂, f₂, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [hent Ar.nonce] at c₂
  obtain he₂ : Env k w s₀.sp R (14 - nl) s₂ :=
    ⟨by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r8],
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r9], h10₂,
      by rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), he₁.r11],
      by rw [sp₂, he₁.sp], he₁.perm.of_eq rd₂ wr₂⟩
  obtain f₂' : Frame (wR w s₀.sp) s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact w_wR (.inl (by decide))
  obtain hk₂ := hk₁.frame (f₂'.sub (wR_mut (D := D) (n := n))) (args_mut Ar) sp₂ rd₂ wr₂
  obtain rd₁₂ : s₂.rd = s₀.rd := rd₂.trans rd₁
  obtain wr₁₂ : s₂.wr = s₀.wr := wr₂.trans wr₁
  obtain hnl := length_bytesAt s₀.mem (State.addr N) nl
  obtain h7 : 7 ≤ (bytesAt s₀.mem (State.addr N) nl).length := by rw [hnl]; exact Ar.h7
  obtain h13 : (bytesAt s₀.mem (State.addr N) nl).length ≤ 13 := by rw [hnl]; exact Ar.h13
  -- The MAC.
  refine WP.seq (WP.mono (mac_ok L he₂ hk₂ rfl Ar.rounds eA eal eD en etl hnl Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te
    Ar.al32 Ar.n32 Ar.hn c₂ (y := 0) (.inl rfl) (Ar.aad.of_eq rd₁₂ wr₁₂) (Ar.data.buf.of_eq rd₁₂ wr₁₂))
    fun s₃ M => ?_)
  obtain c₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame M.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c₂]
  -- The encrypted MAC at `W`.
  refine WP.seq (WP.mono (tag_ok L M.env Ar.rounds h7 h13 c₃ (y := 0) (.inl rfl))
    fun s₄ ⟨he₄, rd₄, wr₄, _, f₄, o₄⟩ => ?_)
  obtain f₄' : Frame (wR w s₀.sp) s₃.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact w_wR (.inl (by decide))
    · exact w_wR (.inl (by decide))
    · exact w_wR (.inr ⟨by decide, by decide⟩)
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain G₄ : Frame (wR w s₀.sp) s₁.mem s₄.mem := (f₂'.trans (M.frame.sub (macR_wR (.inl rfl)))).trans f₄'
  obtain F₄ : Frame (mutR w s₀.sp D n) s₁.mem s₄.mem := G₄.sub wR_mut
  obtain rd₄' : s₄.rd = s₀.rd := by rw [rd₄, M.rd, rd₁₂]
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, M.wr, wr₁₂]
  obtain c₄ : bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 48) 16 =
      Spec.Ccm.ctrBlock (bytesAt s₀.mem (State.addr N) nl) 0 := by
    rw [bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm) (by decide), c₃]
  obtain hk₄ := hk₁.frame F₄ (args_mut Ar) (by rw [he₄.sp, he₁.sp]) (by rw [rd₄', rd₁]) (by rw [wr₄', wr₁])
  -- Counter mode.
  refine WP.seq (WP.mono (ctr_ok L he₄ hk₄ Ar.rounds h7 h13 c₄ eD en (Ar.data.of_eq rd₄' wr₄')
    (by rw [hnl]; exact Ar.hn) Ar.n32) fun s₅ ⟨he₅, rd₅, wr₅, _, f₅, o₅⟩ => ?_)
  obtain F₅ : Frame (mutR w s₀.sp D n) s₁.mem s₅.mem := F₄.trans (f₅.sub ctrR_mut)
  -- The tag copied to `T`.
  obtain hk₅ := hk₁.frame F₅ (args_mut Ar) (by rw [he₅.sp, he₁.sp]) (by rw [rd₅, rd₄', rd₁])
    (by rw [wr₅, wr₄', wr₁])
  obtain ⟨i4, v4⟩ := hk₅.at 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨i5, v5⟩ := hk₅.at 5 (by decide) (show 4 * 5 = 20 from rfl)
  rw [eT] at v4
  rw [etl] at v5
  refine WP.seq (WP.mono (tagOut_ok L he₅ Ar.t4 Ar.t16 i4 v4 i5 v5 (by rw [wr₅, wr₄']; exact hTw) Tb.wrap Tb.w)
    fun s₆ ⟨he₆, hm₆, rd₆, wr₆⟩ => ?_)
  obtain hx : (bytesAt s₅.mem (State.addr w) tl).length = tl := length_bytesAt _ _ _
  obtain f₆ : Frame [⟨State.addr T, tl⟩] s₅.mem s₆.mem := by rw [hm₆]; exact writeBytes_frame' _ hx
  -- `restore`.
  refine WP.mono (restore_ok he₆.r11 L.ww (covers_left he₆.perm.w)
    ((sv₁.frame F₅ (saved_mut Ar)).frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (Tb.w.sub_right (Lay.wSub (by decide))).symm) he₆.sp)
    fun s' ⟨ab, hm, _, _, _⟩ => ⟨ab, ?_⟩
  obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m (State.addr k) R) := fun _ x =>
    Proof.Cmac.aesWith_length _ _ x
  obtain cK : ∀ {m : Mem}, Frame (mutR w s₀.sp D n) s₁.mem m →
      Spec.Ccm.ctxCiph m (State.addr k) R = Spec.Ccm.ctxCiph s₀.mem (State.addr k) R := fun hf => by
    rw [ctxCiph_frame hf (k_mut Ar) hRb, hK₁]
  obtain a₂ : bytesAt s₂.mem (State.addr A) al = bytesAt s₀.mem (State.addr A) al := by
    rw [buf_wR Ar.aad f₂', hent Ar.aad]
  obtain d₂ : bytesAt s₂.mem (State.addr D) n = bytesAt s₀.mem (State.addr D) n := by
    rw [buf_wR Ar.data.buf f₂', hent Ar.data.buf]
  obtain d₄ : bytesAt s₄.mem (State.addr D) n = bytesAt s₀.mem (State.addr D) n := by
    rw [buf_wR Ar.data.buf G₄, hent Ar.data.buf]
  obtain w₅ : bytesAt s₅.mem (State.addr w) 16 = bytesAt s₄.mem (State.addr w) 16 :=
    bytesAt_frame f₅ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simpa using L.w_w (a := 0) (n := 16) (d := 64) (m := 32) (.inl (by decide)) (by decide) (by decide)
      · simpa using L.w_w (a := 0) (n := 16) (d := 384) (m := 2176) (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
      · exact (Ar.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm) (by decide)
  have mo := M.out
  rw [BitVec.add_zero] at o₄ mo
  obtain hY := congrArg List.length o₄
  rw [length_bytesAt, length_xorFrom] at hY
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  obtain d₆ : bytesAt s₆.mem (State.addr D) n = bytesAt s₅.mem (State.addr D) n :=
    bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Tb.d.symm) (by have := Ar.n32; omega_using [this])
  obtain t₆ : bytesAt s₆.mem (State.addr T) tl = bytesAt s₅.mem (State.addr w) tl := by
    rw [hm₆, bytesAt_writeBytes_prefix _ _ _ (by rw [hx]) (by have := Ar.t16; omega_using [this]), hx, Nat.sub_self]
    simp [Spec.Aes.bytesAt]
  refine ⟨?_, ?_⟩
  · rw [hm, d₆, o₅, cK F₄, d₄, crypt_eq (hBC _)]
  · rw [hm, t₆, bytesAt_prefix s₅.mem (State.addr w) Ar.t16, w₅, o₄, take_xorFrom_zero (hBC _) _ hY.symm Ar.t16,
      mo, cK (f₂'.sub wR_mut), cK ((f₂'.sub wR_mut).trans (M.frame.sub (macR_mut (.inl rfl)))), a₂, d₂,
      ← mac_eq _ _ (by rw [hnl]; have := Ar.h13; omega_using [this])]

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp {s : State} (h : sealArm.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealArm.post s s' :=
  have A := args_of_seal h
  seal_wp' A.1.1 A.1.2 A.2.1 rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl
    (ofNat_toNat32 _).symm rfl (ofNat_toNat32 _).symm rfl

end VG.Proof.AesCcm.Arm
