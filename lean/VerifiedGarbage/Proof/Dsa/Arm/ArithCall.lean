module

public import VerifiedGarbage.Impl.Dsa.Arm.Arith
public import VerifiedGarbage.Proof.Dsa.Arm.Pow
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.Arm.Stream
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Dsa.StreamBytes
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Dsa.Arm.Checks
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Add
public import VerifiedGarbage.Proof.Ecdsa.Arm.Flags
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Mont.Arm.Step
public import VerifiedGarbage.Proof.Framework.Arm.Call

/-! ### `Dsa.Arm.PowCall`, which this module and modules that import it used -/

section

/-!
# DSA's exponentiation as a function on 32-bit ARM: its calls

A call (`Impl.Dsa.Arm.Pow.call`) of `vg_dsa_pow_{n}_{e}` from code whose
working space is at `r12`: it passes the context's bytes as the function's
working space, which its contract (`powK`) narrows the call to, and takes
`r12` back from `r11` (`call_ok`). Two runs of a call from the same working
space leak the same trace (`call_trace`), by the function's own constant
time (`powK_ct`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw op2_reg)

theorem body_noFrames (n e : Nat) : (body n e).noFrames = true := by
  simp only [body, Impl.Dsa.Arm.Context.call, Impl.Dsa.Arm.Context.body, contextSetup, exponentiate, exponentStep, exponentBody, exponentProduct, Dynamic.mul, rowD,
    digitRowD, mulRowD, csubD, Dynamic.zeros, ptrLoop, one, powerTwo, addD, addDigits, selectW, Code.noFrames,
    Bool.and_self]

/-- The arguments of a call, `r11` keeping `r12`. -/
theorem head_ok {s : State} (n : Nat) :
    WP isa (.block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 (BitVec.ofNat 16 (contextBytes n / 8))])
      s fun u => u.gpr .r11 = s.gpr .r12 ∧ u.gpr .r0 = s.gpr .r12 ∧
        u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32 ∧ Rest [.r0, .r1, .r11] s u ∧
        u.mem = s.mem :=
  wp_mov (op2_reg s .r12) fun u₁ v₁ => wp_mov (op2_reg u₁ .r12) fun u₂ v₂ => wp_movw fun u v₃ =>
    WP.block_nil ⟨by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr],
      by rw [v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide)], v₃.gpr,
      ((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans (v₃.rest (by decide)),
      by rw [v₃.mem, v₂.mem, v₁.mem]⟩

/-- On entry to the function, its precondition, narrowed to the context. -/
theorem entry_pre {s u : State} {base : Addr} {size n e : Nat} (hs : Ws s base size) (hz : contextBytes n ≤ size)
    (hn48 : n ≤ 48) (h0 : u.gpr .r0 = s.gpr .r12) (h1 : u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32)
    (hm : u.mem = s.mem) (hodd : val32 s.mem base (slot n 0) (2 * n) % 2 = 1)
    (hm1 : 1 < val32 s.mem base (slot n 0) (2 * n)) :
    (powK n e).pre (u.callEntry.withRegions [] [⟨base, contextBytes n⟩]) := by
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by
    rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have l1 : (u.callEntry.gpr .r1).toNat * 8 = contextBytes n := by
    rw [State.callEntry_gpr _ (by decide), h1]; exact words_eq hn48
  simp only [powK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, b0, l1, hm]
  refine ⟨trivial, trivial, ?_, Nat.le_refl _, hodd, hm1⟩
  rw [State.callEntry_gpr _ (by decide), h0, hs.wb_toNat]
  have := hs.nowrap
  omega_using [hz, this]

/-- A call: `b ^ x mod m` into slot 9, as `body_ok`, with `r12` kept and
the registers the calling convention keeps. -/
theorem call_ok {s : State} {base : Addr} {size n e m : Nat} (hs : Ws s base size) (hz : contextBytes n ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Impl.Dsa.Arm.Pow.call n e) s fun t => Ws t base size ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) e % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r11, .lr] s t := by
  unfold Impl.Dsa.Arm.Pow.call
  refine WP.seq (WP.mono (head_ok n) fun u ⟨h11, h0, h1, R₁, M₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.callCalls (k := powK n e) (powK_correct hn hn48 he hen)
    (entry_pre hs hz hn48 h0 h1 M₁ (by rw [hv]; exact hodd) (by rw [hv]; exact hm1))
    (Covers.right (covers_ctx w₁ hz)) (covers_ctx w₁ hz) (fun v hrd hwr hsp _ P _ post => ?_) (body_noFrames n e))
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  simp only [powK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, b0, M₁, hv] at post
  obtain ⟨V, O⟩ := post
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h11]
  refine wp_mov (op2_reg v .r11) fun t v₂ => WP.block_nil ⟨⟨?_, ?_, hs.nowrap⟩, ?_, ?_, ?_⟩
  · rw [v₂.gpr, v11, hs.wb]
  · rw [v₂.wr, hwr]; exact w₁.wr
  · rw [v₂.mem]; exact V
  · rw [v₂.mem]; exact O
  · refine ⟨fun r hr => ?_, by rw [v₂.rd, hrd, R₁.rd], by rw [v₂.wr, hwr, R₁.wr], by rw [v₂.sp, hsp, R₁.sp]⟩
    by_cases h12 : r = .r12
    · subst h12; rw [v₂.gpr, v11]
    · rw [v₂.other _ h12]
      have hp : r ∈ preserved ∧ r ≠ .lr ∧ r ∉ [.r0, .r1, .r11] := by revert hr h12; cases r <;> decide
      rw [P _ hp.1 hp.2.1, R₁.gpr _ hp.2.2]

/-- Two calls from the same working space leak the same trace. -/
theorem call_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n e : Nat} (hs₁ : Ws s₁ base size₁)
    (hs₂ : Ws s₂ base size₂) (hz₁ : contextBytes n ≤ size₁) (hz₂ : contextBytes n ≤ size₂)
    (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (ho₁ : val32 s₁.mem base (slot n 0) (2 * n) % 2 = 1) (hm₁ : 1 < val32 s₁.mem base (slot n 0) (2 * n))
    (ho₂ : val32 s₂.mem base (slot n 0) (2 * n) % 2 = 1) (hm₂ : 1 < val32 s₂.mem base (slot n 0) (2 * n)) :
    SameTrace isa (Impl.Dsa.Arm.Pow.call n e) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs []) a b :=
    fun _ _ => VG.Arm.Taint.agree_ofRegs fun _ h => nomatch h
  unfold Impl.Dsa.Arm.Pow.call
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := VG.Arm.Taint.ofRegs [])
      (σ := VG.Arm.Taint.ofRegs []) (c₀ := .block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _)) (head_ok n) (head_ok n)
    fun u₁ u₂ ⟨_, h0₁, h1₁, R₁, M₁⟩ ⟨_, h0₂, h1₂, R₂, M₂⟩ => ?_
  have w₁ := hs₁.of_rest R₁ (by decide)
  have w₂ := hs₂.of_rest R₂ (by decide)
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (powK_correct hn hn48 he hen) (powK_ct n e hn hn48) [] [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := VG.Arm.Taint.ofRegs []) (σ := VG.Arm.Taint.ofRegs []) (h := .block [])
      (by decide)).mono (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨entry_pre hs₁ hz₁ hn48 h0₁ h1₁ M₁ ho₁ hm₁, entry_pre hs₂ hz₂ hn48 h0₂ h1₂ M₂ ho₂ hm₂, ?_,
    Covers.right (covers_ctx w₁ hz₁), covers_ctx w₁ hz₁, Covers.right (covers_ctx w₂ hz₂), covers_ctx w₂ hz₂⟩
  simp only [powK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h0₁, h0₂]
  exact BitVec.eq_of_toNat_eq (by rw [hs₁.wb_toNat, hs₂.wb_toNat])

end VG.Proof.Dsa.Arm.Pow

end

end

/-! ### `Dsa.Arm.Stream`, which this module and modules that import it used -/

section

/-! ### `Dsa.Arm.Checks`, which this module and modules that import it used -/

section

/-!
# DSA on 32-bit ARM: the masks of the checks

Each check leaves a mask in `r2`, all ones or zero (`mask32`): `nonzero k a`
of `[a] ≠ 0` (`nonzero_ok`), `lessThan k a b` of `[a] < [b]`
(`lessThan_ok`: the carry of `[a] - [b]` a 16-bit digit at a time, as in
`chain_next`), `equal k a b` of `[a] = [b]`; `subWords k o a b` writes
`[a] - [b]` modulo `2^(32k)` (`subWords_ok`), `setConst k o x` the constant
`x` (`setConst_ok`), and `andFlag` ands `r2` into a flag word.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and negOr_shr neg_bit32 w32_eq_zero_iff)
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg op2_lsr op2_lsl
  dpVal toNat_shr)

/-! ## Arithmetic of the borrow chain -/

/-- A word of `[a] - [b]` from its two digits: `w + 2³² c' + b + 1 = a + 2³² + c`. -/
theorem borrow_word {a0 a1 b0 b1 c x0 x1 : Nat} (ha0 : a0 < 2 ^ 16) (ha1 : a1 < 2 ^ 16) (hb0 : b0 < 2 ^ 16)
    (hb1 : b1 < 2 ^ 16) (hc : c ≤ 1) (h0 : x0 = a0 + (2 ^ 16 - 1 - b0) + c)
    (h1 : x1 = a1 + (2 ^ 16 - 1 - b1) + x0 / 2 ^ 16) :
    x0 % 2 ^ 16 + x1 % 2 ^ 16 * 2 ^ 16 + 2 ^ 32 * (x1 / 2 ^ 16) + (b0 + b1 * 2 ^ 16) + 1 =
      a0 + a1 * 2 ^ 16 + 2 ^ 32 + c ∧ x1 / 2 ^ 16 ≤ 1 := by
  subst h0 h1; omega_arith

/-- The chain a word on: `T + P c + B = A + P` for the low part `T < P`. -/
theorem chain_next {P T c B A w c' wb wa : Nat} (hT : T < P) (hw32 : w < 2 ^ 32) (h : T + P * c + B = A + P)
    (hw : w + 2 ^ 32 * c' + wb + 1 = wa + 2 ^ 32 + c) :
    T + P * w < 2 ^ 32 * P ∧ T + P * w + 2 ^ 32 * P * c' + (B + P * wb) = A + P * wa + 2 ^ 32 * P := by
  constructor
  · have := Nat.mul_le_mul_left P (show w + 1 ≤ 2 ^ 32 by omega_arith)
    rw [Nat.mul_add, Nat.mul_one] at this
    rw [Nat.mul_comm (2 ^ 32)]; omega_arith
  · have := congrArg (P * ·) hw
    simp only [Nat.mul_add, Nat.mul_one] at this
    grind

/-- The chain's carry is whether `A ≥ B`. -/
theorem chain_carry {P T c A B : Nat} (hT : T < P) (hc : c ≤ 1)
    (h : T + P * c + B = A + P) : c = if A < B then 0 else 1 := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega_arith
  · rw [Nat.mul_zero] at h; rw [ite_eq_left (by omega_arith)]
  · rw [Nat.mul_one] at h; rw [ite_eq_right (by omega_arith)]

/-- The chain's low part is `A - B` modulo `P`. -/
theorem chain_low {P T c A B : Nat} (hT : T < P) (hc : c ≤ 1) (h : T + P * c + B = A + P) :
    T = (A + P - B) % P := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega_arith
  · rw [Nat.mul_zero] at h; rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [Nat.mul_one] at h
    rw [show A + P - B = (A - B) + P by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

/-! ## A digit of the difference -/

/-- Digit `h` of `[a] - [b]`: `r4 = a_h + (2¹⁶ - 1 - b_h) + c` for the words in
`r7` and `r5`, its carry to `r3`. -/
theorem borrowDigit_ok {s : State} {h : Nat} (hh : h < 2) (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16)
    (hc : (s.gpr .r3).toNat ≤ 1) {is : List Instr} {Q : State → Prop}
    (k : ∀ u, (u.gpr .r4).toNat = hdig (s.gpr .r7).toNat h + (2 ^ 16 - 1 - hdig (s.gpr .r5).toNat h) +
        (s.gpr .r3).toNat → (u.gpr .r3).toNat = (u.gpr .r4).toNat / 2 ^ 16 → Rest [.r0, .r3, .r4] s u →
      u.mem = s.mem → WP isa (.block is) u Q) :
    WP isa (.block (borrowDigit h ++ is)) s Q := by
  obtain ha := hdig_lt (s.gpr .r7).toNat h
  obtain hb := hdig_lt (s.gpr .r5).toNat h
  simp only [borrowDigit, List.cons_append, List.nil_append]
  refine wp_half hh h6 fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  refine wp_half hh (by simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h6) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  obtain v5 : (s₅.gpr .r4).toNat = hdig (s.gpr .r7).toNat h + (2 ^ 16 - 1 - hdig (s.gpr .r5).toNat h) +
      (s.gpr .r3).toNat := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal, h6]
    refine (toNat_add_eq (toNat_sub_eq (toNat_add_eq (toNat_ofNat_dig _ _) toNat_mask16 ?_)
      (toNat_ofNat_dig _ _) ?_) rfl ?_).trans ?_ <;> omega_arith
  refine k s₆ (by rw [u₆.other .r4 (by decide), v5]) (by rw [u₆.gpr, toNat_shr, u₆.other .r4 (by decide)]) ?_
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  exact (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))).trans
    ((u₅.rest (by simp)).trans (u₆.rest (by simp)))

/-! ## Comparisons -/

/-- The registers the comparisons write: all of `dclob` but `r8`. -/
def ltClob : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10]

/-- The borrow chain's invariant after `j` words: `T + 2^(32j) c + B = A + 2^(32j)`. -/
abbrev Chain (m : Mem) (base : Addr) (a b j c : Nat) : Prop :=
  ∃ T, T < 2 ^ (32 * j) ∧ T + 2 ^ (32 * j) * c + val32 m base b j = val32 m base a j + 2 ^ (32 * j)

/-- Two digits of the borrow chain, from the words in `r7` and `r5`. -/
theorem borrowWord {u u₃ u₄ : State} {wa wb : Nat} (r7 : (u.gpr .r7).toNat = wa) (r5 : (u.gpr .r5).toNat = wb)
    (C : (u.gpr .r3).toNat ≤ 1)
    (X₃ : (u₃.gpr .r4).toNat = hdig (u.gpr .r7).toNat 0 + (2 ^ 16 - 1 - hdig (u.gpr .r5).toNat 0) + (u.gpr .r3).toNat)
    (C₃ : (u₃.gpr .r3).toNat = (u₃.gpr .r4).toNat / 2 ^ 16)
    (X₄ : (u₄.gpr .r4).toNat = hdig wa 1 + (2 ^ 16 - 1 - hdig wb 1) + (u₃.gpr .r3).toNat)
    (C₄ : (u₄.gpr .r3).toNat = (u₄.gpr .r4).toNat / 2 ^ 16) (hwa : wa < 2 ^ 32) (hwb : wb < 2 ^ 32) :
    (u₃.gpr .r4).toNat % 2 ^ 16 + (u₄.gpr .r4).toNat % 2 ^ 16 * 2 ^ 16 + 2 ^ 32 * (u₄.gpr .r3).toNat + wb + 1 =
      wa + 2 ^ 32 + (u.gpr .r3).toNat ∧ (u₄.gpr .r3).toNat ≤ 1 := by
  rw [r7, r5] at X₃
  obtain ea := word_digits wa hwa
  obtain eb := word_digits wb hwb
  obtain ⟨h, h'⟩ := borrow_word (hdig_lt wa 0) (hdig_lt wa 1) (hdig_lt wb 0) (hdig_lt wb 1) C X₃ (C₃ ▸ X₄)
  rw [C₄]
  exact ⟨by rw [ea, eb]; omega_arith, h'⟩

theorem lessThan_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a b : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (hb : b + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) (h16b : b < 2 ^ 16) :
    WP isa (lessThan k a b) s fun t =>
      t.gpr .r2 = mask32 (val32 s.mem base a k < val32 s.mem base b k) ∧ Rest ltClob s t ∧ t.mem = s.mem := by
  have hn := hs.nowrap
  unfold lessThan
  refine WP.seq (wp_movw fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r1) (by decide) (by omega_arith) fun s₄ u₄ =>
    wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₅ => WP.block_nil ?_)
  obtain R : Rest ltClob s t := ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
    (u₄.rest (by decide))).trans (u₅.rest (by decide))
  obtain mt : t.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain r6 : t.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain r3 : t.gpr .r3 = 1 := by simp only [u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]
  obtain p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 a := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 b := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) := by
    simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  clear u₁ u₂ u₃ u₄ u₅
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 a) (step := 4) (k := k)
    (fun j u => Rest ltClob s u ∧ u.mem = s.mem ∧ u.gpr .r6 = VG.Proof.X25519.Arm.mask16 ∧
      u.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 b + BitVec.ofNat 32 (4 * j) ∧ (u.gpr .r3).toNat ≤ 1 ∧
      Chain s.mem base a b j (u.gpr .r3).toNat)
    (by decide) hk (by omega_arith) (fun j u u' ⟨c1, c2, c3, c4, c5, c6⟩ F => ⟨c1.trans (F.rest _),
      by rw [F.mem]; exact c2, by rw [F.gpr]; exact c3, by rw [F.gpr]; exact c4, by rw [F.gpr]; exact c5,
      by rw [F.gpr]; exact c6⟩)
    ⟨R, mt, r6, by rw [p1]; exact (BitVec.add_zero _).symm, by rw [r3]; decide, 0, by decide,
      by simp only [r3, val32]; rfl⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨Ru, Mu, _, _, Cu, T, hT, V⟩ _ => ?_)
  · intro j hj u ⟨Ru, Mu, r6u, p1u, Cu, T, hT, V⟩ pu p9u
    obtain wu := hs.of_rest Ru (by decide)
    obtain e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    refine wp_ldr (by decide) (wu.ea (K := a + 4 * j) (at_ptr pu e12) (by omega_arith))
      (wu.read (d := a + 4 * j + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
    obtain w₁ := wu.of_upd v₁ (by decide)
    refine wp_ldr (by decide) (w₁.ea (K := b + 4 * j) (at_ptr (by rw [v₁.other .r1 (by decide)]; exact p1u)
      (by rw [v₁.other .r12 (by decide)]; exact e12)) (by omega_arith))
      (w₁.read (d := b + 4 * j + 0) (n := 4) (by omega_arith)) fun u₂ v₂ => ?_
    obtain r7v : (u₂.gpr .r7).toNat = w32 s.mem base (a + 4 * j) := by
      rw [v₂.other .r7 (by decide), v₁.gpr, Mu, Nat.add_zero]
    obtain r5v : (u₂.gpr .r5).toNat = w32 s.mem base (b + 4 * j) := by rw [v₂.gpr, v₁.mem, Mu, Nat.add_zero]
    obtain c₂ : u₂.gpr .r3 = u.gpr .r3 := by rw [v₂.other .r3 (by decide), v₁.other .r3 (by decide)]
    obtain r6₂ : u₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
      rw [v₂.other .r6 (by decide), v₁.other .r6 (by decide)]; exact r6u
    refine borrowDigit_ok (h := 0) (by decide) r6₂ (by rw [c₂]; exact Cu) fun u₃ X₃ C₃ R₃ M₃ => ?_
    obtain r6₃ : u₃.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [R₃.gpr _ (by decide)]; exact r6₂
    obtain b₃ : (u₃.gpr .r3).toNat ≤ 1 := by
      have := hdig_lt (u₂.gpr .r7).toNat 0
      rw [C₃, X₃, c₂]; omega_arith
    refine borrowDigit_ok (h := 1) (by decide) r6₃ b₃ fun u₄ X₄ C₄ R₄ M₄ => ?_
    refine wp_bump (by decide) fun u₅ v₅ => wp_bump (by decide) fun u₆ v₆ => WP.block_nil ?_
    rw [R₃.gpr .r7 (by decide), R₃.gpr .r5 (by decide), r7v, r5v] at X₄
    rw [c₂] at X₃
    obtain ⟨hw, hc'⟩ := borrowWord (u := u₂) r7v r5v (by rw [c₂]; exact Cu) (by rw [c₂]; exact X₃) C₃ X₄ C₄
      (BitVec.isLt _) (BitVec.isLt _)
    rw [c₂] at hw
    obtain ⟨hlt, heq⟩ := chain_next hT (by omega_arith) V hw
    obtain c₆ : u₆.gpr .r3 = u₄.gpr .r3 := by rw [v₆.other .r3 (by decide), v₅.other .r3 (by decide)]
    refine ⟨⟨((Ru.trans (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
      ((R₃.mono (by decide)).trans (R₄.mono (by decide))))).trans (v₅.rest (by decide))).trans (v₆.rest (by decide)),
      by rw [v₆.mem, v₅.mem, M₄, M₃, v₂.mem, v₁.mem, Mu],
      by rw [v₆.other .r6 (by decide), v₅.other .r6 (by decide), R₄.gpr .r6 (by decide)]; exact r6₃,
      by rw [v₆.gpr, v₅.other .r1 (by decide), R₄.gpr .r1 (by decide), R₃.gpr .r1 (by decide),
        v₂.other .r1 (by decide), v₁.other .r1 (by decide)]; exact ptr_step p1u,
      by rw [c₆]; exact hc', _, by rw [pow32_succ]; exact hlt, ?_⟩,
      by rw [v₆.other .r10 (by decide), v₅.gpr, R₄.gpr .r10 (by decide), R₃.gpr .r10 (by decide),
        v₂.other .r10 (by decide), v₁.other .r10 (by decide)]; exact ptr_step pu,
      by rw [v₆.other .r9 (by decide), v₅.other .r9 (by decide), R₄.gpr .r9 (by decide), R₃.gpr .r9 (by decide),
        v₂.other .r9 (by decide), v₁.other .r9 (by decide)]; exact p9u⟩
    rw [c₆, pow32_succ, val32_succ, val32_succ]
    exact heq
  · refine wp_dp (op2_imm (by decide)) fun t v => WP.block_nil ⟨?_, Ru.trans (v.rest (by decide)), by rw [v.mem, Mu]⟩
    obtain hc := chain_carry hT Cu V
    obtain e3 : u.gpr .r3 = if val32 s.mem base a k < val32 s.mem base b k then 0 else 1 := by
      apply BitVec.eq_of_toNat_eq; rw [hc]; split <;> rfl
    rw [v.gpr, dpVal, e3]
    by_cases h : val32 s.mem base a k < val32 s.mem base b k <;> simp only [h, ↓reduceIte, mask32] <;> decide

/-- `[o] = [a] - [b]` modulo `2^(32k)`. -/
theorem subWords_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k o a b : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (hb : b + 4 * k ≤ size) (ho : o + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16)
    (h16b : b < 2 ^ 16) (h16o : o < 2 ^ 16) (hsa : o + 4 * k ≤ a ∨ a + 4 * k ≤ o)
    (hsb : o + 4 * k ≤ b ∨ b + 4 * k ≤ o) :
    WP isa (subWords k o a b) s fun t =>
      val32 t.mem base o k = (val32 s.mem base a k + 2 ^ (32 * k) - val32 s.mem base b k) % 2 ^ (32 * k) ∧
      Rest dclob s t ∧ Outside base o (4 * k) s.mem t.mem := by
  have hn := hs.nowrap
  unfold subWords
  refine WP.seq (wp_movw fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₃ u₃ => wp_ptr (d := .r1) (by decide) (by omega_arith) fun s₄ u₄ =>
    wp_ptr (d := .r8) (by decide) (by omega_arith) fun s₅ u₅ =>
    wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₆ => WP.block_nil ?_)
  obtain R : Rest dclob s t := (((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
    (u₄.rest (by decide))).trans (u₅.rest (by decide))).trans (u₆.rest (by decide))
  obtain mt : t.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain r6 : t.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain r3 : t.gpr .r3 = 1 := by simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, reduceCtorEq, ↓reduceIte]
  obtain p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 a := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p1 : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 b := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p8 : t.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 o := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) := by
    simp only [u₆.get, u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  clear u₁ u₂ u₃ u₄ u₅ u₆
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 a) (step := 4) (k := k)
    (fun j u => Rest dclob s u ∧ Outside base o (4 * k) s.mem u.mem ∧ u.gpr .r6 = VG.Proof.X25519.Arm.mask16 ∧
      u.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 b + BitVec.ofNat 32 (4 * j) ∧
      u.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 o + BitVec.ofNat 32 (4 * j) ∧ (u.gpr .r3).toNat ≤ 1 ∧
      val32 u.mem base o j + 2 ^ (32 * j) * (u.gpr .r3).toNat + val32 s.mem base b j =
        val32 s.mem base a j + 2 ^ (32 * j))
    (by decide) hk (by omega_arith) (fun j u u' ⟨c1, c2, c3, c4, c5, c6, c7⟩ F => ⟨c1.trans (F.rest _),
      by rw [F.mem]; exact c2, by rw [F.gpr]; exact c3, by rw [F.gpr]; exact c4, by rw [F.gpr]; exact c5,
      by rw [F.gpr]; exact c6, by rw [F.gpr, F.mem]; exact c7⟩)
    ⟨R, by rw [mt]; exact Outside.refl _ _ _ _, r6, by rw [p1]; exact (BitVec.add_zero _).symm,
      by rw [p8]; exact (BitVec.add_zero _).symm, by rw [r3]; decide, by simp only [r3, val32]; rfl⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨Ru, Ou, _, _, _, Cu, V⟩ _ =>
      ⟨chain_low (val32_lt _ _ _ _) Cu V, Ru, Ou⟩
  intro j hj u ⟨Ru, Ou, r6u, p1u, p8u, Cu, V⟩ pu p9u
  obtain wu := hs.of_rest Ru (by decide)
  obtain e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  refine wp_ldr (by decide) (wu.ea (K := a + 4 * j) (at_ptr pu e12) (by omega_arith))
    (wu.read (d := a + 4 * j + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
  obtain w₁ := wu.of_upd v₁ (by decide)
  refine wp_ldr (by decide) (w₁.ea (K := b + 4 * j) (at_ptr (by rw [v₁.other .r1 (by decide)]; exact p1u)
    (by rw [v₁.other .r12 (by decide)]; exact e12)) (by omega_arith))
    (w₁.read (d := b + 4 * j + 0) (n := 4) (by omega_arith)) fun u₂ v₂ => ?_
  obtain r7v : (u₂.gpr .r7).toNat = w32 s.mem base (a + 4 * j) := by
    rw [v₂.other .r7 (by decide), v₁.gpr, Nat.add_zero]; exact Ou.w32 (by omega_arith) (by omega_arith)
  obtain r5v : (u₂.gpr .r5).toNat = w32 s.mem base (b + 4 * j) := by
    rw [v₂.gpr, v₁.mem, Nat.add_zero]; exact Ou.w32 (by omega_arith) (by omega_arith)
  obtain c₂ : u₂.gpr .r3 = u.gpr .r3 := by rw [v₂.other .r3 (by decide), v₁.other .r3 (by decide)]
  obtain r6₂ : u₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [v₂.other .r6 (by decide), v₁.other .r6 (by decide)]; exact r6u
  refine borrowDigit_ok (h := 0) (by decide) r6₂ (by rw [c₂]; exact Cu) fun u₃ X₃ C₃ R₃ M₃ => ?_
  obtain r6₃ : u₃.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [R₃.gpr _ (by decide)]; exact r6₂
  refine wp_dp (op2_reg _ _) fun u₃' v₃ => ?_
  obtain b₃ : (u₃'.gpr .r3).toNat ≤ 1 := by
    have := hdig_lt (u₂.gpr .r7).toNat 0
    rw [v₃.other .r3 (by decide), C₃, X₃, c₂]; omega_arith
  refine borrowDigit_ok (h := 1) (by decide) (by rw [v₃.other .r6 (by decide)]; exact r6₃) b₃
    fun u₄ X₄ C₄ R₄ M₄ => ?_
  refine wp_dp (op2_lsl (by decide)) fun u₅ v₅ => ?_
  obtain w₅ : Ws u₅ base size := ((((w₁.of_upd v₂ (by decide)).of_rest R₃ (by decide)).of_upd v₃ (by decide)).of_rest
    R₄ (by decide)).of_upd v₅ (by decide)
  obtain e8 : u₅.gpr .r8 = u₅.gpr .r12 + BitVec.ofNat 32 (o + 4 * j) := by
    rw [v₅.other .r8 (by decide), v₅.other .r12 (by decide), R₄.gpr .r8 (by decide), R₄.gpr .r12 (by decide),
      v₃.other .r8 (by decide), v₃.other .r12 (by decide), R₃.gpr .r8 (by decide), R₃.gpr .r12 (by decide),
      v₂.other .r8 (by decide), v₂.other .r12 (by decide), v₁.other .r8 (by decide), v₁.other .r12 (by decide)]
    exact at_ptr p8u e12
  refine wp_str (by decide) (w₅.ea (d := 0) e8 (by omega_arith)) (w₅.write (d := o + 4 * j + 0) (n := 4) (by omega_arith))
    fun u₆ m₆ => wp_bump (by decide) fun u₇ v₇ => wp_bump (by decide) fun u₈ v₈ => wp_bump (by decide) fun u₉ v₉ =>
      WP.block_nil ?_
  rw [v₃.other .r7 (by decide), v₃.other .r5 (by decide), R₃.gpr .r7 (by decide), R₃.gpr .r5 (by decide), r7v, r5v,
    v₃.other .r3 (by decide)] at X₄
  rw [c₂] at X₃
  obtain ⟨hw, hc'⟩ := borrowWord (u := u₂) r7v r5v (by rw [c₂]; exact Cu) (by rw [c₂]; exact X₃) C₃ X₄ C₄
    (BitVec.isLt _) (BitVec.isLt _)
  rw [c₂] at hw
  -- The packed word.
  obtain r2₄ : (u₄.gpr .r2).toNat = (u₃.gpr .r4).toNat % 2 ^ 16 := by
    rw [R₄.gpr .r2 (by decide), v₃.gpr, dpVal, toNat_and_r6 r6₃]
  obtain pk : (u₅.gpr .r2).toNat = (u₃.gpr .r4).toNat % 2 ^ 16 + (u₄.gpr .r4).toNat % 2 ^ 16 * 2 ^ 16 := by
    rw [v₅.gpr, dpVal, pack_toNat _ _ (by rw [r2₄]; omega_arith), r2₄]
  rw [← pk] at hw
  obtain hnw : base.toNat + (o + 4 * j) + 4 ≤ 2 ^ 32 := by omega_arith
  obtain m₉ : u₉.mem = u.mem.writeW (off base (o + 4 * j)) (u₅.gpr .r2) := by
    rw [v₉.mem, v₈.mem, v₇.mem, m₆.mem, v₅.mem, M₄, v₃.mem, M₃, v₂.mem, v₁.mem, Nat.add_zero]
  obtain Vo : val32 u₉.mem base o j = val32 u.mem base o j := by
    rw [m₉]; exact val32_congr fun i hi => w32_write_lt hnw (by omega_arith) _
  obtain Wo : w32 u₉.mem base (o + 4 * j) = (u₅.gpr .r2).toNat := by rw [m₉, w32_write_self]
  obtain ⟨_, heq⟩ := chain_next (val32_lt u.mem base o j) (BitVec.isLt _) V hw
  obtain c₉ : u₉.gpr .r3 = u₄.gpr .r3 := by
    rw [v₉.other .r3 (by decide), v₈.other .r3 (by decide), v₇.other .r3 (by decide), m₆.gpr, v₅.other .r3 (by decide)]
  refine ⟨⟨(((((Ru.trans (((v₁.rest (by decide)).trans (v₂.rest (by decide))).trans
    ((R₃.mono (by decide)).trans (v₃.rest (by decide))))).trans ((R₄.mono (by decide)).trans (v₅.rest (by decide)))).trans
    (m₆.rest _)).trans (v₇.rest (by decide))).trans (v₈.rest (by decide))).trans (v₉.rest (by decide)),
    by rw [m₉]; exact Ou.write32 (by omega_arith) (by omega_arith) (by omega_arith) _, ?_, ?_, ?_, by rw [c₉]; exact hc', ?_⟩, ?_, ?_⟩
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r6 (by decide), v₃.other .r6 (by decide)]; exact r6₃
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r1 (by decide), v₃.other .r1 (by decide), R₃.gpr .r1 (by decide), v₂.other .r1 (by decide),
      v₁.other .r1 (by decide)]; exact ptr_step p1u
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r8 (by decide), v₃.other .r8 (by decide), R₃.gpr .r8 (by decide), v₂.other .r8 (by decide),
      v₁.other .r8 (by decide)]; exact ptr_step p8u
  · rw [c₉, pow32_succ, val32_succ, val32_succ, val32_succ, Vo, Wo]
    exact heq
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r10 (by decide), v₃.other .r10 (by decide), R₃.gpr .r10 (by decide), v₂.other .r10 (by decide),
      v₁.other .r10 (by decide)]; exact ptr_step pu
  · simp only [v₉.get, v₈.get, v₇.get, m₆.gpr, v₅.get, reduceCtorEq, ↓reduceIte]
    rw [R₄.gpr .r9 (by decide), v₃.other .r9 (by decide), R₃.gpr .r9 (by decide), v₂.other .r9 (by decide),
      v₁.other .r9 (by decide)]; exact p9u

/-! ## Nonzero and equality -/

theorem val32_succ_eq_zero (m : Mem) (base : Addr) (a j : Nat) :
    val32 m base a (j + 1) = 0 ↔ val32 m base a j = 0 ∧ w32 m base (a + 4 * j) = 0 := by
  have : (2 : Nat) ^ (32 * j) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
  rw [val32_succ, Nat.add_eq_zero_iff, Nat.mul_eq_zero]
  simp only [this, false_or]

/-- `r2` is all ones iff `[a] ≠ 0`. -/
theorem nonzero_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) :
    WP isa (nonzero k a) s fun t =>
      t.gpr .r2 = mask32 (val32 s.mem base a k ≠ 0) ∧ Rest ltClob s t ∧ t.mem = s.mem := by
  have hn := hs.nowrap
  unfold nonzero
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ =>
    wp_ptr (d := .r10) (by decide) (by omega_arith) fun s₂ u₂ =>
    wp_ptr (d := .r9) (by decide) (by omega_arith) fun t u₃ => WP.block_nil ?_)
  obtain R : Rest ltClob s t := ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))
  obtain mt : t.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain r3 : t.gpr .r3 = 0 := by simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 a := by
    simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * k) := by
    simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  clear u₁ u₂ u₃
  refine WP.seq (ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 a) (step := 4) (k := k)
    (fun j u => Rest ltClob s u ∧ u.mem = s.mem ∧ (u.gpr .r3 = 0 ↔ val32 s.mem base a j = 0))
    (by decide) hk (by omega_arith) (fun j u u' ⟨c1, c2, c3⟩ F => ⟨c1.trans (F.rest _),
      by rw [F.mem]; exact c2, by rw [F.gpr]; exact c3⟩)
    ⟨R, mt, by rw [r3]; exact ⟨fun _ => rfl, fun _ => rfl⟩⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨Ru, Mu, Zu⟩ _ => ?_)
  · intro j hj u ⟨Ru, Mu, Zu⟩ pu p9u
    obtain wu := hs.of_rest Ru (by decide)
    obtain e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
    refine wp_ldr (by decide) (wu.ea (K := a + 4 * j) (at_ptr pu e12) (by omega_arith))
      (wu.read (d := a + 4 * j + 0) (n := 4) (by omega_arith)) fun u₁ v₁ => ?_
    refine wp_dp (op2_reg _ _) fun u₂ v₂ => wp_bump (by decide) fun u₃ v₃ => WP.block_nil
      ⟨⟨((Ru.trans (v₁.rest (by decide))).trans (v₂.rest (by decide))).trans (v₃.rest (by decide)),
        by rw [v₃.mem, v₂.mem, v₁.mem, Mu], ?_⟩, ?_, ?_⟩
    · have hor : ∀ x y : BitVec 32, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
      rw [v₃.other .r3 (by decide), v₂.gpr, dpVal, hor, v₁.other .r3 (by decide), Zu, v₁.gpr, Mu,
        Nat.add_zero, w32_eq_zero_iff, val32_succ_eq_zero]
    · rw [v₃.gpr, v₂.other .r10 (by decide), v₁.other .r10 (by decide)]; exact ptr_step pu
    · rw [v₃.other .r9 (by decide), v₂.other .r9 (by decide), v₁.other .r9 (by decide)]; exact p9u
  · refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
    refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
    refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
    refine wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
    refine wp_dp (op2_reg _ _) fun s₈ u₈ => WP.block_nil ⟨?_, ?_, ?_⟩
    · have r3₅ : s₅.gpr .r3 = u.gpr .r3 := by
        rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide)]
      obtain r4₆ : s₆.gpr .r4 = if u.gpr .r3 = 0 then 0 else 1 := by
        rw [u₆.gpr, u₅.gpr, dpVal, u₄.gpr, dpVal, u₃.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
          ← r3₅, negOr_shr, r3₅]
      rw [u₈.gpr, dpVal, u₇.gpr, u₇.other _ (by decide), r4₆]
      have : (if u.gpr .r3 = 0 then (0 : BitVec 32) else 1) = if decide (u.gpr .r3 ≠ 0) then 1 else 0 := by
        by_cases h : u.gpr .r3 = 0 <;> simp [h]
      rw [this, neg_bit32]
      simp only [mask32, decide_eq_true_eq, ne_eq, Zu]
    · exact Ru.trans ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans
        ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans ((u₇.rest (by decide)).trans (u₈.rest (by decide)))))))
    · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, Mu]

theorem mask_not (p : Prop) [Decidable p] : mask32 p ^^^ BitVec.allOnes 32 = mask32 (¬ p) := by
  by_cases hp : p <;> simp only [mask32, hp, not_true_eq_false, not_false_eq_true, ite_true, ite_false] <;> decide

/-- `allOnes` then `eor r2 r2 r4` negates the mask in `r2`. -/
theorem wp_not {s : State} {is : List Instr} {Q : State → Prop} {p : Prop} [Decidable p]
    (h2 : s.gpr .r2 = mask32 p)
    (k : ∀ t, t.gpr .r2 = mask32 (¬ p) → Rest [.r2, .r4] s t → t.mem = s.mem → WP isa (.block is) t Q) :
    WP isa (.block (allOnes ++ .dp .eor .r2 .r2 (.reg .r4) :: is)) s Q := by
  simp only [allOnes, List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_dp (op2_imm (by decide)) fun s₂ u₂ =>
    wp_dp (op2_reg _ _) fun t u₃ => k t ?_ (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans
      (u₃.rest (by decide))) (by rw [u₃.mem, u₂.mem, u₁.mem])
  rw [u₃.gpr, dpVal, u₂.gpr, u₂.other .r2 (by decide), u₁.gpr, u₁.other .r2 (by decide), dpVal, h2, ← mask_not]
  rfl

/-- `r2` is all ones iff `[a] = [b]`. -/
theorem equal_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a b : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (hb : b + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) (h16b : b + 4 * k < 2 ^ 16) :
    WP isa (equal k a b) s fun t =>
      t.gpr .r2 = mask32 (val32 s.mem base a k = val32 s.mem base b k) ∧ Rest dclob s t ∧ t.mem = s.mem := by
  unfold equal
  refine WP.seq (WP.mono (lessThan_ok hs hk ha hb h16a (by omega_arith)) fun u ⟨eu, Ru, mu⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun v uv => WP.block_nil ?_)
  obtain Rv : Rest dclob s v := (Ru.mono (by decide)).trans (uv.rest (by decide))
  refine WP.seq (WP.mono (lessThan_ok (hs.of_rest Rv (by decide)) hk hb ha h16b (by omega_arith))
    fun w ⟨ew, Rw, mw⟩ => ?_)
  refine wp_dp (op2_reg _ _) fun x ux => ?_
  obtain vm : v.mem = s.mem := by rw [uv.mem, mu]
  rw [vm] at ew
  obtain r8w : w.gpr .r8 = mask32 (val32 s.mem base a k < val32 s.mem base b k) := by
    rw [Rw.gpr .r8 (by decide), uv.gpr, eu]
  obtain hx : x.gpr .r2 = mask32 ¬(val32 s.mem base a k = val32 s.mem base b k) := by
    rw [ux.gpr, dpVal, ew, r8w]
    generalize val32 s.mem base a k = A
    generalize val32 s.mem base b k = B
    rcases Nat.lt_trichotomy A B with h | rfl | h
    · simp only [mask32, h, Nat.lt_asymm h, Nat.ne_of_lt h, ↓reduceIte, not_false_eq_true]; decide
    · simp only [mask32, Nat.lt_irrefl, ↓reduceIte, not_true_eq_false]; decide
    · simp only [mask32, h, Nat.lt_asymm h, Nat.ne_of_gt h, ↓reduceIte, not_false_eq_true]; decide
  refine wp_not hx fun t e Rt mt => WP.block_nil ⟨?_, ((((Ru.mono (by decide)).trans (uv.rest (by decide))).trans
    (Rw.mono (by decide))).trans (ux.rest (by decide))).trans (Rt.mono (by decide)), by rw [mt, ux.mem, mw, vm]⟩
  rw [e]
  by_cases h : val32 s.mem base a k = val32 s.mem base b k <;> simp only [mask32, h, ↓reduceIte, not_true_eq_false,
    not_false_eq_true]

/-! ## The flag -/

/-- The flag word at `flag`. -/
abbrev flagW (base : Addr) (flag : Nat) (s : State) : BitVec 32 := s.mem.readW (off base flag) 32

/-- `[flag] &= r2`, through `r4`. -/
theorem andFlag_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {flag : Nat}
    (hf : flag + 4 ≤ size) (hf4 : flag < 4096) :
    WP isa (.block (andFlag flag)) s fun t =>
      flagW base flag t = flagW base flag s &&& s.gpr .r2 ∧ Rest [.r4] s t ∧ Outside base flag 4 s.mem t.mem := by
  have hn := hs.nowrap
  simp only [andFlag]
  refine wp_ldr hf4 (hs.ea12 (by omega_arith)) (hs.read hf) fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  obtain k₂ : Rest [.r4] s s₂ := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  obtain hs₂ := hs.of_rest k₂ (by decide)
  refine wp_str hf4 (hs₂.ea12 (by omega_arith)) (hs₂.write hf) fun s₃ m₃ => WP.block_nil ⟨?_, k₂.trans (m₃.rest _), ?_⟩
  · rw [flagW, flagW, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, dpVal, u₁.gpr, u₁.other _ (by decide)]
  · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega_arith)

theorem mask32_iff {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : mask32 p = mask32 q := by
  by_cases hp : p
  · simp only [mask32, hp, h.mp hp, ↓reduceIte]
  · simp only [mask32, hp, mt h.mpr hp, ↓reduceIte]

/-- The flag `&=` the mask of `0 < [a] < [m]`. -/
theorem checkRange_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a m flag : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (hm : m + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) (h16m : m < 2 ^ 16)
    (hf : flag + 4 ≤ size) (hf4 : flag < 4096) :
    WP isa (checkRange k a m flag) s fun t =>
      flagW base flag t = flagW base flag s &&&
        mask32 (0 < val32 s.mem base a k ∧ val32 s.mem base a k < val32 s.mem base m k) ∧
      Rest dclob s t ∧ Outside base flag 4 s.mem t.mem := by
  unfold checkRange
  refine WP.seq (WP.mono (lessThan_ok hs hk ha hm h16a h16m) fun u ⟨eu, Ru, mu⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun v uv => WP.block_nil ?_)
  obtain Rv : Rest dclob s v := (Ru.mono (by decide)).trans (uv.rest (by decide))
  refine WP.seq (WP.mono (nonzero_ok (hs.of_rest Rv (by decide)) hk ha h16a) fun w ⟨ew, Rw, mw⟩ => ?_)
  refine wp_dp (op2_reg _ _) fun x ux => ?_
  obtain Rx : Rest dclob s x := (Rv.trans (Rw.mono (by decide))).trans (ux.rest (by decide))
  obtain mx : x.mem = s.mem := by rw [ux.mem, mw, uv.mem, mu]
  refine WP.mono (andFlag_ok (hs.of_rest Rx (by decide)) hf hf4) fun t ⟨et, Rt, Ot⟩ =>
    ⟨?_, Rx.trans (Rt.mono (by decide)), by rw [← mx]; exact Ot⟩
  rw [et, flagW, flagW, mx, ux.gpr, dpVal, ew, Rw.gpr .r8 (by decide), uv.gpr, eu, uv.mem, mu, mask32_and]
  exact congrArg _ (mask32_iff (by rw [Nat.pos_iff_ne_zero]))

/-- The flag `&=` the mask of `[a] ≠ 0` (`wantNonzero`) or of `[a] = 0`. -/
theorem checkZero_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a flag : Nat} (hk : 0 < k)
    (ha : a + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16) (hf : flag + 4 ≤ size) (hf4 : flag < 4096)
    (wantNonzero : Bool) :
    WP isa (checkZero k a flag wantNonzero) s fun t =>
      flagW base flag t = flagW base flag s &&&
        mask32 (if wantNonzero then val32 s.mem base a k ≠ 0 else val32 s.mem base a k = 0) ∧
      Rest dclob s t ∧ Outside base flag 4 s.mem t.mem := by
  unfold checkZero
  refine WP.seq (WP.mono (nonzero_ok hs hk ha h16a) fun u ⟨eu, Ru, mu⟩ => ?_)
  obtain wu := hs.of_rest Ru (by decide)
  cases wantNonzero
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append]
    refine wp_not eu fun v ev Rv mv => WP.mono (andFlag_ok (wu.of_rest Rv (by decide)) hf hf4) fun t ⟨et, Rt, Ot⟩ =>
      ⟨?_, ((Ru.mono (by decide)).trans (Rv.mono (by decide))).trans (Rt.mono (by decide)),
        by rw [← mu, ← mv]; exact Ot⟩
    rw [et, flagW, flagW, mv, mu, ev]
    exact congrArg _ (mask32_iff Classical.not_not)
  · simp only [↓reduceIte, List.nil_append]
    refine WP.mono (andFlag_ok wu hf hf4) fun t ⟨et, Rt, Ot⟩ =>
      ⟨?_, (Ru.mono (by decide)).trans (Rt.mono (by decide)), by rw [← mu]; exact Ot⟩
    rw [et, flagW, flagW, mu, eu]

/-! ## Constants -/

theorem wp_movt {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (VG.Proof.X25519.Arm.Upd.setReg _ _ _))

/-- `movImm x` builds `x`'s low word. -/
theorem movImm_val (x : Nat) :
    (BitVec.ofNat 16 (x >>> 16) ++ ((BitVec.ofNat 16 x).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _)]
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  omega_arith

/-- A number from its words. -/
theorem val32_of_words {m : Mem} {base : Addr} {o x : Nat} :
    ∀ {k}, (∀ i < k, w32 m base (o + 4 * i) = x >>> (32 * i) % 2 ^ 32) → val32 m base o k = x % 2 ^ (32 * k)
  | 0, _ => by simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | k + 1, h => by
    rw [val32_succ, val32_of_words fun i hi => h i (by omega_arith), h k (by omega_arith), Nat.shiftRight_eq_div_pow,
      show 32 * (k + 1) = 32 * k + 32 by omega_arith, Nat.pow_add, Nat.mod_mul]

/-- The nonzero words of a constant, stored at `[r10 + 4i]`. -/
theorem constWords_ok {u : State} {base : Addr} {size : Nat} (hs : Ws u base size) {k o x : Nat}
    (h10 : u.gpr .r10 = u.gpr .r12 + BitVec.ofNat 32 o) (ho : o + 4 * k ≤ size) (hk4 : 4 * k ≤ 4096)
    (hz : ∀ i < k, w32 u.mem base (o + 4 * i) = 0) :
    ∀ j ≤ k, WP isa (.block ((List.range j).flatMap fun i =>
        if x >>> (32 * i) % 2 ^ 32 = 0 then [] else movImm (x >>> (32 * i)) ++
          ([.str .r4 .r10 (4 * i)] : List Instr))) u fun t =>
      Rest [.r4] u t ∧ (∀ i < k, w32 t.mem base (o + 4 * i) = if i < j then x >>> (32 * i) % 2 ^ 32 else 0) ∧
      Outside base o (4 * k) u.mem t.mem
  | 0, _ => WP.block_nil ⟨Rest.refl _ _, fun i hi => by rw [hz i hi]; rfl, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (constWords_ok hs h10 ho hk4 hz j (by omega_arith)) fun t ⟨R, V, O⟩ => ?_
    by_cases hx : x >>> (32 * j) % 2 ^ 32 = 0
    · rw [ite_eq_left hx]
      refine WP.block_nil ⟨R, fun i hi => ?_, O⟩
      rw [V i hi]
      rcases Nat.lt_trichotomy i j with h | rfl | h
      · rw [ite_eq_left h, ite_eq_left (by omega_arith)]
      · rw [ite_eq_right (Nat.lt_irrefl _), ite_eq_left (Nat.lt_succ_self _), hx]
      · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
    · rw [ite_eq_right hx]
      obtain wt := hs.of_rest R (by decide)
      obtain e10 : t.gpr .r10 = t.gpr .r12 + BitVec.ofNat 32 o := by
        rw [R.gpr .r10 (by decide), R.gpr .r12 (by decide)]; exact h10
      simp only [movImm, List.cons_append, List.nil_append]
      refine wp_movw fun t₁ v₁ => wp_movt fun t₂ v₂ => ?_
      obtain w₂ := (wt.of_upd v₁ (by decide)).of_upd v₂ (by decide)
      refine wp_str (by omega_arith) (w₂.ea (K := o) (d := 4 * j)
        (by rw [v₂.other .r10 (by decide), v₁.other .r10 (by decide), v₂.other .r12 (by decide),
          v₁.other .r12 (by decide)]; exact e10) (by omega_arith))
        (w₂.write (d := o + 4 * j) (n := 4) (by omega_arith)) fun t₃ m₃ => WP.block_nil ⟨?_, fun i hi => ?_, ?_⟩
      · exact ((R.trans (v₁.rest (by decide))).trans (v₂.rest (by decide))).trans (m₃.rest _)
      · have hv : t₂.gpr .r4 = BitVec.ofNat 32 (x >>> (32 * j)) := by rw [v₂.gpr, v₁.gpr, movImm_val]
        rw [m₃.mem, v₂.mem, v₁.mem, hv]
        rcases Nat.lt_trichotomy i j with h | rfl | h
        · rw [w32_write_lt (by omega_arith) (by omega_arith), V i hi, ite_eq_left h, ite_eq_left (by omega_arith)]
        · rw [w32_write_self, BitVec.toNat_ofNat, ite_eq_left (Nat.lt_succ_self _)]
        · rw [w32_write_ne (size := o + 4 * k) (by omega_arith) (by omega_arith) (by omega_arith) (.inr (by omega_arith)), V i hi,
            ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
      · rw [m₃.mem, v₂.mem, v₁.mem]; exact O.write32 (by omega_arith) (by omega_arith) (by omega_arith) _

/-- `[o] = x` modulo `2^(32k)`. -/
theorem setConst_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k o x : Nat} (hk : 0 < k)
    (ho : o + 4 * k ≤ size) (h16 : o + 4 * k < 2 ^ 16) (hk4 : 4 * k ≤ 4096) :
    WP isa (setConst k o x) s fun t =>
      val32 t.mem base o k = x % 2 ^ (32 * k) ∧ Rest dclob s t ∧ Outside base o (4 * k) s.mem t.mem := by
  unfold Dynamic.setConst
  refine WP.seq (WP.mono (zeros_ok hs hk ho h16) fun u ⟨wu, Z, O, R⟩ => ?_)
  refine wp_ptr (d := .r10) (by decide) (by omega_arith) fun v uv => ?_
  obtain wv := wu.of_upd uv (by decide)
  refine WP.mono (constWords_ok wv (k := k) (x := x)
    (by rw [uv.gpr, uv.other .r12 (by decide)]) ho hk4 (fun i hi => by rw [uv.mem]; exact Z i hi) k (Nat.le_refl _))
    fun t ⟨Rt, Vt, Ot⟩ => ⟨val32_of_words fun i hi => by rw [Vt i hi, ite_eq_left hi], ((R.mono (by decide)).trans
      (uv.rest (by decide))).trans (Rt.mono (by decide)), by rw [← uv.mem] at O; exact O.trans Ot⟩

/-- `r2` is all ones iff `[a] < x`, through `[tmp]`. -/
theorem lessThanConstant_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k a tmp x : Nat}
    (hk : 0 < k) (ha : a + 4 * k ≤ size) (ht : tmp + 4 * k ≤ size) (h16a : a + 4 * k < 2 ^ 16)
    (h16t : tmp + 4 * k < 2 ^ 16) (hk4 : 4 * k ≤ 4096) (hx : x < 2 ^ (32 * k))
    (hsep : a + 4 * k ≤ tmp ∨ tmp + 4 * k ≤ a) :
    WP isa (lessThanConstant k a tmp x) s fun t =>
      t.gpr .r2 = mask32 (val32 s.mem base a k < x) ∧ Rest dclob s t ∧ Outside base tmp (4 * k) s.mem t.mem := by
  have hn := hs.nowrap
  unfold lessThanConstant
  refine WP.seq (WP.mono (setConst_ok hs hk ht h16t hk4) fun u ⟨Vu, Ru, Ou⟩ => ?_)
  refine WP.mono (lessThan_ok (hs.of_rest Ru (by decide)) hk ha ht h16a (by omega_arith)) fun t ⟨et, Rt, mt⟩ =>
    ⟨?_, Ru.trans (Rt.mono (by decide)), by rw [mt]; exact Ou⟩
  rw [et, Vu, Nat.mod_eq_of_lt hx, Ou.val32 hsep (by omega_arith)]

/-! ## Widths -/

/-- `r2` is all ones iff `2^(bits-1) ≤ [a] < 2^bits`, for `0 < bits ≤ 64n`; `r11` changes too. -/
theorem widthMask_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n a tmp bits : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size) (h16a : a + 8 * n < 2 ^ 16)
    (h16t : tmp + 8 * n < 2 ^ 16) (hn4 : 8 * n ≤ 4096) (hb : 0 < bits) (hbn : bits ≤ 64 * n)
    (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (widthMask n a tmp bits) s fun t =>
      t.gpr .r2 = mask32 (2 ^ (bits - 1) ≤ val32 s.mem base a (2 * n) ∧ val32 s.mem base a (2 * n) < 2 ^ bits) ∧
      Rest (.r11 :: dclob) s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  obtain e8 : 4 * (2 * n) = 8 * n := by omega_arith
  obtain e64 : 32 * (2 * n) = 64 * n := by omega_arith
  obtain hp1 : 2 ^ (bits - 1) < 2 ^ (32 * (2 * n)) := by
    rw [e64]; exact Nat.pow_lt_pow_right (by decide) (by omega_arith)
  unfold widthMask
  refine WP.seq (WP.mono (lessThanConstant_ok hs (k := 2 * n) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) hp1 (by omega_arith)) fun u ⟨eu, Ru, Ou⟩ => ?_)
  refine WP.seq (wp_not eu fun v ev Rv mv => wp_mov (op2_reg _ _) fun w uw => WP.block_nil ?_)
  obtain Rw : Rest (.r11 :: dclob) s w :=
    ((Ru.mono (by decide)).trans (Rv.mono (by decide))).trans (uw.rest (by decide))
  obtain mw : w.mem = u.mem := by rw [uw.mem, mv]
  obtain r11 : w.gpr .r11 = mask32 ¬(val32 s.mem base a (2 * n) < 2 ^ (bits - 1)) := by rw [uw.gpr, ev]
  obtain Ow : Outside base tmp (8 * n) s.mem w.mem := by rw [mw, ← e8]; exact Ou
  split
  · refine WP.seq (WP.mono (lessThanConstant_ok (hs.of_rest Rw (by decide)) (k := 2 * n) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by rw [e64]; exact Nat.pow_lt_pow_right (by decide) (by omega_arith))
      (by omega_arith)) fun x ⟨ex, Rx, Ox⟩ => ?_)
    refine wp_dp (op2_reg _ _) fun t ut => WP.block_nil ⟨?_, (Rw.trans (Rx.mono (by decide))).trans
      (ut.rest (by decide)), by rw [ut.mem]; exact Ow.trans (e8 ▸ Ox)⟩
    rw [ut.gpr, dpVal, ex, Rx.gpr .r11 (by decide), r11, mw, mask32_and, Ou.val32 (by omega_arith) (by omega_arith)]
    exact mask32_iff (by rw [Nat.not_lt, and_comm])
  · refine wp_mov (op2_reg _ _) fun t ut => WP.block_nil ⟨?_, Rw.trans (ut.rest (by decide)),
      by rw [ut.mem]; exact Ow⟩
    obtain hlt := val32_lt u.mem base a (2 * n)
    rw [ut.gpr, r11]
    rw [Ou.val32 (by omega_arith) (by omega_arith), e64] at hlt
    have : 2 ^ (64 * n) ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) (by omega_arith)
    exact mask32_iff ⟨fun h => ⟨Nat.not_lt.mp h, by omega_arith⟩, fun h => Nat.not_lt.mpr h.1⟩

/-- A width larger than the buffer cannot match. -/
theorem optionalWidth_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n a tmp bits : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (ht : tmp + 8 * n ≤ size) (h16a : a + 8 * n < 2 ^ 16)
    (h16t : tmp + 8 * n < 2 ^ 16) (hn4 : 8 * n ≤ 4096) (hb : 0 < bits)
    (hsep : a + 8 * n ≤ tmp ∨ tmp + 8 * n ≤ a) :
    WP isa (optionalWidth n a tmp bits) s fun t =>
      t.gpr .r2 = mask32 (2 ^ (bits - 1) ≤ val32 s.mem base a (2 * n) ∧ val32 s.mem base a (2 * n) < 2 ^ bits) ∧
      Rest (.r11 :: dclob) s t ∧ Outside base tmp (8 * n) s.mem t.mem := by
  unfold optionalWidth
  split
  · exact widthMask_ok hs hn ha ht h16a h16t hn4 hb (by omega_arith) hsep
  · refine wp_mov (op2_imm (by decide)) fun t ut => WP.block_nil ⟨?_, ut.rest (by decide),
      by rw [ut.mem]; exact Outside.refl _ _ _ _⟩
    obtain hlt := val32_lt s.mem base a (2 * n)
    have : 2 ^ (32 * (2 * n)) ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by omega_arith)
    rw [ut.gpr]
    rw [mask32_iff (q := False) ⟨fun h => by omega_arith, False.elim⟩]
    rfl

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.Doubling`, which only this module used -/

section

/-! # Counted modular doubling on ARMv7

The public counter stays in registers: `r1` across digit addition, then `r0`
across conditional subtraction. The arithmetic and memory bounds are those
of the existing addition and subtraction kernels.
-/

@[expose] public section
namespace VG.Proof.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_movw wp_subs op2_reg op2_imm)

theorem countedDouble_parts_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hv : val32 s.mem base (slot n 9) (2 * n) < m) :
    WP isa (countedDouble n) s fun t => Ws t base size ∧
      val32 t.mem base (resS n) (2 * n) =
        (val32 s.mem base (resS n) (2 * n) + val32 s.mem base (resS n) (2 * n)) % m ∧
      Outs base [(resS n, 8 * n), (tmpS n, 8 * n), (accS n, 4 * (8 * n + 2))] s.mem t.mem ∧
      Rest dclob s t ∧ t.gpr .r0 = s.gpr .r1 := by
  let M := contextMod n
  let acc := accS n
  let o := resS n
  let a := resS n
  let b := resS n
  have hs := h.ws
  have hn : 0 < M.n := h.n0
  obtain hL : MulLayD M size invO acc o a b :=
    context_lay h.size_le h.small (by decide) (by decide) (by decide)
  have hm : val32 s.mem base M.mo (words M) = m := h.modulus
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  have hA : val32 s.mem base a (words M) < m := hv
  have hB : val32 s.mem base b (words M) < m := hv
  suffices H : WP isa (countedDouble n) s fun t => Ws t base size ∧
    val32 t.mem base o (words M) = (val32 s.mem base a (words M) + val32 s.mem base b (words M)) % m ∧
    Outs base [(o, 4 * words M), (M.tmp, 4 * words M), (acc, 4 * (4 * words M + 2))] s.mem t.mem ∧
    Rest dclob s t ∧ t.gpr .r0 = s.gpr .r1 by
    simpa only [M, o, a, b, acc, contextMod, Impl.Mont.Arm.words,
      show 4 * (2 * n) = 8 * n by omega_arith,
      show 4 * (4 * (2 * n) + 2) = 4 * (8 * n + 2) by omega_arith] using H
  have hnw := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  obtain hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_arith
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  rw [hW] at hm hA hB ⊢
  unfold countedDouble
  refine WP.seq (WP.mono (VG.Arm.WP.gpr (addDigits_ok hs (M := M) (acc := acc) (a := a) (b := b) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact a_le) (by rw [hW]; exact b_le)
    (by rw [hD]; omega_using [acc16]) (by rw [hW]; exact a16) (by omega_using [b16])
    (by rw [hD, hW]; omega_using [sa]) (by rw [hD, hW]; omega_using [sb])) (r := .r1) (by
      simp [instrs, addDigits, ptrLoop, ptr, addDigitD, half, bump, mask16] <;> (repeat' apply And.intro) <;> exact of_decide_eq_true rfl))
    fun t₀ ⟨⟨w₀, V₀, D₀, O₀, R₀⟩, C₀⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun t₁ U => WP.block_nil ?_)
  obtain w₁ := w₀.of_upd U (by decide)
  have V₁ := V₀
  have D₁ := D₀
  have O₁ := O₀
  rw [← U.mem] at V₁ D₁ O₁
  obtain R₁ := R₀.trans (U.rest (by decide : .r0 ∈ dclob))
  obtain C₁ : t₁.gpr .r0 = s.gpr .r1 := by rw [U.gpr, C₀]
  simp only [hD, hW] at V₁ D₁ O₁
  obtain hm₁ : val32 t₁.mem base M.mo W = m := by
    rw [O₁.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  refine WP.mono (VG.Arm.WP.gpr (csubD_ok w₁ (M := M) (src := acc) (o := o) (m := m) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact o_le) (by rw [hW]; exact tmp_le) (by rw [hW]; exact mo_le)
    (by rw [hD]; omega_using [acc16]) o16 (by rw [hW]; exact tmp16) (by rw [hW]; exact mo16)
    (by rw [hD, hW]; omega_using [stmp]) (by rw [hW]; exact tmo) (by rw [hD, hW]; omega_using [so])
    (by rw [hW]; exact ot) (by rw [hW]; exact hm₁) hm0 (by rw [hD]; exact D₁) (by rw [hD, V₁]; omega_using [hA, hB])) (r := .r0) (by
      simp [instrs, csubD, ptrLoop, ptr, diffDigitD, half, bump, mask16] <;> (repeat' apply And.intro) <;> exact of_decide_eq_true rfl))
    fun t ⟨⟨wt, V, O, R⟩, C⟩ => ⟨wt, ?_, ?_, R₁.trans R, C.trans C₁⟩
  · rw [hW] at V; rw [V, hD, V₁]
  · rw [hW] at O
    exact (Outs.of_outside (O₁.mono (o' := acc) (n' := 4 * (4 * W + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)).trans (O.mono (by simp))

/-- One doubling keeps the context and carries the counter into `r0`. -/
theorem countedDouble_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hv : val32 s.mem base (slot n 9) (2 * n) < m) :
    WP isa (countedDouble n) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) = 2 * val32 s.mem base (slot n 9) (2 * n) % m ∧
      t.gpr .r0 = s.gpr .r1 := by
  refine WP.mono (countedDouble_parts_ok h hv) fun t ⟨w, V, O, R, C⟩ => ?_
  obtain K : OpKeep n base 9 s t := ⟨R, O⟩
  exact ⟨h.keep (by decide) w K, K, by simpa only [resS, Nat.two_mul] using V, C⟩

structure DoubleInv (n m size k : Nat) (base : Addr) (s : State) (j : Nat) (u : State) : Prop where
  ctx : Context n m base size u
  val : val32 u.mem base (slot n 9) (2 * n) = 2 ^ j * val32 s.mem base (slot n 9) (2 * n) % m
  keep : OpKeep n base 9 s u
  count : u.gpr .r0 = BitVec.ofNat 32 (k - j)

theorem doubles_ok {n size m : Nat} {base : Addr} (k : Nat) {s : State}
    (h : Context n m base size s) (hv : val32 s.mem base (slot n 9) (2 * n) < m)
    (hk : k < 2 ^ 16) :
    WP isa (doubles n k) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) = 2 ^ k * val32 s.mem base (slot n 9) (2 * n) % m := by
  unfold doubles
  split
  · rename_i hz
    subst k
    exact WP.block_nil ⟨h, ⟨Rest.refl _ _, Outs.refl _ _ _⟩,
      by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hv]⟩
  · rename_i hk0
    refine WP.seq (wp_movw fun t U => WP.block_nil ?_)
    obtain c : Context n m base size t := ⟨h.ws.of_upd U (by decide), h.size_le, h.small, h.n0,
      by rw [U.mem]; exact h.modulus, h.gt_one, by rw [U.mem]; exact h.inverse⟩
    obtain I0 : DoubleInv n m size k base s 0 t := ⟨c,
      by rw [U.mem, Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hv],
      ⟨U.rest (by decide), by rw [U.mem]; exact Outs.refl _ _ _⟩,
      by rw [U.gpr, Nat.sub_zero, movw_ofNat hk]⟩
    refine WP.loop (M := isa) (fun r u => ∃ j, r = k - j ∧ j < k ∧ DoubleInv n m size k base s j u)
      ?_ k t ⟨0, rfl, by omega_arith, I0⟩
    rintro r u ⟨j, rfl, hj, I⟩
    refine WP.seq (wp_mov (op2_reg _ _) fun u₀ U₀ => WP.block_nil ?_)
    obtain c₀ : Context n m base size u₀ := ⟨I.ctx.ws.of_upd U₀ (by decide), I.ctx.size_le,
      I.ctx.small, I.ctx.n0, by rw [U₀.mem]; exact I.ctx.modulus, I.ctx.gt_one,
      by rw [U₀.mem]; exact I.ctx.inverse⟩
    obtain hm : 0 < m := by have := I.ctx.gt_one; omega_arith
    refine WP.seq (WP.mono (countedDouble_ok c₀ (by rw [U₀.mem, I.val]; exact Nat.mod_lt _ hm))
      fun u₁ ⟨c₁, K₁, V₁, C₁⟩ => ?_)
    refine wp_subs (op2_imm (by decide)) fun u₂ U₂ Z₂ => WP.block_nil ?_
    obtain I' : DoubleInv n m size k base s (j + 1) u₂ := by
      refine ⟨⟨c₁.ws.of_upd U₂ (by decide), c₁.size_le, c₁.small, c₁.n0,
        by rw [U₂.mem]; exact c₁.modulus, c₁.gt_one, by rw [U₂.mem]; exact c₁.inverse⟩, ?_, ?_, ?_⟩
      · rw [U₂.mem, V₁, U₀.mem, I.val, Nat.mul_mod_mod, Nat.pow_succ]
        congr 1
        ac_rfl
      · refine ⟨((I.keep.rest.trans (U₀.rest (by decide))).trans K₁.rest).trans (U₂.rest (by decide)), ?_⟩
        rw [U₂.mem]
        exact I.keep.mem.trans (by rw [← U₀.mem]; exact K₁.mem)
      · rw [U₂.gpr, C₁, U₀.gpr, I.count, ofNat_sub_one (by omega_arith) (by omega_arith)]
        congr 1
    obtain hz : u₂.z = decide (j + 1 = k) := by
      rw [Z₂, C₁, U₀.gpr, I.count, ofNat_sub_one (by omega_arith) (by omega_arith),
        VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
      simp only [decide_eq_decide]
      omega_arith
    by_cases hj1 : j + 1 = k
    · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hj1]; rfl,
        I'.ctx, I'.keep, by rw [I'.val, hj1]⟩
    · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hj1]; rfl,
        k - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, I'⟩

end VG.Proof.Dsa.Arm

end

end


/-!
# DSA on 32-bit ARM: the arithmetic on slots

`reduceStream n` reduces the bytes from `r11` to `lr` modulo the context's
modulus into the result slot (`reduceStream_ok`), a byte at a time
(`streamStep_ok`: eight doublings and the byte's addition); `modulusMinus`
writes `m - amount` (`modulusMinus_ok`), `ordinaryMul` and `ordinaryAdd`
multiply and add ordinary residues (`ordinaryMul_ok`, `ordinaryAdd_ok`).
All of them change only the result and product slots, the temporary slot and
the accumulator (`streamRanges`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_ldrb wp_dp wp_cmp op2_imm op2_reg dpVal eval_ne
  eval_eq)

theorem _root_.VG.Proof.Mont.Arm.Dyn.OpKeep.trans {n o : Nat} {base : Addr} {s t u : State}
    (h₁ : OpKeep n base o s t) (h₂ : OpKeep n base o t u) : OpKeep n base o s u :=
  ⟨h₁.rest.trans h₂.rest, h₁.mem.trans h₂.mem⟩

/-- The memory the slot arithmetic changes: the result and product slots, the
temporary slot and the accumulator. -/
abbrev streamRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 9, 8 * n), (slot n 10, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

theorem _root_.VG.Proof.Mont.Arm.Dyn.OpKeep.streamRanges {n o : Nat} {base : Addr} {s t : State}
    (K : OpKeep n base o s t) (ho : o = 9 ∨ o = 10 := by decide) : Outs base (streamRanges n) s.mem t.mem :=
  K.mem.mono fun r hr => by
    simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp

/-- Memory past the context is kept. -/
theorem Outs.outside {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m') {o n : Nat}
    (hr : ∀ r ∈ rs, o ≤ r.1 ∧ r.1 + r.2 ≤ o + n) : Outside base o n m m' :=
  fun x hx => h x fun r hr' => by have := hr r hr'; omega_arith

theorem streamRanges_inside (n : Nat) : ∀ r ∈ streamRanges n, 0 ≤ r.1 ∧ r.1 + r.2 ≤ 0 + contextBytes n := by
  obtain b9 := slot_bound (n := n) (i := 9) (by decide)
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain b1 := slot_le (n := n) (i := 1) (j := 2) (by decide)
  obtain b6 := slot_bound (n := n) (i := 6) (by decide)
  obtain a := slot_acc n
  simp only [stride] at *
  simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl) <;> constructor <;> omega_arith

/-! ## Doublings and a byte -/

theorem reduceStep_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hv : val32 s.mem base (slot n 9) (2 * n) < m) (hb : val32 s.mem base (slot n 10) (2 * n) < m) :
    WP isa (reduceStep n) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (256 * val32 s.mem base (slot n 9) (2 * n) + val32 s.mem base (slot n 10) (2 * n)) % m := by
  have m1 := h.gt_one
  obtain nw : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold reduceStep
  refine WP.seq (WP.mono (doubles_ok 8 h hv (by decide)) fun u ⟨cu, Ku, Vu⟩ => ?_)
  obtain Bu := Ku.val32 (i := 10) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw
  refine WP.mono (context_add_ok cu (o := 9) (a := 9) (b := 10) (by decide) (by decide) (by decide)
    (by rw [Vu]; exact Nat.mod_lt _ (by omega_arith)) (by rw [Bu]; exact hb)) fun t ⟨ct, Kt, Vt⟩ =>
    ⟨ct, Ku.trans Kt, ?_⟩
  rw [Vt, Vu, Bu, Nat.mod_add_mod]

/-- A number below `2³²` with its low word replaced. -/
theorem val32_low_write {m : Mem} {base : Addr} {d k : Nat} (hk : 0 < k) (hn : base.toNat + d + 4 * k ≤ 2 ^ 32)
    (hv : val32 m base d k < 2 ^ 32) (v : BitVec 32) : val32 (m.writeW (off base d) v) base d k = v.toNat := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  obtain hu : val32 (m.writeW (off base d) v) base (d + 4) j = val32 m base (d + 4) j :=
    val32_congr fun i hi => w32_write_ne (size := d + 4 * (j + 1)) (by omega_arith) (by omega_arith) (by omega_arith) (.inr (by omega_arith)) v
  rw [val32] at hv ⊢
  rw [w32_write_self, hu]
  omega_arith

theorem streamStep_ok {n size m i len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hi : i < len) (hlen : p.toNat + len ≤ 2 ^ 32)
    (hl : len < 2 ^ 32)
    (hc : s.gpr .r11 = p + BitVec.ofNat 32 i) (he : s.gpr .lr = p + BitVec.ofNat 32 len)
    (hr : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hv : val32 s.mem base (slot n 9) (2 * n) < m) (hpad : val32 s.mem base (slot n 10) (2 * n) < 2 ^ 32) :
    WP isa (streamStep n) s fun t =>
      Context n m base size t ∧ t.gpr .r11 = p + BitVec.ofNat 32 (i + 1) ∧ t.gpr .lr = s.gpr .lr ∧
      t.z = decide (i + 1 = len) ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (256 * val32 s.mem base (slot n 9) (2 * n) + (s.mem (State.addr p + BitVec.ofNat 64 i)).toNat) % m ∧
      val32 t.mem base (slot n 10) (2 * n) < 2 ^ 32 ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Rest (.r11 :: dclob) s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain s9 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have n0 := h.n0
  simp only [stride] at b10 s9
  unfold streamStep
  obtain ea : State.addr (s.gpr .r11 + BitVec.ofNat 32 0) = State.addr p + BitVec.ofNat 64 i := by
    rw [hc, Offset.add_add, Nat.add_zero, VG.Arm.addr_add (by omega_arith)]
  refine WP.seq (wp_ldrb (by decide) ea hr fun s₁ u₁ => wp_ptr (d := .r10) (by decide) (by simp only [prodS]; omega_arith)
    fun s₂ u₂ => ?_)
  obtain w₂ : Ws s₂ base size := (h.ws.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  refine wp_str (by decide) (w₂.ea (K := prodS n) (d := 0) (by simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte])
    (by simp only [prodS]; omega_arith)) (w₂.write (d := prodS n + 0) (n := 4) (by simp only [prodS]; omega_arith))
    fun s₃ m₃ => WP.block_nil ?_
  obtain mem₃ : s₃.mem = s.mem.writeW (off base (slot n 10)) (BitVec.setWidth 32 (s.mem (State.addr p + BitVec.ofNat 64 i))) := by
    rw [m₃.mem, u₂.mem, u₁.mem, u₂.other .r4 (by decide), u₁.gpr]; rfl
  obtain O₃ : Outside base (slot n 10) (8 * n) s.mem s₃.mem := by
    rw [mem₃]; exact (writeW32_outside _ _ _ (by omega_arith)).mono (Nat.le_refl _) (by omega_arith)
  obtain w₃ : Ws s₃ base size := w₂.of_mupd m₃
  obtain c₃ : Context n m base size s₃ := h.of_slot w₃ O₃ (by decide)
  obtain byte := (s.mem (State.addr p + BitVec.ofNat 64 i)).isLt
  obtain B₃ : val32 s₃.mem base (slot n 10) (2 * n) = (s.mem (State.addr p + BitVec.ofNat 64 i)).toNat := by
    rw [mem₃, val32_low_write (by omega_arith) (by omega_arith) hpad, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)]
  obtain Y₃ : val32 s₃.mem base (slot n 9) (2 * n) = val32 s.mem base (slot n 9) (2 * n) :=
    O₃.val32 (by omega_arith) (by omega_arith)
  obtain R₃ : Rest (.r11 :: dclob) s s₃ :=
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (m₃.rest _)
  refine WP.seq (WP.mono (reduceStep_ok c₃ (by rw [Y₃]; exact hv) (by rw [B₃]; omega_arith)) fun u ⟨cu, Ku, Vu⟩ => ?_)
  refine wp_dp (op2_imm (by decide)) fun t₁ v₁ => wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ?_
  obtain Ru : Rest (.r11 :: dclob) s u := R₃.trans (Ku.rest.mono (by decide))
  obtain r11 : t₁.gpr .r11 = p + BitVec.ofNat 32 (i + 1) := by
    rw [v₁.gpr, dpVal, Ku.rest.gpr .r11 (by decide), m₃.gpr, u₂.other .r11 (by decide),
      u₁.other .r11 (by decide), hc]
    show p + BitVec.ofNat 32 i + BitVec.ofNat 32 1 = _
    rw [Offset.add_add]
  obtain lr : t₁.gpr .lr = s.gpr .lr := by rw [v₁.other .lr (by decide)]; exact Ru.gpr .lr (by decide)
  obtain mt : t.mem = u.mem := by rw [f.mem, v₁.mem]
  refine ⟨⟨?_, c₃.size_le, c₃.small, c₃.n0, ?_, c₃.gt_one, ?_⟩, by rw [f.gpr]; exact r11, by rw [f.gpr]; exact lr,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (cu.ws.of_upd v₁ (by decide)).of_fupd f
  · rw [mt]; exact cu.modulus
  · rw [mt]; exact cu.inverse
  · rw [z, r11, lr, he, sub_add_add, cmp_ofNat (by omega_arith) (by omega_arith)]
  · rw [mt, Vu, Y₃, B₃]
  · have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_arith
    rw [mt, Ku.val32 (i := 10) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', B₃]
    omega_arith
  · rw [mt]
    exact (Outs.of_outside O₃ (by simp)).trans Ku.streamRanges
  · exact (Ru.trans (v₁.rest (by decide))).trans (f.rest _)

/-! ## The stream -/

/-- The bytes from `r11 = p` to `lr = p + len`, reduced modulo `m` into the
result slot. -/
theorem reduceStream_ok {n size m len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hlen : p.toNat + len ≤ 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : s.gpr .r11 = p) (he : s.gpr .lr = p + BitVec.ofNat 32 len)
    (hr : ∀ i < len, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨off base 0, contextBytes n⟩) :
    WP isa (reduceStream n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) len) % m ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Rest (.r11 :: dclob) s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  obtain b9 := slot_bound (n := n) (i := 9) (by decide)
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain s9 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have n0 := h.n0
  obtain m0 : 0 < m := by omega_arith
  simp only [stride] at b9 b10 s9
  obtain e8 : 4 * (2 * n) = 8 * n := by omega_arith
  unfold reduceStream
  refine WP.seq (WP.mono (zeros_ok h.ws (k := 2 * n) (o := resS n) (by omega_arith) (by simp only [resS]; omega_arith)
    (by simp only [resS]; omega_arith)) fun u₁ ⟨w₁, Z₁, O₁, R₁⟩ => ?_)
  rw [e8] at O₁
  obtain c₁ := h.of_slot w₁ O₁ (by decide)
  refine WP.seq (WP.mono (zeros_ok w₁ (k := 2 * n) (o := prodS n) (by omega_arith) (by simp only [prodS]; omega_arith)
    (by simp only [prodS]; omega_arith)) fun u₂ ⟨w₂, Z₂, O₂, R₂⟩ => ?_)
  rw [e8] at O₂
  obtain c₂ := c₁.of_slot w₂ O₂ (by decide)
  obtain Y₂ : val32 u₂.mem base (slot n 9) (2 * n) = 0 := by
    rw [O₂.val32 (by simp only [prodS]; omega_arith) (by omega_arith)]; exact val32_zeros Z₁
  obtain P₂ : val32 u₂.mem base (slot n 10) (2 * n) = 0 := val32_zeros Z₂
  obtain K₂ : Outs base (streamRanges n) s.mem u₂.mem :=
    (Outs.of_outside O₁ (by simp [resS])).trans (Outs.of_outside O₂ (by simp [prodS]))
  obtain R₂' : Rest (.r11 :: dclob) s u₂ := (R₁.mono (by decide)).trans (R₂.mono (by decide))
  obtain r11 : u₂.gpr .r11 = p := by rw [R₂.gpr .r11 (by decide), R₁.gpr .r11 (by decide), hc]
  obtain lr : u₂.gpr .lr = p + BitVec.ofNat 32 len := by rw [R₂.gpr .lr (by decide), R₁.gpr .lr (by decide), he]
  refine WP.seq (wp_cmp (op2_reg _ _) fun u₃ f₃ z₃ => WP.block_nil ?_)
  obtain c₃ : Context n m base size u₃ := ⟨c₂.ws.of_fupd f₃, c₂.size_le, c₂.small, c₂.n0, by rw [f₃.mem]; exact c₂.modulus,
    c₂.gt_one, by rw [f₃.mem]; exact c₂.inverse⟩
  obtain R₃ : Rest (.r11 :: dclob) s u₃ := R₂'.trans (f₃.rest _)
  obtain K₃ : Outs base (streamRanges n) s.mem u₃.mem := by rw [f₃.mem]; exact K₂
  obtain p0 : p = p + BitVec.ofNat 32 0 := (BitVec.add_zero p).symm
  obtain d0 := sub_add_add p 0 len
  rw [BitVec.add_zero] at d0
  rw [r11, lr, d0, cmp_ofNat (by omega_arith) (by omega_arith)] at z₃
  obtain dec0 : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) 0) % m = 0 := by
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, Spec.Dsa.decodeBE, List.foldl_nil, Nat.zero_mod]
  refine WP.ite (decide (0 = len)) (by rw [eval_eq, z₃]) (fun hz => WP.block_nil ⟨c₃, ?_, K₃, R₃⟩) fun hz => ?_
  · have hz : len = 0 := (of_decide_eq_true hz).symm
    rw [f₃.mem, Y₂, hz, dec0]
  obtain hpos : 0 < len := by have := of_decide_eq_false hz; omega_arith
  obtain inside := streamRanges_inside n
  refine WP.loop (M := isa) (fun k (u : State) => ∃ i, k = len - i ∧ i < len ∧ Context n m base size u ∧
      u.gpr .r11 = p + BitVec.ofNat 32 i ∧ u.gpr .lr = p + BitVec.ofNat 32 len ∧
      val32 u.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) i) % m ∧
      val32 u.mem base (slot n 10) (2 * n) < 2 ^ 32 ∧ Outs base (streamRanges n) s.mem u.mem ∧
      Rest (.r11 :: dclob) s u) ?_ len u₃
    ⟨0, by omega_arith, hpos, c₃, by rw [f₃.gpr, r11]; exact p0, by rw [f₃.gpr, lr], by rw [f₃.mem, Y₂, dec0],
      by rw [f₃.mem, P₂]; decide, K₃, R₃⟩
  rintro k u ⟨i, rfl, hi, cu, r11u, lru, Vu, Pu, Ou, Ru⟩
  refine WP.mono (streamStep_ok cu hm hi hlen hl r11u lru (by rw [Ru.rd, Ru.wr]; exact hr i hi)
    (by rw [Vu]; exact Nat.mod_lt _ m0) Pu) fun t ⟨ct, r11t, lrt, zt, Vt, Pt, Ot, Rt⟩ => ?_
  obtain byte : u.mem (State.addr p + BitVec.ofNat 64 i) = s.mem (State.addr p + BitVec.ofNat 64 i) :=
    VG.Proof.Weierstrass.keep_of_disjoint (Outs.outside Ou inside) hd (by omega_arith) hi (by omega_arith)
  obtain Vt' : val32 t.mem base (slot n 9) (2 * n) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) (i + 1)) % m := by
    rw [Vt, Vu, byte, VG.Proof.Dsa.reduce_prefix_succ]
  by_cases hl : i + 1 = len
  · exact .inl ⟨by rw [eval_ne, zt]; simp [hl], ct, by rw [Vt', hl], Ou.trans Ot, Ru.trans Rt⟩
  · exact .inr ⟨by rw [eval_ne, zt]; simp [hl], len - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ct, r11t,
      by rw [lrt, lru], Vt', Pt, Ou.trans Ot, Ru.trans Rt⟩

/-! ## Slot arithmetic -/

/-- `[resS] = m - amount`. -/
theorem modulusMinus_ok {n size m amount : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ha : amount ≤ m) (hn4 : 8 * n ≤ 4096) :
    WP isa (modulusMinus n amount) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) = m - amount ∧ Outs base (streamRanges n) s.mem t.mem ∧
      Rest dclob s t := by
  have sz := h.size_le
  have sm := h.small
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain s09 := slot_le (n := n) (i := 0) (j := 9) (by decide)
  obtain s9 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have n0 := h.n0
  obtain hm : m < 2 ^ (32 * (2 * n)) := by rw [← h.modulus]; exact val32_lt _ _ _ _
  simp only [stride] at b10 s09 s9
  obtain e8 : 4 * (2 * n) = 8 * n := by omega_arith
  unfold modulusMinus
  refine WP.seq (WP.mono (setConst_ok h.ws (k := 2 * n) (o := prodS n) (x := amount) (by omega_arith)
    (by simp only [prodS]; omega_arith) (by simp only [prodS]; omega_arith) (by omega_arith)) fun u ⟨Vu, Ru, Ou⟩ => ?_)
  rw [e8] at Ou
  obtain cu := h.of_slot (h.ws.of_rest Ru (by decide)) Ou (by decide)
  refine WP.mono (subWords_ok cu.ws (k := 2 * n) (o := resS n) (a := modS n) (b := prodS n) (by omega_arith)
    (by simp only [modS]; omega_arith) (by simp only [prodS]; omega_arith) (by simp only [resS]; omega_arith)
    (by simp only [modS]; omega_arith) (by simp only [prodS]; omega_arith) (by simp only [resS]; omega_arith)
    (by simp only [resS, modS]; omega_arith) (by simp only [resS, prodS]; omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, ?_, ?_, Ru.trans Rt⟩
  · rw [e8] at Ot; exact cu.of_slot (cu.ws.of_rest Rt (by decide)) Ot (by decide)
  · show val32 t.mem base (resS n) (2 * n) = _
    obtain Vu' : val32 u.mem base (slot n 10) (2 * n) = amount := by rw [Nat.mod_eq_of_lt (by omega_arith)] at Vu; exact Vu
    rw [Vt, show modS n = slot n 0 from rfl, cu.modulus, show prodS n = slot n 10 from rfl, Vu', show m + 2 ^ (32 * (2 * n)) - amount = (m - amount) + 2 ^ (32 * (2 * n)) by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [e8] at Ot; exact (Outs.of_outside Ou (by simp [prodS])).trans (Outs.of_outside Ot (by simp [resS]))

/-- `[resS] = [expS] [baseS] mod m`, from `R² mod m` in slot 7. -/
theorem ordinaryMul_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hr2 : val32 s.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m) :
    WP isa (ordinaryMul n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 11) (2 * n) * val32 s.mem base (slot n 8) (2 * n) % m ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Rest dclob s t := by
  obtain nw : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold ordinaryMul
  refine WP.seq (WP.mono (context_mul_ok h (o := 10) (a := 8) (b := 7) (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := h.gt_one; omega_arith))) fun u ⟨cu, Ku, ltu, Vu⟩ => ?_)
  obtain Pu : val32 u.mem base (slot n 10) (2 * n) = val32 s.mem base (slot n 8) (2 * n) * 2 ^ (64 * n) % m :=
    mont_encode h.coprime ltu (by rw [Vu, hr2])
  obtain Eu := Ku.val32 (i := 11) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw
  refine WP.mono (context_mul_ok cu (o := 9) (a := 11) (b := 10) (by decide) (by decide) (by decide) ltu)
    fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ?_, Ku.streamRanges.trans Kt.streamRanges, Ku.rest.trans Kt.rest⟩
  rw [Pu, Eu] at Vt
  rw [← Nat.mod_eq_of_lt ltt, ← Eu]
  rw [Eu]
  exact VG.Proof.Dsa.mont_scale h.coprime Vt

/-- `[resS] = [baseS] + [expS] mod m`. -/
theorem ordinaryAdd_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ha : val32 s.mem base (slot n 8) (2 * n) < m) (hb : val32 s.mem base (slot n 11) (2 * n) < m) :
    WP isa (ordinaryAdd n) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (val32 s.mem base (slot n 8) (2 * n) + val32 s.mem base (slot n 11) (2 * n)) % m :=
  context_add_ok h (o := 9) (a := 8) (b := 11) (by decide) (by decide) (by decide) ha hb

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.Arith`, which only this module used -/

section

/-!
# DSA's reductions and products as functions on 32-bit ARM: their code

`vg_dsa_mulmod_{n}` and `vg_dsa_reduce_{n}` (`Impl/Dsa/Arm/Arith.lean`) save
the registers they use as `vg_dsa_pow_{n}_{e}` does (`save_ok`), set up the
context, run `ordinaryMul` or `reduceStream`, and restore the registers
(`restore_ok`): `mulBody_ok`, `reduceBody_ok`. Their contracts in this file's
terms are `mulK` and `reduceK`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow VG.Impl.Dsa.Arm.Arith
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_str wp_ldr wp_dp op2_reg dpVal)

/-- The registers saved in the header, with `r12` the working space. -/
theorem save_ok {s : State} {base : Addr} {size : Nat} (E : Entry s base size) (hz : 44 ≤ size) :
    WP isa (.block save) s fun t => Ws t base size ∧
      (∀ x ∈ slots, t.mem.readW (off base x.2) 32 = s.gpr x.1) ∧
      Outs base (words slots) s.mem t.mem ∧ Rest [.r12] s t := by
  unfold save
  refine wp_mov (op2_reg s .r0) fun s₁ u₁ => ?_
  have w₁ : Ws s₁ base size := ⟨by rw [u₁.gpr]; exact E.wb, u₁.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (stores_ok slots w₁ (slots_fit hz) slots_apart) fun t ⟨S, O, R⟩ =>
    ⟨w₁.of_rest R (by decide), fun x hx => by rw [S x hx, u₁.other _ (slots_r12 x hx)],
      by rw [← u₁.mem]; exact O, (u₁.rest (by decide)).trans (R.mono (by decide))⟩

/-- The saved registers, from the header. -/
theorem restore_ok {s t : State} {base : Addr} {size : Nat} (hs : Ws t base size) (hz : 44 ≤ size)
    (hv : ∀ x ∈ slots, t.mem.readW (off base x.2) 32 = s.gpr x.1) :
    WP isa (.block restore) t fun u =>
      (∀ r ∈ preserved, u.gpr r = s.gpr r) ∧ Rest preserved t u ∧ u.mem = t.mem := by
  refine WP.mono (loads_ok slots hs (slots_fit hz) slots_r12 slots_nodup) fun u ⟨L, R, M⟩ =>
    ⟨fun r hr => ?_, slots_regs ▸ R, M⟩
  rw [← slots_regs] at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  rw [L x hx, hv x hx]

/-- The saved words, through code that changes only `rs`, apart from them. -/
theorem saved_keep {s t u : State} {base : Addr} {rs : List (Nat × Nat)}
    (hv : ∀ x ∈ slots, t.mem.readW (off base x.2) 32 = s.gpr x.1) (O : Outs base rs t.mem u.mem)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ 8 ∨ 48 ≤ r.1) :
    ∀ x ∈ slots, u.mem.readW (off base x.2) 32 = s.gpr x.1 := fun x hx => by
  have hw := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
  simp only at hw
  rw [outs_readW O (fun r h => by have := hr r h; omega_arith) (by omega_arith), hv x hx]

theorem setup_apart (n : Nat) : ∀ r ∈ Context.callRanges n, r.1 + r.2 ≤ 8 ∨ 48 ≤ r.1 := by
  simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    slot, stride]
  omega_arith

theorem stream_apart (n : Nat) : ∀ r ∈ streamRanges n, r.1 + r.2 ≤ 8 ∨ 48 ≤ r.1 := by
  simp only [streamRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    slot, stride]
  omega_arith

theorem stream_scratch {n : Nat} :
    ∀ r ∈ streamRanges n, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  within_scratch (by
    simp only [streamRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      contextBytes, slot, stride]
    omega_arith)

theorem ctx_of_rest {n m size : Nat} {base : Addr} {rs : List Reg} {s t : State} (h : Context n m base size s)
    (R : Rest rs s t) (h12 : .r12 ∉ rs) (hm : t.mem = s.mem) : Context n m base size t :=
  ⟨h.ws.of_rest R h12, h.size_le, h.small, h.n0, by rw [hm]; exact h.modulus, h.gt_one, by rw [hm]; exact h.inverse⟩

/-! ## Products -/

/-- `a b mod m` into slot 9, for the modulus in slot 0 and `a`, `b` in slots
8 and 11; the registers the calling convention keeps are restored. -/
theorem mulBody_ok {s : State} {base : Addr} {size n m : Nat} (E : Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (mulBody n) s fun t =>
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) * val32 s.mem base (slot n 11) (2 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨c44, c4960⟩ := contextBytes_bounds hn48
  have nw := E.nowrap
  have s0 := slot_bound (n := n) (i := 0) (by decide)
  have s8 := slot_bound (n := n) (i := 8) (by decide)
  have s11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  have h8 := slot_header n 8
  have h11 := slot_header n 11
  simp only [stride] at s0 s8 s11
  unfold mulBody
  refine WP.seq (WP.mono (save_ok E (by omega_arith)) fun s₂ ⟨w₂, S₂, O₂, R₂⟩ => ?_)
  have away : ∀ {d k : Nat}, 48 ≤ d → d + 4 * k ≤ 2 ^ 64 → val32 s₂.mem base d k = val32 s.mem base d k :=
    fun hd hd' => O₂.val32 (fun r hr => .inr (by have := slots_words r hr; omega_arith)) hd'
  have hv₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := by
    rw [away (by omega_arith) (by omega_arith)]; exact hv
  refine WP.seq (WP.mono (Context.call_ok w₂ (by omega_arith) hn hn48 hv₂ hm1 hodd)
    fun s₃ ⟨c₃, _, rr₃, O₃, R₃⟩ => ?_)
  refine WP.seq (WP.mono (ordinaryMul_ok c₃ rr₃) fun s₄ ⟨c₄, V₄, O₄, R₄⟩ => ?_)
  refine WP.mono (restore_ok c₄.ws (by omega_arith) (saved_keep (saved_keep S₂ O₃ (setup_apart n)) O₄ (stream_apart n)))
    fun t ⟨P, R₅, M₅⟩ => ⟨?_, ?_, P, ?_, ?_, ?_⟩
  · have k₃ : ∀ {d k : Nat}, (∀ r ∈ Context.callRanges n, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) → d + 4 * k ≤ 2 ^ 64 →
        val32 s₃.mem base d k = val32 s₂.mem base d k := fun h h' => O₃.val32 h h'
    rw [M₅, V₄,
      k₃ (by simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega_arith) (by omega_arith),
      k₃ (by simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega_arith) (by omega_arith),
      away (by omega_arith) (by omega_arith), away (by omega_arith) (by omega_arith), Nat.mul_comm]
  · rw [M₅]
    exact ((outs_within O₂ (words_scratch n)).trans (outs_within O₃ (setup_scratch hn))).trans
      (outs_within O₄ stream_scratch)
  · rw [R₅.sp, R₄.sp, R₃.sp, R₂.sp]
  · rw [R₅.rd, R₄.rd, R₃.rd, R₂.rd]
  · rw [R₅.wr, R₄.wr, R₃.wr, R₂.wr]

/-! ## Reductions -/

/-- Bytes apart from the context keep their values through code that
changes only ranges within it. -/
theorem bytes_apart {m m' : Mem} {base p : Addr} {len n : Nat} {rs : List (Nat × Nat)}
    (O : Outs base rs m m') (hd : Region.Disjoint ⟨p, len⟩ ⟨base, contextBytes n⟩) (hl : len ≤ 2 ^ 64)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ contextBytes n) (hn48 : n ≤ 48) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len :=
  VG.Proof.Dsa.outs_bytes O hl (fun r h => by have := hr r h; have := contextBytes_bounds hn48; omega_arith)
    fun r h => hd.sub_right (Offset.sub_base base (hr r h))

theorem setup_inside {n : Nat} (hn : 0 < n) : ∀ r ∈ Context.callRanges n, r.1 + r.2 ≤ contextBytes n := by
  simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    contextBytes, slot, stride]
  omega_arith

/-- The saves, then the bytes' address into `r11` and their length into the
header. -/
theorem reduceHead_ok {s : State} {base : Addr} {size : Nat} (E : Entry s base size) (hz : 48 ≤ size) :
    WP isa (.block (save ++ ([.mov .r11 (.reg .r2), .str .r3 .r12 lenAt] : List Instr))) s fun t => Ws t base size ∧
      (∀ x ∈ slots, t.mem.readW (off base x.2) 32 = s.gpr x.1) ∧
      Outs base ((lenAt, 4) :: words slots) s.mem t.mem ∧ Rest [.r11, .r12] s t ∧
      t.gpr .r11 = s.gpr .r2 ∧ t.mem.readW (off base lenAt) 32 = s.gpr .r3 := by
  have nw := E.nowrap
  refine VG.Proof.X25519.Arm.WP.append (save_ok E (by omega_arith)) fun s₁ ⟨w₁, S₁, O₁, R₁⟩ =>
    wp_mov (op2_reg s₁ .r2) fun s₂ u₂ => ?_
  have w₂ := w₁.of_upd u₂ (by decide)
  refine wp_str (by decide) (w₂.ea12 (by simp only [lenAt]; omega_arith)) (w₂.write (by simp only [lenAt]; omega_arith))
    fun t m₃ => WP.block_nil ⟨w₂.of_mupd m₃, fun x hx => ?_, ?_, ?_, ?_, ?_⟩
  · have hw := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
    simp only at hw
    rw [m₃.mem, Mem.readW_writeW_sep (Offset.sep base (.inl (by simp only [lenAt]; omega_arith)) (by omega_arith)
      (by simp only [lenAt]; omega_arith)) (by decide), u₂.mem]
    exact S₁ x hx
  · rw [m₃.mem]
    refine (O₁.mono fun r h => List.mem_cons_of_mem _ h).trans ?_
    rw [u₂.mem]
    exact Outs.of_outside (writeW32_outside _ _ _ (by simp only [lenAt]; omega_arith)) (List.mem_cons_self ..)
  · exact ((R₁.mono (by decide)).trans (u₂.rest (by decide))).trans (m₃.rest _)
  · rw [m₃.gpr, u₂.gpr, R₁.gpr .r2 (by decide)]
  · rw [m₃.mem, Mem.readW_writeW_self32, u₂.other .r3 (by decide), R₁.gpr .r3 (by decide)]

/-- `lr` = the header's length plus `r11`. -/
theorem reduceEnd_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 48 ≤ size) :
    WP isa (.block [.ldr .lr .r12 lenAt, .dp .add .lr .lr (.reg .r11)]) s fun t =>
      t.gpr .lr = s.mem.readW (off base lenAt) 32 + s.gpr .r11 ∧ Rest [.lr] s t ∧ t.mem = s.mem :=
  wp_ldr (by decide) (hs.ea12 (by simp only [lenAt]; omega_arith)) (hs.read (by simp only [lenAt]; omega_arith))
    fun u₁ v₁ => wp_dp (op2_reg _ _) fun t v₂ => WP.block_nil
      ⟨by rw [v₂.gpr, dpVal, v₁.gpr, v₁.other .r11 (by decide)],
        (v₁.rest (by decide)).trans (v₂.rest (by decide)), by rw [v₂.mem, v₁.mem]⟩

theorem len_apart : ∀ r ∈ (lenAt, 4) :: words slots, r.1 + r.2 ≤ 64 := by decide

/-- The `len` bytes at `p`, in `r2` and `r3`, apart from the context, reduced
modulo the modulus in slot 0, into slot 9; the registers the calling
convention keeps are restored. -/
theorem reduceBody_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32} (E : Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm : 255 < m) (hodd : m % 2 = 1)
    (hp : s.gpr .r2 = p) (hl : (s.gpr .r3).toNat = len) (hfit : p.toNat + len ≤ 2 ^ 32)
    (hr : ∀ i < len, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩) :
    WP isa (reduceBody n) s fun t =>
      val32 t.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) len) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨c44, c4960⟩ := contextBytes_bounds hn48
  have c48 : 48 ≤ contextBytes n := by simp only [contextBytes, slot, stride]; omega_arith
  have nw := E.nowrap
  have s0 := slot_bound (n := n) (i := 0) (by decide)
  have h0 := slot_header n 0
  simp only [stride] at s0
  have llt : len < 2 ^ 32 := by rw [← hl]; exact (s.gpr .r3).isLt
  unfold reduceBody
  refine WP.seq (WP.mono (reduceHead_ok E (by omega_arith)) fun s₂ ⟨w₂, S₂, O₂, R₂, P₂, L₂⟩ => ?_)
  have hv₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := by
    rw [O₂.val32 (fun r hr => .inr (by have := len_apart r hr; omega_arith)) (by omega_arith)]; exact hv
  refine WP.seq (WP.mono (Context.light_ok w₂ (by omega_arith) hn hn48 hv₂ (by omega_arith) hodd)
    fun s₃ ⟨c₃, O₃, R₃⟩ => ?_)
  refine WP.seq (WP.mono (reduceEnd_ok c₃.ws (by omega_arith)) fun s₄ ⟨L₄, R₄, M₄⟩ => ?_)
  have c₄ := ctx_of_rest c₃ R₄ (by decide) M₄
  have r11 : s₄.gpr .r11 = p := by rw [R₄.gpr .r11 (by decide), R₃.gpr .r11 (by decide), P₂, hp]
  have lr : s₄.gpr .lr = p + BitVec.ofNat 32 len := by
    rw [L₄, R₃.gpr .r11 (by decide), P₂, hp, outs_readW O₃ (fun r h => by have := setup_apart n r h; simp only [lenAt]; omega_arith)
      (by simp only [lenAt]; omega_arith), L₂, BitVec.add_comm, ← hl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have rw₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by
    rw [R₄.rd, R₄.wr, R₃.rd, R₃.wr, R₂.rd, R₂.wr]
  refine WP.seq (WP.mono (reduceStream_ok c₄ hm hfit llt r11 lr (fun i hi => by rw [rw₄]; exact hr i hi)
    (by rw [show off base 0 = base from BitVec.add_zero _]; exact hd)) fun s₅ ⟨c₅, V₅, O₅, R₅⟩ => ?_)
  have K₄ : Outs base [] s₃.mem s₄.mem := fun x _ => by rw [M₄]
  refine WP.mono (restore_ok c₅.ws (by omega_arith)
    (saved_keep (saved_keep (saved_keep S₂ O₃ (setup_apart n)) K₄ (by simp)) O₅ (stream_apart n)))
    fun t ⟨P, R₆, M₆⟩ => ⟨?_, ?_, P, ?_, ?_, ?_⟩
  · rw [M₆, V₅, M₄, bytes_apart O₃ hd (by omega_arith) (setup_inside hn) hn48,
      bytes_apart O₂ hd (by omega_arith) (fun r h => by have := len_apart r h; omega_arith) hn48]
  · rw [M₆]
    refine ((outs_within O₂ (within_scratch fun r h => .inl (len_apart r h))).trans
      (outs_within O₃ (setup_scratch hn))).trans ?_
    rw [← M₄]
    exact outs_within O₅ stream_scratch
  · rw [R₆.sp, R₅.sp, R₄.sp, R₃.sp, R₂.sp]
  · rw [R₆.rd, R₅.rd, R₄.rd, R₃.rd, R₂.rd]
  · rw [R₆.wr, R₅.wr, R₄.wr, R₃.wr, R₂.wr]

/-! ## The functions -/

/-- `vg_dsa_mulmod_{n}`'s contract in this file's terms, as `powK`. -/
def mulK (n : Nat) : Contract isa where
  pre := (powK n 1).pre
  post s t :=
    let base := State.addr (s.gpr .r0)
    val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) * val32 s.mem base (slot n 11) (2 * n) %
          val32 s.mem base (slot n 0) (2 * n) ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0

theorem mulK_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (h : (mulK n).pre s) :
    ∃ tr t, Exec isa (mulBody n) s tr t ∧ abiPreserved s t ∧ (mulK n).post s t := by
  obtain ⟨-, hwr, hnw, hz, hodd, hm1⟩ := h
  have E : Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    ⟨rfl, ⟨_, Nat.le_refl _, by omega_arith, by rw [hwr]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hnw⟩
  obtain ⟨tr, t, ex, V, O, P, hsp, -, -⟩ := mulBody_ok E hz hn hn48 rfl hm1 hodd
  exact ⟨tr, t, ex, ⟨P, hsp⟩, V, O⟩

theorem mulK_ct (n : Nat) (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (mulK n).pre (mulK n).pub (mulBody n) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ Eq => ?_
  have E : ∀ {s : State}, (mulK n).pre s → Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) := by
    intro s H
    exact ⟨rfl, ⟨_, Nat.le_refl _, by have := H.2.2.1; omega_arith, by rw [H.2.1]; simp⟩,
      by simpa only [VG.Proof.X25519.Arm.addr_toNat] using H.2.2.1⟩
  have E₂ : Entry s₂ (State.addr (s₁.gpr .r0)) ((s₂.gpr .r1).toNat * 8) := by rw [Eq]; exact E h₂
  unfold mulBody
  refine savedSetup_trace (E h₁) E₂ h₁.2.2.2.1 h₂.2.2.2.1 hn hn48
    h₁.2.2.2.2.1 h₁.2.2.2.2.2 ?_ ?_ ?_
  · rw [Eq]; exact h₂.2.2.2.2.1
  · rw [Eq]; exact h₂.2.2.2.2.2
  · refine RelCT.seq (ordinaryMul_relCT n) ?_
    exact (relCT_of_check (σ := VG.Arm.Taint.ofRegs []) (h := .block []) (by decide)).mono (fun _ _ h => h)
      fun _ _ _ => trivial

/-- `vg_dsa_reduce_{n}`'s contract in this file's terms: the working space at
`r0`, of `r1` words, and the `r3` bytes at `r2`, apart from it. -/
def reduceK (n : Nat) : Contract isa where
  pre s :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (slot n 0) (2 * n)
    s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩] ∧ s.wr = [⟨base, (s.gpr .r1).toNat * 8⟩] ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      contextBytes n ≤ (s.gpr .r1).toNat * 8 ∧
      Region.Disjoint ⟨base, (s.gpr .r1).toNat * 8⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ∧
      M % 2 = 1 ∧ 255 < M
  post s t :=
    let base := State.addr (s.gpr .r0)
    val32 t.mem base (slot n 9) (2 * n) =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) %
          val32 s.mem base (slot n 0) (2 * n) ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r2 = t.gpr .r2 ∧ s.gpr .r3 = t.gpr .r3

theorem reduceK_entry {n : Nat} {s : State} (h : (reduceK n).pre s) :
    Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
  ⟨rfl, ⟨_, Nat.le_refl _, by have := h.2.2.1; omega_arith, by rw [h.2.1]; exact List.mem_singleton_self _⟩,
    by rw [VG.Proof.X25519.Arm.addr_toNat]; exact h.2.2.1⟩

theorem reduceK_bytes {n : Nat} {s : State} (h : (reduceK n).pre s) :
    ∀ i < (s.gpr .r3).toNat, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 i) 1 :=
  fun i hi => ⟨_, List.mem_append_left _ (by rw [h.1]; exact List.mem_singleton_self _),
    Offset.contains_base _ (by omega_arith) (by have := h.2.2.2.1; have := (s.gpr .r2).isLt; omega_arith)⟩

theorem reduceK_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (h : (reduceK n).pre s) :
    ∃ tr t, Exec isa (reduceBody n) s tr t ∧ abiPreserved s t ∧ (reduceK n).post s t := by
  have E := reduceK_entry h
  have hb := reduceK_bytes h
  obtain ⟨-, -, -, hfit, hz, hd, hodd, hm⟩ := h
  obtain ⟨tr, t, ex, V, O, P, hsp, -, -⟩ := reduceBody_ok E hz hn hn48 rfl hm hodd rfl rfl hfit
    hb (hd.symm.sub_right (Region.sub_prefix hz))
  exact ⟨tr, t, ex, ⟨P, hsp⟩, V, O⟩

theorem addr_inj {a b : BitVec 32} (h : State.addr a = State.addr b) : a = b :=
  BitVec.eq_of_toNat_eq (by rw [← VG.Proof.X25519.Arm.addr_toNat a, ← VG.Proof.X25519.Arm.addr_toNat b, h])

theorem reduceK_ct (n : Nat) (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (reduceK n).pre (reduceK n).pub (reduceBody n) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ ⟨p0, p2, p3⟩ => ?_
  have E₁ := reduceK_entry h₁
  have E₂ := reduceK_entry h₂
  have hz₁ := h₁.2.2.2.2.1
  have hz₂ := h₂.2.2.2.2.1
  obtain ⟨c44, c4960⟩ := contextBytes_bounds hn48
  have c48 : 48 ≤ contextBytes n := by simp only [contextBytes, slot, stride]; omega_arith
  have s0 := slot_bound (n := n) (i := 0) (by decide)
  have h0 := slot_header n 0
  simp only [stride] at s0
  have pb : State.addr (s₁.gpr .r0) = State.addr (s₂.gpr .r0) := by rw [p0]
  unfold reduceBody
  refine SameTrace.seq (SameTrace.of_relCT (relCT_of_check (τ := VG.Arm.Taint.ofRegs [.r0, .r2, .r3])
      (σ := wsT true false) (h := .block []) (by decide))
      (VG.Arm.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> with_reducible assumption))
    (reduceHead_ok E₁ (by omega_arith)) (reduceHead_ok E₂ (by omega_arith))
    fun u₁ u₂ ⟨w₁, _, O₁, _, P₁, L₁⟩ ⟨w₂, _, O₂, _, P₂, L₂⟩ => ?_
  have mod : ∀ {s u : State} {base : Addr}, Outs base ((lenAt, 4) :: words slots) s.mem u.mem →
      val32 u.mem base (slot n 0) (2 * n) = val32 s.mem base (slot n 0) (2 * n) := fun O =>
    O.val32 (fun r hr => .inr (by have := len_apart r hr; omega_arith)) (by omega_arith)
  have W₂ : Ws u₂ (State.addr (s₁.gpr .r0)) ((s₂.gpr .r1).toNat * 8) := by rw [pb]; exact w₂
  refine SameTrace.seq (Context.light_trace w₁ W₂ (by rw [P₁, P₂, p2]))
    (Context.light_ok w₁ (by omega_arith) hn hn48 (mod O₁) (by have := h₁.2.2.2.2.2.2.2; omega_arith)
      h₁.2.2.2.2.2.2.1)
    (Context.light_ok w₂ (by omega_arith) hn hn48 (mod O₂) (by have := h₂.2.2.2.2.2.2.2; omega_arith)
      h₂.2.2.2.2.2.2.1)
    fun v₁ v₂ ⟨c₁, Q₁, R₁⟩ ⟨c₂, Q₂, R₂⟩ => ?_
  refine SameTrace.seq (SameTrace.of_relCT (relCT_of_check (τ := wsT true false) (σ := wsT true false)
      (h := .block []) (by decide)) (VG.Arm.Taint.agree_ofRegs fun r hr => ?_))
    (reduceEnd_ok c₁.ws (by omega_arith)) (reduceEnd_ok c₂.ws (by omega_arith)) fun x₁ x₂ ⟨L₃, K₁, _⟩ ⟨L₄, K₂, _⟩ => ?_
  · simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact addr_inj (c₁.ws.wb.trans (pb.trans c₂.ws.wb.symm))
    · rw [R₁.gpr .r11 (by decide), R₂.gpr .r11 (by decide), P₁, P₂, p2]
  refine SameTrace.of_relCT (RelCT.seq (reduceStream_relCT n)
    ((relCT_of_check (σ := VG.Arm.Taint.ofRegs []) (h := .block []) (by decide)).mono (fun _ _ h => h)
      fun _ _ _ => trivial)) (VG.Arm.Taint.agree_ofRegs fun r hr => ?_)
  have k : ∀ {s u : State} {base : Addr}, Outs base (Context.callRanges n) s.mem u.mem →
      u.mem.readW (off base lenAt) 32 = s.mem.readW (off base lenAt) 32 := fun O =>
    outs_readW O (fun r h => by have := setup_apart n r h; simp only [lenAt]; omega_arith) (by simp only [lenAt]; omega_arith)
  simp only [wsRegs, ↓reduceIte, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [K₁.gpr .r12 (by decide), K₂.gpr .r12 (by decide)]
    exact addr_inj (c₁.ws.wb.trans (pb.trans c₂.ws.wb.symm))
  · rw [K₁.gpr .r11 (by decide), K₂.gpr .r11 (by decide), R₁.gpr .r11 (by decide), R₂.gpr .r11 (by decide),
      P₁, P₂, p2]
  · rw [L₃, L₄, R₁.gpr .r11 (by decide), R₂.gpr .r11 (by decide), P₁, P₂, p2, k Q₁, k Q₂, L₁, L₂, p3]

end VG.Proof.Dsa.Arm.Pow

end

end


/-!
# DSA's reductions and products as functions on 32-bit ARM: their calls

Calls of `vg_dsa_mulmod_{n}` and `vg_dsa_reduce_{n}` from code whose working
space is at `r12`, as `PowCall.lean` for `vg_dsa_pow_{n}_{e}`: the context's
bytes are the function's working space, which its contract narrows the call
to, with the reduction's bytes, and `r12` comes back from `r11`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Pow VG.Impl.Dsa.Arm.Arith
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_dp wp_movw op2_reg dpVal)

theorem mulBody_noFrames (n : Nat) : (mulBody n).noFrames = true := by
  simp only [mulBody, Impl.Dsa.Arm.Context.call, Impl.Dsa.Arm.Context.body, contextSetup, ordinaryMul, Dynamic.mul, rowD, digitRowD, mulRowD, csubD, Dynamic.zeros,
    ptrLoop, one, powerTwo, addD, addDigits, Code.noFrames, Bool.and_self]

theorem doubles_noCalls (n k : Nat) : (doubles n k).noCalls = true := by
  unfold doubles
  split <;> simp only [countedDouble, addDigits, csubD, ptrLoop, Code.noCalls, Bool.and_self]

theorem reduceBody_noFrames (n : Nat) : (reduceBody n).noFrames = true := by
  simp only [reduceBody, Impl.Dsa.Arm.Context.light, reduceStream, streamStep, reduceStep, addD, addDigits,
    csubD, Dynamic.zeros, ptrLoop, Code.noFrames, Bool.and_self, Bool.and_true, Bool.true_and]
  exact Code.noFrames_of_noCalls (doubles_noCalls n 8)

/-! ## Products -/

theorem mulCall_ok {s : State} {base : Addr} {size n m : Nat} (hs : Ws s base size) (hz : contextBytes n ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m)
    (hodd : m % 2 = 1) :
    WP isa (mulCall n) s fun t => Ws t base size ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) * val32 s.mem base (slot n 11) (2 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r11, .lr] s t := by
  unfold mulCall
  refine WP.seq (WP.mono (head_ok n) fun u ⟨h11, h0, h1, R₁, M₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.callCalls (k := mulK n) (mulK_correct hn hn48)
    (entry_pre (e := 1) hs hz hn48 h0 h1 M₁ (by rw [hv]; exact hodd) (by rw [hv]; exact hm1))
    (Covers.right (covers_ctx w₁ hz)) (covers_ctx w₁ hz) (fun v hrd hwr hsp _ P _ post => ?_) (mulBody_noFrames n))
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  simp only [mulK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, b0, M₁, hv] at post
  obtain ⟨V, O⟩ := post
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h11]
  refine wp_mov (op2_reg v .r11) fun t v₂ => WP.block_nil ⟨⟨?_, ?_, hs.nowrap⟩, ?_, ?_, ?_⟩
  · rw [v₂.gpr, v11, hs.wb]
  · rw [v₂.wr, hwr]; exact w₁.wr
  · rw [v₂.mem]; exact V
  · rw [v₂.mem]; exact O
  · refine ⟨fun r hr => ?_, by rw [v₂.rd, hrd, R₁.rd], by rw [v₂.wr, hwr, R₁.wr], by rw [v₂.sp, hsp, R₁.sp]⟩
    by_cases h12 : r = .r12
    · subst h12; rw [v₂.gpr, v11]
    · rw [v₂.other _ h12]
      have hp : r ∈ preserved ∧ r ≠ .lr ∧ r ∉ [.r0, .r1, .r11] := by revert hr h12; cases r <;> decide
      rw [P _ hp.1 hp.2.1, R₁.gpr _ hp.2.2]

theorem mulCall_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n : Nat} (hs₁ : Ws s₁ base size₁)
    (hs₂ : Ws s₂ base size₂) (hz₁ : contextBytes n ≤ size₁) (hz₂ : contextBytes n ≤ size₂)
    (hn : 0 < n) (hn48 : n ≤ 48)
    (ho₁ : val32 s₁.mem base (slot n 0) (2 * n) % 2 = 1) (hm₁ : 1 < val32 s₁.mem base (slot n 0) (2 * n))
    (ho₂ : val32 s₂.mem base (slot n 0) (2 * n) % 2 = 1) (hm₂ : 1 < val32 s₂.mem base (slot n 0) (2 * n)) :
    SameTrace isa (mulCall n) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs []) a b :=
    fun _ _ => VG.Arm.Taint.agree_ofRegs fun _ h => nomatch h
  unfold mulCall head
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := VG.Arm.Taint.ofRegs [])
      (σ := VG.Arm.Taint.ofRegs []) (c₀ := .block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _)) (head_ok n) (head_ok n)
    fun u₁ u₂ ⟨_, h0₁, h1₁, R₁, M₁⟩ ⟨_, h0₂, h1₂, R₂, M₂⟩ => ?_
  have w₁ := hs₁.of_rest R₁ (by decide)
  have w₂ := hs₂.of_rest R₂ (by decide)
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (mulK_correct hn hn48) (mulK_ct n hn hn48) [] [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := VG.Arm.Taint.ofRegs []) (σ := VG.Arm.Taint.ofRegs []) (h := .block [])
      (by decide)).mono (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨entry_pre (e := 1) hs₁ hz₁ hn48 h0₁ h1₁ M₁ ho₁ hm₁, entry_pre (e := 1) hs₂ hz₂ hn48 h0₂ h1₂ M₂ ho₂ hm₂,
    ?_, Covers.right (covers_ctx w₁ hz₁), covers_ctx w₁ hz₁, Covers.right (covers_ctx w₂ hz₂), covers_ctx w₂ hz₂⟩
  simp only [mulK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h0₁, h0₂]
  exact BitVec.eq_of_toNat_eq (by rw [hs₁.wb_toNat, hs₂.wb_toNat])

/-! ## Reductions -/

/-- The bytes' address and length. -/
theorem rpre_ok {s : State} :
    WP isa (.block [.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11)]) s fun u =>
      u.gpr .r2 = s.gpr .r11 ∧ u.gpr .r3 = s.gpr .lr - s.gpr .r11 ∧ Rest [.r2, .r3] s u ∧ u.mem = s.mem :=
  wp_mov (op2_reg s .r11) fun u₁ v₁ => wp_dp (op2_reg _ _) fun u₂ v₂ => WP.block_nil
    ⟨by rw [v₂.other _ (by decide), v₁.gpr], by rw [v₂.gpr, dpVal, v₁.other _ (by decide), v₁.other _ (by decide)],
      (v₁.rest (by decide)).trans (v₂.rest (by decide)), by rw [v₂.mem, v₁.mem]⟩

/-- The bytes' address and length, then the arguments. -/
theorem rhead_ok {s : State} (n : Nat) :
    WP isa (.block (([.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11)] : List Instr) ++ head n)) s fun u =>
      u.gpr .r2 = s.gpr .r11 ∧ u.gpr .r3 = s.gpr .lr - s.gpr .r11 ∧ u.gpr .r11 = s.gpr .r12 ∧
        u.gpr .r0 = s.gpr .r12 ∧ u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32 ∧
        Rest [.r0, .r1, .r2, .r3, .r11] s u ∧ u.mem = s.mem :=
  VG.Proof.X25519.Arm.WP.append rpre_ok fun u ⟨h2, h3, R, M⟩ => WP.mono (head_ok n) fun t ⟨h11, h0, h1, R', M'⟩ =>
    ⟨by rw [R'.gpr _ (by decide), h2], by rw [R'.gpr _ (by decide), h3],
      by rw [h11, R.gpr _ (by decide)], by rw [h0, R.gpr _ (by decide)], h1,
      (R.mono (by decide)).trans (R'.mono (by decide)), M'.trans M⟩

/-- On entry to the function, its precondition, narrowed to the context and
the bytes. -/
theorem rentry_pre {s u : State} {base : Addr} {size n len : Nat} {p : BitVec 32} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn48 : n ≤ 48) (h0 : u.gpr .r0 = s.gpr .r12)
    (h1 : u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32) (h2 : u.gpr .r2 = p)
    (h3 : (u.gpr .r3).toNat = len) (hfit : p.toNat + len ≤ 2 ^ 32)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩)
    (hm : u.mem = s.mem) (hodd : val32 s.mem base (slot n 0) (2 * n) % 2 = 1)
    (hm255 : 255 < val32 s.mem base (slot n 0) (2 * n)) :
    (reduceK n).pre (u.callEntry.withRegions [⟨State.addr p, len⟩] [⟨base, contextBytes n⟩]) := by
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by
    rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have l1 : (u.callEntry.gpr .r1).toNat * 8 = contextBytes n := by
    rw [State.callEntry_gpr _ (by decide), h1]; exact words_eq hn48
  have e2 : u.callEntry.gpr .r2 = p := by rw [State.callEntry_gpr _ (by decide), h2]
  have e3 : (u.callEntry.gpr .r3).toNat = len := by rw [State.callEntry_gpr _ (by decide), h3]
  simp only [reduceK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, b0, l1, e2, e3, hm]
  refine ⟨trivial, trivial, ?_, hfit, Nat.le_refl _, hd.symm, hodd, hm255⟩
  rw [State.callEntry_gpr _ (by decide), h0, hs.wb_toNat]
  have := hs.nowrap
  omega_using [hz, this]

theorem reduceCall_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) (hv : val32 s.mem base (slot n 0) (2 * n) = m)
    (hm : 255 < m) (hodd : m % 2 = 1) (h11 : s.gpr .r11 = p) (hlr : s.gpr .lr = p + BitVec.ofNat 32 len)
    (hfit : p.toNat + len ≤ 2 ^ 32) (llt : len < 2 ^ 32) (hr : InRegions (s.rd ++ s.wr) (State.addr p) len)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩) :
    WP isa (reduceCall n) s fun t => Ws t base size ∧
      val32 t.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) len) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .r11, .lr] s t := by
  have l3 : (s.gpr .lr - s.gpr .r11).toNat = len := by
    rw [hlr, h11, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt llt]
  unfold reduceCall
  refine WP.seq (WP.mono (rhead_ok n) fun u ⟨h2, h3, h11', h0, h1, R₁, M₁⟩ => ?_)
  have w₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.callCalls (k := reduceK n) (reduceK_correct hn hn48)
    (rentry_pre hs hz hn48 h0 h1 (h2.trans h11) (by rw [h3, l3]) hfit hd M₁ (by rw [hv]; exact hodd)
      (by rw [hv]; exact hm))
    (Covers.append_left (Covers.one (by rw [R₁.rd, R₁.wr]; exact hr)) (Covers.right (covers_ctx w₁ hz)))
    (covers_ctx w₁ hz) (fun v hrd hwr hsp _ P _ post => ?_) (reduceBody_noFrames n))
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have e2 : u.callEntry.gpr .r2 = p := by rw [State.callEntry_gpr _ (by decide), h2, h11]
  have e3 : (u.callEntry.gpr .r3).toNat = len := by rw [State.callEntry_gpr _ (by decide), h3, l3]
  simp only [reduceK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, b0, e2, e3, M₁, hv]
    at post
  obtain ⟨V, O⟩ := post
  have v11 : v.gpr .r11 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h11']
  refine wp_mov (op2_reg v .r11) fun t v₂ => WP.block_nil ⟨⟨?_, ?_, hs.nowrap⟩, ?_, ?_, ?_⟩
  · rw [v₂.gpr, v11, hs.wb]
  · rw [v₂.wr, hwr]; exact w₁.wr
  · rw [v₂.mem]; exact V
  · rw [v₂.mem]; exact O
  · refine ⟨fun r hr => ?_, by rw [v₂.rd, hrd, R₁.rd], by rw [v₂.wr, hwr, R₁.wr], by rw [v₂.sp, hsp, R₁.sp]⟩
    by_cases h12 : r = .r12
    · subst h12; rw [v₂.gpr, v11]
    · rw [v₂.other _ h12]
      have hp : r ∈ preserved ∧ r ≠ .lr ∧ r ∉ [.r0, .r1, .r2, .r3, .r11] := by
        revert hr h12; cases r <;> decide
      rw [P _ hp.1 hp.2.1, R₁.gpr _ hp.2.2]

theorem reduceCall_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n len : Nat} {p : BitVec 32}
    (hs₁ : Ws s₁ base size₁) (hs₂ : Ws s₂ base size₂) (hz₁ : contextBytes n ≤ size₁)
    (hz₂ : contextBytes n ≤ size₂) (hn : 0 < n) (hn48 : n ≤ 48)
    (ho₁ : val32 s₁.mem base (slot n 0) (2 * n) % 2 = 1) (hm₁ : 255 < val32 s₁.mem base (slot n 0) (2 * n))
    (ho₂ : val32 s₂.mem base (slot n 0) (2 * n) % 2 = 1) (hm₂ : 255 < val32 s₂.mem base (slot n 0) (2 * n))
    (a₁ : s₁.gpr .r11 = p) (l₁ : s₁.gpr .lr = p + BitVec.ofNat 32 len)
    (a₂ : s₂.gpr .r11 = p) (l₂ : s₂.gpr .lr = p + BitVec.ofNat 32 len)
    (hfit : p.toNat + len ≤ 2 ^ 32) (llt : len < 2 ^ 32) (hr₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr p) len)
    (hr₂ : InRegions (s₂.rd ++ s₂.wr) (State.addr p) len)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨base, contextBytes n⟩) :
    SameTrace isa (reduceCall n) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (VG.Arm.Taint.ofRegs []) a b :=
    fun _ _ => VG.Arm.Taint.agree_ofRegs fun _ h => nomatch h
  have l3 : ∀ {s : State}, s.gpr .r11 = p → s.gpr .lr = p + BitVec.ofNat 32 len →
      (s.gpr .lr - s.gpr .r11).toNat = len := fun h11 hlr => by
    rw [hlr, h11, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt llt]
  unfold reduceCall head
  refine SameTrace.seq (SameTrace.of_relCT (erased_relCT (τ := VG.Arm.Taint.ofRegs [])
      (σ := VG.Arm.Taint.ofRegs [])
      (c₀ := .block [.mov .r2 (.reg .r11), .dp .sub .r3 .lr (.reg .r11), .mov .r11 (.reg .r12),
        .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _)) (rhead_ok n) (rhead_ok n)
    fun u₁ u₂ ⟨h2₁, h3₁, _, h0₁, h1₁, R₁, M₁⟩ ⟨h2₂, h3₂, _, h0₂, h1₂, R₂, M₂⟩ => ?_
  have w₁ := hs₁.of_rest R₁ (by decide)
  have w₂ := hs₂.of_rest R₂ (by decide)
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (reduceK_correct hn hn48) (reduceK_ct n hn hn48) [⟨State.addr p, len⟩]
      [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := VG.Arm.Taint.ofRegs []) (σ := VG.Arm.Taint.ofRegs []) (h := .block [])
      (by decide)).mono (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨rentry_pre hs₁ hz₁ hn48 h0₁ h1₁ (h2₁.trans a₁) (by rw [h3₁, l3 a₁ l₁]) hfit hd M₁ ho₁ hm₁,
    rentry_pre hs₂ hz₂ hn48 h0₂ h1₂ (h2₂.trans a₂) (by rw [h3₂, l3 a₂ l₂]) hfit hd M₂ ho₂ hm₂, ?_,
    Covers.append_left (Covers.one (by rw [R₁.rd, R₁.wr]; exact hr₁)) (Covers.right (covers_ctx w₁ hz₁)),
    covers_ctx w₁ hz₁,
    Covers.append_left (Covers.one (by rw [R₂.rd, R₂.wr]; exact hr₂)) (Covers.right (covers_ctx w₂ hz₂)),
    covers_ctx w₂ hz₂⟩
  simp only [reduceK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide),
    h0₁, h0₂, h2₁, h2₂, h3₁, h3₂, a₁, a₂, l₁, l₂]
  exact ⟨BitVec.eq_of_toNat_eq (by rw [hs₁.wb_toNat, hs₂.wb_toNat]), rfl, rfl⟩

end VG.Proof.Dsa.Arm.Pow
