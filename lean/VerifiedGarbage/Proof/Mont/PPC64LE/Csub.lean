module

import VerifiedGarbage.Proof.Mont.PPC64LE.Row
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Montgomery arithmetic on PPC64LE: the conditional subtraction

`csub M src` reduces the number below `2m` at `[r3 + src]` (`D` digits and
a top digit) modulo `m` into `[r4]`: the digits of its difference with `m`
go to `[M.tmp]` (`diffs_ok`), the carry out plus the top digit is 1 exactly
when the number is at least `m`, and its negation selects the difference or
the number, a 64-bit word at a time (`sels_ok`, `csub_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- `2³² - 1`. -/
abbrev M32 : BitVec 64 := BitVec.ofNat 64 (2 ^ 32 - 1)

theorem mask32_ok {s : State} {is : List Instr} {Q : State → Prop}
    (k : WP isa (.block is) (s.write .r0 M32) Q) : WP isa (.block (mask32 ++ is)) s Q := by
  simp only [mask32, List.cons_append, List.nil_append]
  refine wp_step (exec_li (by decide)) (wp_step exec_ori (wp_step exec_oris ?_))
  rw [write_write, write_write]
  simp only [write_gpr, ite_true]
  rw [show (0#64 ||| BitVec.setWidth 64 (65535 : BitVec 16) |||
    BitVec.setWidth 64 (65535 : BitVec 16) <<< 16) = M32 by decide]
  exact k

/-- Digit `j` of `[r3 + src] - m`, from the carry `r10`, stored at
`[r3 + M.tmp + 4j]`, its carry to `r10`. -/
theorem diffDigit_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src j : Nat}
    (h3 : At s base .r3 0) (h0 : s.gpr .r0 = M32) (hc : (s.gpr .r10).toNat < 2 ^ 32)
    (hsrc : src + 4 * j + 4 ≤ size) (hmo : M.mo + 4 * j + 4 ≤ size) (htmp : M.tmp + 4 * j + 4 ≤ size) :
    WP isa (.block (diffDigit M src j)) s fun u =>
      u.mem = s.mem.writeW (off base (M.tmp + 4 * j)) (BitVec.ofNat 32
        (w32 s.mem base (src + 4 * j) + (2 ^ 32 - 1 - w32 s.mem base (M.mo + 4 * j)) + (s.gpr .r10).toNat)) ∧
      (u.gpr .r10).toNat = (w32 s.mem base (src + 4 * j) + (2 ^ 32 - 1 - w32 s.mem base (M.mo + 4 * j)) +
        (s.gpr .r10).toNat) / 2 ^ 32 ∧
      Kp [.r10, .r11, .r12] s u := by
  have t0 := w32_lt s.mem base (src + 4 * j)
  have t1 := w32_lt s.mem base (M.mo + 4 * j)
  simp only [diffDigit]
  refine wp_step (lwz0_ok hs h3 (by decide) hsrc) ?_
  refine wp_step (lwz0_ok (hs.write _ _) (h3.write _) (by decide) hmo) ?_
  refine wp_step exec_add ?_
  refine wp_step exec_sub ?_
  refine wp_step exec_add ?_
  refine wp_step (stw0_ok ((((hs.write _ _).write _ _).write _ _).write _ _ |>.write _ _)
    (((((h3.write _).write _).write _).write _).write _) (by decide) htmp) ?_
  refine wp_step (exec_lsr_d (by decide)) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true, h0]
  have e : (BitVec.ofNat 64 (w32 s.mem base (src + 4 * j)) + M32 - BitVec.ofNat 64 (w32 s.mem base (M.mo + 4 * j)) +
      s.gpr .r10).toNat = w32 s.mem base (src + 4 * j) + (2 ^ 32 - 1 - w32 s.mem base (M.mo + 4 * j)) +
        (s.gpr .r10).toNat := by
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_add, toNat_ofNat_lt (by omega),
      toNat_ofNat_lt (by omega), show M32.toNat = 2 ^ 32 - 1 from rfl]
    omega
  refine ⟨by rw [e], by rw [BitVec.toNat_ushiftRight, e, Nat.shiftRight_eq_div_pow], ?_⟩
  exact ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, hr.1, hr.2.1, hr.2.2, ite_false], rfl, rfl, rfl, rfl⟩

/-- The first `k` digits of the difference. -/
def diffs (M : Mod) (src k : Nat) : List Instr := (List.range k).flatMap (diffDigit M src)

theorem diffs_succ (M : Mod) (src k : Nat) : diffs M src (k + 1) = diffs M src k ++ diffDigit M src k := by
  simp only [diffs, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` digits of `[src] + 2^(32 k) - m`, from the carry `r10 = 1`, to
`[M.tmp]`, the carry to `r10`. -/
theorem diffs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src W : Nat}
    (h3 : At s base .r3 0) (h0 : s.gpr .r0 = M32) (hc : (s.gpr .r10).toNat = 1)
    (hsrc : src + 4 * W ≤ size) (hmo : M.mo + 4 * W ≤ size) (htmp : M.tmp + 4 * W ≤ size)
    (hs1 : src + 4 * W ≤ M.tmp ∨ M.tmp + 4 * W ≤ src) (hs2 : M.mo + 4 * W ≤ M.tmp ∨ M.tmp + 4 * W ≤ M.mo) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block (diffs M src k)) s fun u =>
      Outside base M.tmp (4 * k) s.mem u.mem ∧
      val32 u.mem base M.tmp k + 2 ^ (32 * k) * (u.gpr .r10).toNat + val32 s.mem base M.mo k =
        val32 s.mem base src k + 2 ^ (32 * k) ∧
      (u.gpr .r10).toNat ≤ 1 ∧ Kp [.r10, .r11, .r12] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [val32, hc], by omega, Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [diffs_succ]
    refine wp_append (WP.mono (diffs_ok hs h3 h0 hc hsrc hmo htmp hs1 hs2 (k := k) (by omega))
      fun s₁ ⟨O₁, V₁, C₁, K₁⟩ => ?_)
    refine WP.mono (diffDigit_ok (K₁.ws hs) (K₁.at h3) (by rw [K₁.g]; exact h0) (by omega) (j := k)
      (by omega) (by omega) (by omega)) fun u ⟨m₂, c₂, K₂⟩ => ?_
    have tk : w32 s₁.mem base (src + 4 * k) = w32 s.mem base (src + 4 * k) := O₁.w32 (by omega) (by omega)
    have mk : w32 s₁.mem base (M.mo + 4 * k) = w32 s.mem base (M.mo + 4 * k) := O₁.w32 (by omega) (by omega)
    rw [tk, mk] at m₂ c₂
    have W := writeW32_outside s₁.mem base (d := M.tmp + 4 * k)
      (BitVec.ofNat 32 (w32 s.mem base (src + 4 * k) + (2 ^ 32 - 1 - w32 s.mem base (M.mo + 4 * k)) +
        (s₁.gpr .r10).toNat)) (by omega)
    rw [← m₂] at W
    have hlow : val32 u.mem base M.tmp k = val32 s₁.mem base M.tmp k := W.val32 (by omega) (by omega)
    have htop : w32 u.mem base (M.tmp + 4 * k) = (w32 s.mem base (src + 4 * k) +
        (2 ^ 32 - 1 - w32 s.mem base (M.mo + 4 * k)) + (s₁.gpr .r10).toNat) % 2 ^ 32 := by
      rw [m₂, w32_write_self, BitVec.toNat_ofNat]
    have t0 := w32_lt s.mem base (src + 4 * k)
    have t1 := w32_lt s.mem base (M.mo + 4 * k)
    have hv : val32 u.mem base M.tmp (k + 1) + 2 ^ (32 * (k + 1)) * (u.gpr .r10).toNat +
        val32 s.mem base M.mo (k + 1) = val32 s.mem base src (k + 1) + 2 ^ (32 * (k + 1)) := by
      rw [val32_succ, val32_succ, val32_succ, hlow, htop, c₂, pow32_succ]
      generalize hxd : w32 s.mem base (src + 4 * k) + (2 ^ 32 - 1 - w32 s.mem base (M.mo + 4 * k)) +
        (s₁.gpr .r10).toNat = x at *
      have hx' := Nat.div_add_mod x (2 ^ 32)
      generalize 2 ^ (32 * k) = P at *
      have : x + w32 s.mem base (M.mo + 4 * k) = w32 s.mem base (src + 4 * k) + 2 ^ 32 - 1 + (s₁.gpr .r10).toNat := by
        omega
      grind
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), hv, ?_, K₁.trans K₂⟩
    have := val32_lt u.mem base M.tmp (k + 1)
    have := val32_lt s.mem base src (k + 1)
    have hP : 0 < 2 ^ (32 * (k + 1)) := Nat.two_pow_pos _
    by_contra hc2
    have : 2 ^ (32 * (k + 1)) * 2 ≤ 2 ^ (32 * (k + 1)) * (u.gpr .r10).toNat := Nat.mul_le_mul_left _ (by omega)
    omega

/-! ## The selection -/

/-- `x` where the mask is zero, `y` where it is all ones. -/
theorem sel_mask (x y : BitVec 64) {mk : BitVec 64} (h : mk = 0 ∨ mk = BitVec.allOnes 64) :
    x ^^^ ((y ^^^ x) &&& mk) = if mk = 0 then x else y := by
  rcases h with rfl | rfl
  · simp
  · have : BitVec.allOnes 64 ≠ 0 := by decide
    simp only [this, ite_false, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm x y, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Word `k` of `[src]`, or of `[tmp]` where the mask `r10` is all ones, to
`[r4 + 8k]`. -/
theorem selWord_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src O k : Nat}
    (h3 : At s base .r3 0) (h4 : At s base .r4 O) (hsrc4 : src % 4 = 0) (htmp4 : M.tmp % 4 = 0)
    (hsrc : src + 8 * k + 8 ≤ size) (htmp : M.tmp + 8 * k + 8 ≤ size) (hO : O + 8 * k + 8 ≤ size) :
    WP isa (.block (selWord M src k)) s fun u =>
      u.mem = s.mem.writeW (off base (O + 8 * k)) (word s.mem base (src + 8 * k) ^^^
        ((word s.mem base (M.tmp + 8 * k) ^^^ word s.mem base (src + 8 * k)) &&& s.gpr .r10)) ∧
      Kp [.r11, .r12] s u := by
  simp only [selWord]
  refine wp_step (ld0_ok hs h3 (by decide) (by omega) hsrc) ?_
  refine wp_step (ld0_ok (hs.write _ _) (h3.write _) (by decide) (by omega) htmp) ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_logic ?_
  refine wp_step (std_ok ((((hs.write _ _).write _ _).write _ _).write _ _ |>.write _ _)
    (((((h4.write _).write _).write _).write _).write _) (by decide) (by omega) (d := 8 * k) hO) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [write_gpr, hr.1, hr.2, ite_false]

/-- The selections of the low `k` words. -/
def sels (M : Mod) (src k : Nat) : List Instr := (List.range k).flatMap (selWord M src)

theorem sels_succ (M : Mod) (src k : Nat) : sels M src (k + 1) = sels M src k ++ selWord M src k := by
  simp only [sels, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `[src]`, or of `[tmp]` where the mask `r10` is all
ones, to `[r4]` (apart from both). -/
theorem sels_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src O W : Nat}
    (h3 : At s base .r3 0) (h4 : At s base .r4 O) (hsrc4 : src % 4 = 0) (htmp4 : M.tmp % 4 = 0)
    (hmk : s.gpr .r10 = 0 ∨ s.gpr .r10 = BitVec.allOnes 64)
    (hsrc : src + 8 * W ≤ size) (htmp : M.tmp + 8 * W ≤ size) (hO : O + 8 * W ≤ size)
    (hs1 : src + 8 * W ≤ O ∨ O + 8 * W ≤ src) (hs2 : M.tmp + 8 * W ≤ O ∨ O + 8 * W ≤ M.tmp) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block (sels M src k)) s fun u =>
      Outside base O (8 * k) s.mem u.mem ∧
      wordsVal u.mem base O k = (if s.gpr .r10 = 0 then wordsVal s.mem base src k else wordsVal s.mem base M.tmp k) ∧
      Kp [.r11, .r12] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp [wordsVal], Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [sels_succ]
    refine wp_append (WP.mono (sels_ok hs h3 h4 hsrc4 htmp4 hmk hsrc htmp hO hs1 hs2 (k := k) (by omega))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    refine WP.mono (selWord_ok (K₁.ws hs) (K₁.at h3) (K₁.at h4) hsrc4 htmp4 (k := k) (by omega) (by omega)
      (by omega)) fun u ⟨m₂, K₂⟩ => ?_
    rw [O₁.word (by omega) (by omega), O₁.word (by omega) (by omega), K₁.g, sel_mask _ _ hmk] at m₂
    have W := writeW_outside s₁.mem base (d := O + 8 * k)
      (if s.gpr .r10 = 0 then word s.mem base (src + 8 * k) else word s.mem base (M.tmp + 8 * k)) (by omega)
    rw [← m₂] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega)).trans (W.mono (by omega) (by omega)), ?_, K₁.trans K₂⟩
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_succ_top, W.wordsVal (by omega) (by omega), V₁, m₂,
      word_writeW_self]
    split <;> rfl

/-! ## The reduction -/

/-- What `csub` computes: the number `N = L + R top < 2m` modulo `m`, given its
difference with `m`, `T + R c + m = L + R`. -/
theorem csub_math {L T R m c top : Nat} (hm : m < R) (hN : L + R * top < 2 * m)
    (hT : T < R) (he : T + R * c + m = L + R) (hc : c ≤ 1) :
    c + top ≤ 1 ∧ (if c + top = 0 then L else T) = (L + R * top) % m := by
  have htop : top ≤ 1 := by
    by_contra h
    have : R * 2 ≤ R * top := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain rfl | rfl : top = 0 ∨ top = 1 := by omega
  · obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
    · simp only [Nat.mul_zero, Nat.add_zero, ite_true] at he hN ⊢
      exact ⟨by omega, (Nat.mod_eq_of_lt (by omega)).symm⟩
    · simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at he hN ⊢
      refine ⟨by omega, ?_⟩
      rw [show (if (1 : Nat) = 0 then L else T) = T from rfl, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
    · simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add] at he hN ⊢
      refine ⟨by omega, ?_⟩
      rw [show (if (1 : Nat) = 0 then L else T) = T from rfl, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [Nat.mul_one] at he hN
      omega

theorem neg_mask {x : Nat} (hx : x ≤ 1) :
    BitVec.ofNat 64 0 - BitVec.ofNat 64 x = 0 ∨ BitVec.ofNat 64 0 - BitVec.ofNat 64 x = BitVec.allOnes 64 := by
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
  · exact .inl (by decide)
  · exact .inr (by decide)

theorem neg_mask_zero {x : Nat} (hx : x ≤ 1) : (BitVec.ofNat 64 0 - BitVec.ofNat 64 x = 0) ↔ x = 0 := by
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
  · decide
  · decide

/-- What `csub` needs of the layout: the number (`D + 1` digits at `src`),
the difference (`D` at `M.tmp`), the modulus (`D` at `M.mo`) and the result
(`n` words at `O`, `D = 2n`). -/
structure CsubLay (M : Mod) (size src O : Nat) : Prop where
  src_le : src + 4 * (2 * M.n + 1) ≤ size
  tmp_le : M.tmp + 8 * M.n ≤ size
  mo_le : M.mo + 8 * M.n ≤ size
  o_le : O + 8 * M.n ≤ size
  src4 : src % 4 = 0
  tmp4 : M.tmp % 4 = 0
  s1 : src + 4 * (2 * M.n + 1) ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ src
  s2 : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo
  s3 : src + 8 * M.n ≤ O ∨ O + 8 * M.n ≤ src
  s4 : M.tmp + 8 * M.n ≤ O ∨ O + 8 * M.n ≤ M.tmp

/-- `[r4] = [r3 + src] mod m`, for a number below `2m` (`D` digits and a top
digit). -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src O m : Nat}
    (h3 : At s base .r3 0) (h4 : At s base .r4 O) (hL : CsubLay M size src O)
    (hm : val32 s.mem base M.mo (2 * M.n) = m) (hN : val32 s.mem base src (2 * M.n + 1) < 2 * m) :
    WP isa (.block (csub M src)) s fun u =>
      wordsVal u.mem base O M.n = val32 s.mem base src (2 * M.n + 1) % m ∧
      Outs base [(M.tmp, 8 * M.n), (O, 8 * M.n)] s.mem u.mem ∧
      Kp [.r0, .r10, .r11, .r12] s u := by
  obtain ⟨src_le, tmp_le, mo_le, o_le, src4, tmp4, s1, s2, s3, s4⟩ := hL
  have hn := hs.nowrap
  have hs15 := hs.small
  have ec : csub M src = mask32 ++ (.li .r10 1 :: (diffs M src (2 * M.n) ++
      ([.load .w .r11 wb (src + 4 * (2 * M.n)), .add .r10 .r10 .r11, .li .r11 0, .sub .r10 .r11 .r10] ++
        sels M src M.n))) := by
    simp only [csub, digits, diffs, sels, List.append_assoc, List.cons_append, List.nil_append]
  rw [ec]
  refine mask32_ok ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_append (WP.mono (diffs_ok (W := 2 * M.n) ((hs.write _ _).write _ _) ((h3.write _).write _)
    (by simp only [write_gpr, reduceCtorEq, ite_false, ite_true]) (by simp only [write_gpr, ite_true]; rfl)
    (by omega) (by omega) (by omega) (by omega) (by omega) (k := 2 * M.n) (Nat.le_refl _))
    fun s₂ ⟨O₂, V₂, C₂, K₂⟩ => ?_)
  simp only [write_mem] at O₂ V₂
  have K₀₂ : Kp [.r0, .r10, .r11, .r12] s s₂ :=
    ((Kp.write s _ (by decide)).trans (Kp.write _ _ (by decide))).trans (K₂.mono (by decide))
  have hs₂ := K₀₂.ws hs
  have h3₂ := K₀₂.at h3
  have h4₂ := K₀₂.at h4
  refine wp_step (lwz0_ok hs₂ h3₂ (by decide) (d := src + 4 * (2 * M.n)) (by omega)) ?_
  refine wp_step exec_add ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
  -- The mask.
  have htop : w32 s₂.mem base (src + 4 * (2 * M.n)) = w32 s.mem base (src + 4 * (2 * M.n)) :=
    O₂.w32 (by omega) (by omega)
  rw [htop]
  generalize hc : (s₂.gpr .r10).toNat = c at C₂ V₂
  generalize hT : w32 s.mem base (src + 4 * (2 * M.n)) = top
  have hL : val32 s₂.mem base src (2 * M.n) = val32 s.mem base src (2 * M.n) := O₂.val32 (by omega) (by omega)
  have hN' : val32 s.mem base src (2 * M.n) + 2 ^ (32 * (2 * M.n)) * top < 2 * m := by
    rw [← hT, ← val32_succ]; exact hN
  have hm0 : m < 2 ^ (32 * (2 * M.n)) := by rw [← hm]; exact val32_lt _ _ _ _
  obtain ⟨hct, hsel⟩ := csub_math hm0 hN' (val32_lt s₂.mem base M.tmp (2 * M.n))
    (by have := V₂; rw [hm] at this; omega) C₂
  have hadd : s₂.gpr .r10 + BitVec.ofNat 64 top = BitVec.ofNat 64 (c + top) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hc, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hadd]
  refine WP.mono (sels_ok (W := M.n) ((((hs₂.write _ _).write _ _).write _ _).write _ _)
    ((((h3₂.write _).write _).write _).write _) ((((h4₂.write _).write _).write _).write _) src4 tmp4
    (by simp only [write_gpr, ite_true]; exact neg_mask hct) (by omega) (by omega) (by omega) (by omega) (by omega)
    (k := M.n) (Nat.le_refl _)) fun u ⟨O₃, V₃, K₃⟩ => ⟨?_, ?_, ?_⟩
  · simp only [write_gpr, ite_true, write_mem] at V₃
    rw [V₃, wordsVal_eq_val32, wordsVal_eq_val32, hL, val32_succ, hT, ← hsel]
    simp only [neg_mask_zero hct]
  · simp only [write_mem] at O₃
    intro x hx
    rw [O₃ x (hx (O, 8 * M.n) (by simp)), O₂ x (by
      have := hx (M.tmp, 8 * M.n) (by simp)
      simp only at this; omega)]
  · exact K₀₂.trans ((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
      ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))).trans (K₃.mono (by decide)))

end VG.Proof.Mont.PPC64LE
