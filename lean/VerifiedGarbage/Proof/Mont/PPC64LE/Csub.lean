module

import VerifiedGarbage.Proof.Mont.PPC64LE.Row
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Mont.PPC64LE.AddSub
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Montgomery arithmetic on PPC64LE: the conditional subtraction

`csub M src` reduces the number below `2m` at `[r3 + src]` (`n` words and
a top word) modulo `m` (at `r7`) into `[r4]`: the words of its difference
with `m` go to `[M.tmp]` (`chain_ok`), CA plus the top word is 1 exactly
when the number is at least `m`, and its negation selects the difference or
the number, a word at a time (`sels_ok`, `csub_ok`). `mask32_ok` is the
mask of a 32-bit digit, for code that works on them.
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
  refine wp_step (ld0_ok hs h3 (by decide) (by omega_arith) hsrc) ?_
  refine wp_step (ld0_ok (hs.write _ _) (h3.write _) (by decide) (by omega_arith) htmp) ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_logic ?_
  refine wp_step exec_logic ?_
  refine wp_step (std_ok ((((hs.write _ _).write _ _).write _ _).write _ _ |>.write _ _)
    (((((h4.write _).write _).write _).write _).write _) (by decide) (by omega_arith) (d := 8 * k) hO) (WP.block_nil ?_)
  simp only [write_gpr, write_mem, reduceCtorEq, ite_false, ite_true]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [write_gpr, hr.1, hr.2, ite_false]

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
    refine wp_append (WP.mono (sels_ok hs h3 h4 hsrc4 htmp4 hmk hsrc htmp hO hs1 hs2 (k := k) (by omega_arith))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    refine WP.mono (selWord_ok (K₁.ws hs) (K₁.at h3) (K₁.at h4) hsrc4 htmp4 (k := k) (by omega_arith) (by omega_arith)
      (by omega_arith)) fun u ⟨m₂, K₂⟩ => ?_
    rw [O₁.word (by omega_arith) (by omega_arith), O₁.word (by omega_arith) (by omega_arith), K₁.g, sel_mask _ _ hmk] at m₂
    have W := writeW_outside s₁.mem base (d := O + 8 * k)
      (if s.gpr .r10 = 0 then word s.mem base (src + 8 * k) else word s.mem base (M.tmp + 8 * k)) (by omega_arith)
    rw [← m₂] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), ?_, K₁.trans K₂⟩
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_succ_top, W.wordsVal (by omega_arith) (by omega_arith), V₁, m₂,
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
    have : R * 2 ≤ R * top := Nat.mul_le_mul_left _ (by omega_arith)
    omega_arith
  obtain rfl | rfl : top = 0 ∨ top = 1 := by omega_arith
  · obtain rfl | rfl : c = 0 ∨ c = 1 := by omega_arith
    · simp only [Nat.mul_zero, Nat.add_zero, ite_true] at he hN ⊢
      exact ⟨by omega_arith, (Nat.mod_eq_of_lt (by omega_arith)).symm⟩
    · simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at he hN ⊢
      refine ⟨by omega_arith, ?_⟩
      rw [show (if (1 : Nat) = 0 then L else T) = T from rfl, Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
  · obtain rfl | rfl : c = 0 ∨ c = 1 := by omega_arith
    · simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.zero_add] at he hN ⊢
      refine ⟨by omega_arith, ?_⟩
      rw [show (if (1 : Nat) = 0 then L else T) = T from rfl, Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    · simp only [Nat.mul_one] at he hN
      omega_arith

theorem neg_mask {x : Nat} (hx : x ≤ 1) :
    BitVec.ofNat 64 0 - BitVec.ofNat 64 x = 0 ∨ BitVec.ofNat 64 0 - BitVec.ofNat 64 x = BitVec.allOnes 64 := by
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega_arith
  · exact .inl (by decide)
  · exact .inr (by decide)

theorem neg_mask_zero {x : Nat} (hx : x ≤ 1) : (BitVec.ofNat 64 0 - BitVec.ofNat 64 x = 0) ↔ x = 0 := by
  obtain rfl | rfl : x = 0 ∨ x = 1 := by omega_arith
  · decide
  · decide

/-- What `csub` needs of the layout: the number (`n + 1` words at `src`),
the difference (`n` at `M.tmp`), the modulus (`n` at `M.mo`) and the result
(`n` at `O`). -/
structure CsubLay (M : Mod) (size src O : Nat) : Prop where
  src_le : src + 8 * (M.n + 1) ≤ size
  tmp_le : M.tmp + 8 * M.n ≤ size
  mo_le : M.mo + 8 * M.n ≤ size
  o_le : O + 8 * M.n ≤ size
  src4 : src % 4 = 0
  tmp4 : M.tmp % 4 = 0
  s1 : src + 8 * (M.n + 1) ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ src
  s2 : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo
  s3 : src + 8 * M.n ≤ O ∨ O + 8 * M.n ≤ src
  s4 : M.tmp + 8 * M.n ≤ O ∨ O + 8 * M.n ≤ M.tmp

/-- `[r4] = [r3 + src] mod m`, for a number below `2m` (`n` words and a top
word) and the modulus at `r7`. -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {M : Mod} {src O m : Nat}
    (h3 : At s base .r3 0) (h4 : At s base .r4 O) (h7 : At s base .r7 M.mo) (hL : CsubLay M size src O)
    (hn0 : 0 < M.n) (hm : wordsVal s.mem base M.mo M.n = m) (hN : wordsVal s.mem base src (M.n + 1) < 2 * m) :
    WP isa (.block (csub M src)) s fun u =>
      wordsVal u.mem base O M.n = wordsVal s.mem base src (M.n + 1) % m ∧
      Outs base [(M.tmp, 8 * M.n), (O, 8 * M.n)] s.mem u.mem ∧
      Kp [.r10, .r11, .r12] s u := by
  obtain ⟨src_le, tmp_le, mo_le, o_le, src4, tmp4, s1, s2, s3, s4⟩ := hL
  have hn := hs.nowrap
  have hs15 := hs.small
  have ec : csub M src = chain true wb src .r7 0 M.tmp M.n ++
      ([.load .d .r11 wb (src + 8 * M.n), .addze .r10 .r11, .li .r11 0, .sub .r10 .r11 .r10] ++
        sels M src M.n) := by
    simp only [csub, List.append_assoc]
  rw [ec]
  refine wp_append (WP.mono (chain_ok (sub := true) (W := M.n) hs h3 h7 h3 (by decide) (by decide) src4
    (by decide) tmp4 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (k := M.n) (Nat.le_refl _))
    fun s₂ ⟨O₂, V₂, K₂⟩ => ?_)
  simp only [ite_true, Bool.toNat_true, Nat.zero_add, Nat.add_zero] at V₂
  rw [hm, show cOf true M.n s₂.ca = s₂.ca.toNat by simp only [cOf]; split <;> omega_arith] at V₂
  have hs₂ := K₂.ws hs
  have h3₂ := K₂.at h3
  have h4₂ := K₂.at h4
  refine wp_step (ld0_ok hs₂ h3₂ (by decide) (by omega_arith) (d := src + 8 * M.n) (by omega_arith)) ?_
  refine wp_step exec_addze ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  simp only [write_gpr, writeCarry_gpr, ite_true, reduceCtorEq, ite_false, RegUpd.ca_write]
  -- The mask.
  have htop : word s₂.mem base (src + 8 * M.n) = word s.mem base (src + 8 * M.n) :=
    O₂.word (by omega_arith) (by omega_arith)
  rw [htop]
  generalize hc : s₂.ca.toNat = c at V₂
  generalize hT : (word s.mem base (src + 8 * M.n)).toNat = top
  have hL : wordsVal s₂.mem base src M.n = wordsVal s.mem base src M.n := O₂.wordsVal (by omega_arith) (by omega_arith)
  have hN' : wordsVal s.mem base src M.n + 2 ^ (64 * M.n) * top < 2 * m := by
    rw [← hT, ← wordsVal_succ_top]; exact hN
  have hm0 : m < 2 ^ (64 * M.n) := by rw [← hm]; exact wordsVal_lt _ _ _ _
  have hc1 : c ≤ 1 := hc ▸ Bool.toNat_le _
  obtain ⟨hct, hsel⟩ := csub_math hm0 hN' (wordsVal_lt s₂.mem base M.tmp M.n)
    (by have := V₂; omega_arith) hc1
  have hadd : BitVec.ofNat 64 (top + c) = BitVec.ofNat 64 (c + top) := by rw [Nat.add_comm]
  rw [hadd]
  refine WP.mono (sels_ok (W := M.n) ((((hs₂.write _ _).writeCarry _ _).write _ _).write _ _)
    ((((h3₂.write _).writeCarry _).write _).write _) ((((h4₂.write _).writeCarry _).write _).write _) src4 tmp4
    (by simp only [write_gpr, ite_true]; exact neg_mask hct) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (k := M.n) (Nat.le_refl _)) fun u ⟨O₃, V₃, K₃⟩ => ⟨?_, ?_, ?_⟩
  · simp only [write_gpr, ite_true, write_mem, RegUpd.mem_writeCarry] at V₃
    rw [V₃, hL, wordsVal_succ_top, hT, ← hsel]
    simp only [neg_mask_zero hct]
  · simp only [write_mem, RegUpd.mem_writeCarry] at O₃
    intro x hx
    rw [O₃ x (hx (O, 8 * M.n) (by simp)), O₂ x (by
      have := hx (M.tmp, 8 * M.n) (by simp)
      simp only at this; omega_arith)]
  · exact (K₂.mono (by decide)).trans ((((Kp.write _ _ (by decide)).trans (Kp.writeCarry _ _ (by decide))).trans
      ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide)))).trans (K₃.mono (by decide)))

end VG.Proof.Mont.PPC64LE
