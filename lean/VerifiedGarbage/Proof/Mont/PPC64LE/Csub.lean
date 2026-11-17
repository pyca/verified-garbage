module

import VerifiedGarbage.Proof.Mont.PPC64LE.Row
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-! ### `Mont.PPC64LE.AddSub`, which this module and modules that import it used -/

section

/-!
# Montgomery arithmetic on PPC64LE: sums and differences

`chain sub ra da rb db dd k` stores the low `k` words of `[ra + da] + [rb + db]`
(or, for `sub`, of `[ra + da] - [rb + db] + 2^(64 k)`) at `[r3 + dd]`, word
by word with CA (`chainStep_ok`), and leaves the carry (or, for `sub`, no
borrow) in CA (`chain_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont.PPC64LE VG.Proof.Mont

/-- The carry into word `j` of a chain: none (or no borrow) into the first. -/
def cOf (sub : Bool) (j : Nat) (ca : Bool) : Nat := if j = 0 then sub.toNat else ca.toNat

theorem exec_carryOp (sub : Bool) (j : Nat) (d n m : Reg) (s : State) :
    exec (carryOp sub (j == 0) d n m) s = some (s.writeCarry d ((s.gpr n).toNat +
      (if sub then 2 ^ 64 - 1 - (s.gpr m).toNat else (s.gpr m).toNat) + cOf sub j s.ca)) := by
  cases sub <;> cases j <;> rfl

/-- Word `j` of `[ra + da] ± [rb + db]`, from the carry `cOf sub j CA`, to
`[r3 + dd + 8j]`, the carry to CA. -/
theorem chainStep_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {sub : Bool} {ra rb : Reg}
    {Ka Kb da db dd j : Nat} (ha : At s base ra Ka) (hb : At s base rb Kb) (h3 : At s base .r3 0)
    (hra : ra ≠ .r0) (hrb : rb ∉ [.r0, .r11]) (hda4 : da % 4 = 0) (hdb4 : db % 4 = 0) (hdd4 : dd % 4 = 0)
    (hda : Ka + (da + 8 * j) + 8 ≤ size) (hdb : Kb + (db + 8 * j) + 8 ≤ size) (hdd : dd + 8 * j + 8 ≤ size) :
    WP isa (.block (chainStep sub ra da rb db dd j)) s fun u =>
      ∃ lo : BitVec 64, u.mem = s.mem.writeW (off base (dd + 8 * j)) lo ∧
      lo.toNat + 2 ^ 64 * u.ca.toNat + (if sub then (word s.mem base (Kb + (db + 8 * j))).toNat else 0) =
        (word s.mem base (Ka + (da + 8 * j))).toNat +
          (if sub then 2 ^ 64 - 1 else (word s.mem base (Kb + (db + 8 * j))).toNat) + cOf sub j s.ca ∧
      Kp [.r11, .r12] s u := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hrb
  have hs15 := hs.small
  simp only [chainStep]
  refine wp_step (ld_ok hs ha hra (by omega_arith) hda) ?_
  refine wp_step (ld_ok (hs.write _ _) (hb.write _ hrb.2) hrb.1 (by omega_arith) hdb) ?_
  refine wp_step (exec_carryOp _ _ _ _ _ _) ?_
  refine wp_step (std_ok (((hs.write _ _).write _ _).writeCarry _ _) (((h3.write _).write _).writeCarry _)
    (by decide) (by omega_arith) (d := dd + 8 * j) (by omega_arith)) (WP.block_nil ?_)
  simp only [write_gpr, writeCarry_gpr, write_mem, RegUpd.mem_writeCarry, RegUpd.ca_write,
    reduceCtorEq, ite_false, ite_true, Nat.zero_add]
  refine ⟨_, rfl, ?_, ?_⟩
  · have hc : cOf sub j s.ca ≤ 1 := by unfold cOf; split <;> exact Bool.toNat_le _
    have hx := (word s.mem base (Ka + (da + 8 * j))).isLt
    have hy := (word s.mem base (Kb + (db + 8 * j))).isLt
    have e := RegUpd.toNat_add_ca (((s.write .r11 (word s.mem base (Ka + (da + 8 * j)))).write .r12
      (word s.mem base (Kb + (db + 8 * j))))) (r := .r11) (v := (word s.mem base (Ka + (da + 8 * j))).toNat +
        (if sub then 2 ^ 64 - 1 - (word s.mem base (Kb + (db + 8 * j))).toNat else
          (word s.mem base (Kb + (db + 8 * j))).toNat) + cOf sub j s.ca) (by split <;> omega_arith)
    rw [RegUpd.gpr_writeCarry_self] at e
    rw [show ({ ((s.write .r11 (word s.mem base (Ka + (da + 8 * j)))).write .r12
      (word s.mem base (Kb + (db + 8 * j)))).writeCarry .r11 _ with mem := _ } : State).ca =
      (((s.write .r11 (word s.mem base (Ka + (da + 8 * j)))).write .r12
      (word s.mem base (Kb + (db + 8 * j)))).writeCarry .r11 _).ca from rfl]
    cases sub <;> simp only [ite_true, ite_false, Bool.false_eq_true] at e ⊢ <;> omega_arith
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [write_gpr, writeCarry_gpr, hr.1, hr.2, ite_false]

theorem chain_succ (sub : Bool) (ra : Reg) (da : Nat) (rb : Reg) (db dd k : Nat) :
    chain sub ra da rb db dd (k + 1) = chain sub ra da rb db dd k ++ chainStep sub ra da rb db dd k := by
  simp only [chain, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The low `k` words of `[ra + da] + [rb + db]` (for `sub`, of
`[ra + da] + 2^(64 k) - [rb + db]`) to `[r3 + dd]`, apart from both, the
carry (for `sub`, no borrow) to CA. -/
theorem chain_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {sub : Bool} {ra rb : Reg}
    {Ka Kb da db dd W : Nat} (ha : At s base ra Ka) (hb : At s base rb Kb) (h3 : At s base .r3 0)
    (hra : ra ∉ [.r0, .r11, .r12]) (hrb : rb ∉ [.r0, .r11, .r12]) (hda4 : da % 4 = 0) (hdb4 : db % 4 = 0)
    (hdd4 : dd % 4 = 0) (hda : Ka + da + 8 * W ≤ size) (hdb : Kb + db + 8 * W ≤ size) (hdd : dd + 8 * W ≤ size)
    (sa : Ka + da + 8 * W ≤ dd ∨ dd + 8 * W ≤ Ka + da) (sb : Kb + db + 8 * W ≤ dd ∨ dd + 8 * W ≤ Kb + db) :
    ∀ {k : Nat}, k ≤ W →
    WP isa (.block (chain sub ra da rb db dd k)) s fun u =>
      Outside base dd (8 * k) s.mem u.mem ∧
      wordsVal u.mem base dd k + 2 ^ (64 * k) * cOf sub k u.ca +
          (if sub then wordsVal s.mem base (Kb + db) k else 0) =
        wordsVal s.mem base (Ka + da) k +
          (if sub then 2 ^ (64 * k) - 1 else wordsVal s.mem base (Kb + db) k) + sub.toNat ∧
      Kp [.r11, .r12] s u
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by cases sub <;> simp [wordsVal, cOf], Kp.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [chain_succ]
    refine wp_append (WP.mono (chain_ok hs ha hb h3 hra hrb hda4 hdb4 hdd4 hda hdb hdd sa sb (k := k) (by omega_arith))
      fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    refine WP.mono (chainStep_ok (sub := sub) (K₁.ws hs) (K₁.at ha (not_mem_sub hra)) (K₁.at hb (not_mem_sub hrb))
      (K₁.at h3) (ne_of_not_mem hra) (not_mem_sub hrb) hda4 hdb4 hdd4 (j := k) (by omega_arith) (by omega_arith) (by omega_arith))
      fun u ⟨lo, m₂, c₂, K₂⟩ => ?_
    have xk : word s₁.mem base (Ka + (da + 8 * k)) = word s.mem base (Ka + da + 8 * k) := by
      rw [← Nat.add_assoc]; exact O₁.word (by omega_arith) (by omega_arith)
    have yk : word s₁.mem base (Kb + (db + 8 * k)) = word s.mem base (Kb + db + 8 * k) := by
      rw [← Nat.add_assoc]; exact O₁.word (by omega_arith) (by omega_arith)
    rw [xk, yk] at c₂
    have W := writeW_outside s₁.mem base (d := dd + 8 * k) lo (by omega_arith)
    rw [← m₂] at W
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (W.mono (by omega_arith) (by omega_arith)), ?_, K₁.trans K₂⟩
    rw [wordsVal_succ_top, wordsVal_succ_top, wordsVal_succ_top, W.wordsVal (by omega_arith) (by omega_arith), m₂,
      word_writeW_self, pow64_succ, show cOf sub (k + 1) u.ca = u.ca.toNat from rfl]
    have hP : 1 ≤ 2 ^ (64 * k) := Nat.one_le_two_pow
    generalize 2 ^ (64 * k) = P at *
    generalize cOf sub k s₁.ca = c at *
    have e := congrArg (P * ·) c₂
    simp only [Nat.mul_add] at e
    cases sub
    · simp only [ite_false, Bool.false_eq_true, Nat.add_zero, Bool.toNat_false, Nat.mul_zero] at V₁ e ⊢
      grind
    · simp only [ite_true, Bool.toNat_true] at V₁ e ⊢
      grind

end VG.Proof.Mont.PPC64LE

end

end

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
