module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Mont.PPC64LE
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

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
