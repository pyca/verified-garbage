import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery arithmetic on 32-bit ARM: the operations

For a modulus `m` in the working space (`ModOkW`) and an accumulator of
`accLen M` bytes at `acc` apart from the numbers (`OpLay`): `mul acc o a b`
writes `[a] [b] R⁻¹ mod m` to `[o]` (`mul_ok`), `add` writes
`[a] + [b] mod m` (`add_ok`) and `sub` writes `[a] - [b] mod m` (`sub_ok`),
for `[a]`, `[b]` below `m`, in the shape of the other targets' operations
(`n` 64-bit words). Each changes only the registers `clob`, the result, the
temporary area and the accumulator (`OpKeep`).
-/

namespace VG.Proof.Mont.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_movw op2_reg op2_lsr op2_imm dpVal
  toNat_add_lt toNat_shr)

/-- The bytes of the accumulator: `2D + 2` digits. -/
def accLen (M : Mod) : Nat := 4 * (2 * digits M + 2)

/-- Where the operations' numbers are: in the working space, and the
accumulator apart from them, from the modulus and from the temporary area,
which `[o]` is apart from too. -/
structure OpLay (M : Mod) (size acc o a b : Nat) : Prop where
  acc_le : acc + accLen M ≤ size
  o_le : o + 8 * M.n ≤ size
  a_le : a + 8 * M.n ≤ size
  b_le : b + 8 * M.n ≤ size
  acc_o : acc + accLen M ≤ o ∨ o + 8 * M.n ≤ acc
  acc_a : acc + accLen M ≤ a ∨ a + 8 * M.n ≤ acc
  acc_b : acc + accLen M ≤ b ∨ b + 8 * M.n ≤ acc
  acc_mo : acc + accLen M ≤ M.mo ∨ M.mo + 8 * M.n ≤ acc
  acc_tmp : acc + accLen M ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ acc
  o_tmp : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o

/-- What an operation writing `[o]` keeps: the registers but `clob`, the
regions, the stack pointer, and the memory but `[o]`, the temporary area and
the accumulator. -/
structure OpKeep (M : Mod) (base : Addr) (acc o : Nat) (s s' : State) : Prop where
  rest : Rest clob s s'
  mem : Outs base [(o, 8 * M.n), (M.tmp, 8 * M.n), (acc, accLen M)] s.mem s'.mem

theorem m_pos_of_inv {m : Nat} {minv : Nat} (h : (m * minv + 1) % 2 ^ 64 = 0) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with rfl | h'
  · simp at h
  · exact h'

/-- The count of words, an immediate. -/
theorem words_encodable {M : Mod} (h : M.n < 128) : encodable (BitVec.ofNat 32 (words M)) = true := by
  have : ∀ n < 128, encodable (BitVec.ofNat 32 (2 * n)) = true := by decide
  exact this _ h

/-! ## Clearing the accumulator -/

/-- `k` stores of `r7 = 0` from `[acc]`. -/
theorem stores0_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (h7 : s.gpr .r7 = 0)
    {acc : Nat} : ∀ k, acc + 4 * k ≤ size →
    WP isa (.block ((List.range k).map fun j => .str .r7 wb (acc + 4 * j))) s fun u =>
      Outside base acc (4 * k) s.mem u.mem ∧ (∀ j < k, w32 u.mem base (acc + 4 * j) = 0) ∧ Rest [] s u
  | 0, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      Rest.refl _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    refine VG.Proof.X25519.Arm.WP.append (stores0_ok hs h7 k (by omega_arith)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    refine wp_str (hs.off_lt (by omega_arith)) (hs₁.ea (by omega_arith)) (hs₁.write (d := acc + 4 * k) (n := 4) (by omega_arith))
      fun u m => WP.block_nil ⟨?_, fun j hj => ?_, K₁.trans (m.rest _)⟩
    · rw [m.mem]
      exact (O₁.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · rw [m.mem]
      rcases Nat.lt_or_ge j k with h | h
      · rw [w32_write_ne hn (size := size) (by omega_arith) (by omega_arith) (by omega_arith), V₁ j h]
      · rw [show j = k by omega_arith, w32_write_self, K₁.gpr _ (by decide), h7]; rfl

theorem zeros_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc k : Nat}
    (hk : acc + 4 * k ≤ size) {is : List Instr} {Q : State → Prop}
    (h : ∀ u, Outside base acc (4 * k) s.mem u.mem → (∀ j < k, w32 u.mem base (acc + 4 * j) = 0) →
      Rest [.r7] s u → WP isa (.block is) u Q) :
    WP isa (.block (zeros acc k ++ is)) s Q := by
  simp only [zeros, List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine VG.Proof.X25519.Arm.WP.append (stores0_ok (hs.of_rest (u₁.rest (ws := [.r7]) (by simp)) (by decide))
    u₁.gpr k hk) fun u ⟨O, V, K⟩ => h u (u₁.mem ▸ O) V ((u₁.rest (by simp)).trans (K.mono (by simp)))

theorem dval_zero {m : Mem} {base : Addr} {d : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m base (d + 4 * j) = 0) → dval m base d k = 0
  | 0, _ => rfl
  | k + 1, h => by rw [dval, dval_zero fun j hj => h j (by omega_arith), h k (by omega_arith), Nat.zero_mul]

/-! ## Addition -/

/-- Digit `j` of `[a] + [b]`, from the carry `c`, to `[acc + 4j]`, with `r7`
and `r8` their words. -/
theorem addDigit_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hj : acc + 4 * j + 4 ≤ size) (hc : (s.gpr .r3).toNat ≤ 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Outside base (acc + 4 * j) 4 s.mem u.mem → w32 u.mem base (acc + 4 * j) < 2 ^ 16 →
      w32 u.mem base (acc + 4 * j) + 2 ^ 16 * (u.gpr .r3).toNat =
        hdig (s.gpr .r7).toNat (j % 2) + hdig (s.gpr .r8).toNat (j % 2) + (s.gpr .r3).toNat →
      (u.gpr .r3).toNat ≤ 1 → Rest [.r3, .r4, .r5] s u → WP isa (.block is) u Q) :
    WP isa (.block (addDigit acc j ++ is)) s Q := by
  have hn := hs.nowrap
  simp only [addDigit, List.cons_append, List.nil_append]
  refine wp_half (Nat.mod_lt _ (by decide)) h6 fun s₁ u₁ => ?_
  refine wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have K₅ : Rest [.r3, .r4, .r5] s s₅ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp)))))
  have hs₅ := hs.of_rest K₅ (by decide)
  refine wp_str (hs.off_lt (by omega_arith)) (hs₅.ea (by omega_arith)) (hs₅.write hj) fun s₆ m₆ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₇ u₇ => ?_
  have d0 := hdig_lt (s.gpr .r7).toNat (j % 2)
  have d1 := hdig_lt (s.gpr .r8).toNat (j % 2)
  have a1 : (s₁.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) := by rw [u₁.gpr, BitVec.toNat_ofNat]; omega_arith
  have a2 : (s₂.gpr .r5).toNat = hdig (s.gpr .r8).toNat (j % 2) := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_ofNat]; omega_arith
  have a2r4 : s₂.gpr .r4 = s₁.gpr .r4 := u₂.other _ (by decide)
  have a3 : (s₃.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) + hdig (s.gpr .r8).toNat (j % 2) := by
    rw [u₃.gpr, dpVal, toNat_add_lt (by rw [a2r4, a1, a2]; omega_arith), a2r4, a1, a2]
  have a3r3 : s₃.gpr .r3 = s.gpr .r3 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have a4 : (s₄.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) + hdig (s.gpr .r8).toNat (j % 2) +
      (s.gpr .r3).toNat := by
    rw [u₄.gpr, dpVal, toNat_add_lt (by rw [a3, a3r3]; omega_arith), a3, a3r3]
  have h6₄ : s₄.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact h6
  have a5 : (s₅.gpr .r5).toNat = (s₄.gpr .r4).toNat % 2 ^ 16 := by rw [u₅.gpr, dpVal, toNat_and_r6 h6₄]
  have r4₆ : s₆.gpr .r4 = s₄.gpr .r4 := by rw [m₆.gpr, u₅.other _ (by decide)]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r3₇ : (s₇.gpr .r3).toNat = (s₄.gpr .r4).toNat / 2 ^ 16 := by rw [u₇.gpr, toNat_shr, r4₆]
  have w₇ : w32 s₇.mem base (acc + 4 * j) = (s₄.gpr .r4).toNat % 2 ^ 16 := by
    rw [u₇.mem, m₆.mem, w32_write_self, a5]
  refine k s₇ ?_ (by rw [w₇]; omega_arith) (by rw [w₇, r3₇, a4]; omega_arith) (by rw [r3₇, a4]; omega_arith)
    (K₅.trans ((m₆.rest _).trans (u₇.rest (by simp))))
  rw [u₇.mem, m₆.mem, mem₅]; exact writeW32_outside _ _ _ (by omega_arith)

/-- A register outside a list is outside any of its sublists. -/
theorem not_mem_sub {r : Reg} {l l' : List Reg} (h : r ∉ l') (hl : ∀ x ∈ l, x ∈ l' := by decide) : r ∉ l :=
  fun hr => h (hl r hr)

/-- A register outside a list is none of its members. -/
theorem ne_of_not_mem {r x : Reg} {l : List Reg} (h : r ∉ l) (hx : x ∈ l := by decide) : r ≠ x :=
  fun e => h (e ▸ hx)

/-- Word `k` of `[ra + a] + [rb + b]`. -/
def addWord (acc : Nat) (ra : Reg) (a : Nat) (rb : Reg) (b k : Nat) : List Instr :=
  [.ldr .r7 ra (a + 4 * k), .ldr .r8 rb (b + 4 * k)] ++ addDigit acc (2 * k) ++ addDigit acc (2 * k + 1)

/-- The first `k` words of `[ra + a] + [rb + b]`. -/
def addK (acc : Nat) (ra : Reg) (a : Nat) (rb : Reg) (b k : Nat) : List Instr :=
  (List.range k).flatMap (addWord acc ra a rb b)

theorem addK_succ (acc : Nat) (ra : Reg) (a : Nat) (rb : Reg) (b k : Nat) :
    addK acc ra a rb b (k + 1) = addK acc ra a rb b k ++ addWord acc ra a rb b k := by
  simp only [addK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The digits of the first `k` words of `[a] + [b]`, from the carry `c`
(read at `[ra + da]` and `[rb + db]`, `ra = r12 + ka`, `rb = r12 + kb`). -/
theorem addK_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc a b : Nat}
    {ra rb : Reg} {ka da kb db : Nat} (hra : s.gpr ra = s.gpr .r12 + BitVec.ofNat 32 ka) (hka : ka + da = a)
    (hrb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 kb) (hkb : kb + db = b)
    (hra' : ra ∉ [.r3, .r4, .r5, .r7, .r8]) (hrb' : rb ∉ [.r3, .r4, .r5, .r7, .r8])
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hc : (s.gpr .r3).toNat ≤ 1) :
    ∀ {k : Nat}, acc + 4 * (2 * k) ≤ size → a + 4 * k ≤ size → b + 4 * k ≤ size →
    (acc + 4 * (2 * k) ≤ a ∨ a + 4 * k ≤ acc) → (acc + 4 * (2 * k) ≤ b ∨ b + 4 * k ≤ acc) →
    WP isa (.block (addK acc ra da rb db k)) s fun u =>
      Outside base acc (4 * (2 * k)) s.mem u.mem ∧ Digs u.mem base acc (2 * k) ∧ (u.gpr .r3).toNat ≤ 1 ∧
      dval u.mem base acc (2 * k) + 2 ^ (32 * k) * (u.gpr .r3).toNat =
        val32 s.mem base a k + val32 s.mem base b k + (s.gpr .r3).toNat ∧
      Rest [.r3, .r4, .r5, .r7, .r8] s u
  | 0, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      hc, by simp only [val32, dval, Nat.mul_zero, Nat.pow_zero]; omega_arith, Rest.refl _ _⟩
  | k + 1, hacc, ha, hb, hsa, hsb => by
    have hn := hs.nowrap
    rw [addK_succ]
    refine VG.Proof.X25519.Arm.WP.append (addK_ok hs hra hka hrb hkb hra' hrb' h6 hc (k := k) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₁ ⟨O₁, D₁, C₁, V₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    simp only [addWord, List.cons_append, List.append_assoc]
    have ea₁ : State.addr (s₁.gpr ra + BitVec.ofNat 32 (da + 4 * k)) = off base (a + 4 * k) := by
      rw [← hka, Nat.add_assoc]
      exact hs₁.ea_off (by rw [K₁.gpr _ hra', K₁.gpr _ (by decide)]; exact hra) (by omega_arith)
    refine wp_ldr (hs.off_lt (d := da + 4 * k) (by omega_arith)) ea₁ (hs₁.read (d := a + 4 * k) (n := 4) (by omega_arith))
      fun s₂ u₂ => ?_
    have ea₂ : State.addr (s₂.gpr rb + BitVec.ofNat 32 (db + 4 * k)) = off base (b + 4 * k) := by
      rw [← hkb, Nat.add_assoc]
      refine (hs₁.of_rest (u₂.rest (ws := [.r7]) (by simp)) (by decide)).ea_off ?_ (by omega_arith)
      rw [u₂.other _ (ne_of_not_mem hrb'), u₂.other _ (by decide), K₁.gpr _ hrb',
        K₁.gpr _ (by decide)]
      exact hrb
    refine wp_ldr (hs.off_lt (d := db + 4 * k) (by omega_arith)) ea₂
      (by rw [u₂.wr, u₂.rd]; exact hs₁.read (d := b + 4 * k) (n := 4) (by omega_arith)) fun s₃ u₃ => ?_
    have K₃ : Rest [.r3, .r4, .r5, .r7, .r8] s s₃ := K₁.trans ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
    have hs₃ := hs.of_rest K₃ (by decide)
    refine addDigit_ok hs₃ (j := 2 * k) (by rw [K₃.gpr _ (by decide)]; exact h6) (by omega_arith)
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide)]; exact C₁) fun s₄ O₄ W₄ V₄ C₄ K₄ => ?_
    have K₄' := K₃.trans (K₄.mono (by simp))
    have hs₄ := hs.of_rest K₄' (by decide)
    refine addDigit_ok hs₄ (j := 2 * k + 1) (by rw [K₄'.gpr _ (by decide)]; exact h6) (by omega_arith) C₄
      fun u O₅ W₅ V₅ C₅ K₅ => WP.block_nil ?_
    have m₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
    have hwa : (s₂.gpr .r7).toNat = w32 s.mem base (a + 4 * k) := by
      rw [u₂.gpr]; exact O₁.w32 (by omega_arith) (by omega_arith)
    have hwb : (s₃.gpr .r8).toNat = w32 s.mem base (b + 4 * k) := by
      rw [u₃.gpr, u₂.mem]; exact O₁.w32 (by omega_arith) (by omega_arith)
    have r7₃ : s₃.gpr .r7 = s₂.gpr .r7 := u₃.other _ (by decide)
    have r7₄ : s₄.gpr .r7 = s₂.gpr .r7 := by rw [K₄.gpr _ (by decide), r7₃]
    have r8₄ : s₄.gpr .r8 = s₃.gpr .r8 := K₄.gpr _ (by decide)
    have r3₃ : s₃.gpr .r3 = s₁.gpr .r3 := by rw [u₃.other _ (by decide), u₂.other _ (by decide)]
    rw [r7₃, hwa, hwb, r3₃, show 2 * k % 2 = 0 by omega_arith] at V₄
    rw [r7₄, hwa, r8₄, hwb, show (2 * k + 1) % 2 = 1 by omega_arith] at V₅
    have O₄' : Outside base acc (4 * (2 * (k + 1))) s₁.mem s₄.mem := by
      rw [← m₃]; exact O₄.mono (by omega_arith) (by omega_arith)
    have O₅' : Outside base acc (4 * (2 * (k + 1))) s₄.mem u.mem := O₅.mono (by omega_arith) (by omega_arith)
    have w0 : w32 u.mem base (acc + 4 * (2 * k)) = w32 s₄.mem base (acc + 4 * (2 * k)) :=
      O₅.w32 (by omega_arith) (by omega_arith)
    have low : ∀ j < 2 * k, w32 u.mem base (acc + 4 * j) = w32 s₁.mem base (acc + 4 * j) := fun j hj => by
      rw [O₅.w32 (by omega_arith) (by omega_arith), O₄.w32 (by omega_arith) (by omega_arith), m₃]
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₄'.trans O₅'), fun j hj => ?_, C₅, ?_,
      K₄'.trans (K₅.mono (by simp))⟩
    · rcases Nat.lt_or_ge j (2 * k) with h | h
      · rw [low j h]; exact D₁ j h
      · obtain rfl | rfl : j = 2 * k ∨ j = 2 * k + 1 := by omega_arith
        · rw [w0]; exact W₄
        · exact W₅
    · have hd : dval u.mem base acc (2 * k) = dval s₁.mem base acc (2 * k) := dval_congr low
      have ea := word_digits (w32 s.mem base (a + 4 * k)) (BitVec.isLt _)
      have eb := word_digits (w32 s.mem base (b + 4 * k)) (BitVec.isLt _)
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega_arith, dval, dval, hd, w0, val32_append _ _ _ k 1,
        val32_append _ _ _ k 1, show 32 * (k + 1) = 32 * k + 32 by omega_arith, Nat.pow_add,
        show 16 * (2 * k + 1) = 32 * k + 16 by omega_arith, show 16 * (2 * k) = 32 * k by omega_arith, Nat.pow_add]
      simp only [val32, Nat.mul_zero, Nat.add_zero]
      generalize 2 ^ (32 * k) = P at *
      generalize hdig (w32 s.mem base (a + 4 * k)) 0 = a0 at *
      generalize hdig (w32 s.mem base (a + 4 * k)) 1 = a1 at *
      generalize hdig (w32 s.mem base (b + 4 * k)) 0 = b0 at *
      generalize hdig (w32 s.mem base (b + 4 * k)) 1 = b1 at *
      grind

/-! ## Subtraction -/

/-- Digit `j` of `[a] + m - [b]`, from the carry `c`, to `[acc + 4j]`, with
`r7`, `r8` and `r9` the words of `[a]`, `[b]` and `m`. -/
theorem subDigit_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc j : Nat}
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hj : acc + 4 * j + 4 ≤ size) (hc : (s.gpr .r3).toNat ≤ 2)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, Outside base (acc + 4 * j) 4 s.mem u.mem → w32 u.mem base (acc + 4 * j) < 2 ^ 16 →
      w32 u.mem base (acc + 4 * j) + 2 ^ 16 * (u.gpr .r3).toNat =
        hdig (s.gpr .r7).toNat (j % 2) + hdig (s.gpr .r9).toNat (j % 2) +
          (2 ^ 16 - 1 - hdig (s.gpr .r8).toNat (j % 2)) + (s.gpr .r3).toNat →
      (u.gpr .r3).toNat ≤ 2 → Rest [.r3, .r4, .r5] s u → WP isa (.block is) u Q) :
    WP isa (.block (subDigit acc j ++ is)) s Q := by
  have hn := hs.nowrap
  simp only [subDigit, List.cons_append, List.nil_append]
  refine wp_half (Nat.mod_lt _ (by decide)) h6 fun s₁ u₁ => ?_
  refine wp_half (Nat.mod_lt _ (by decide)) (by rw [u₁.other _ (by decide)]; exact h6) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  have h6₄ : s₄.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    exact h6
  refine wp_half (Nat.mod_lt _ (by decide)) h6₄ fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  refine wp_dp (op2_reg _ _) fun s₇ u₇ => ?_
  refine wp_dp (op2_reg _ _) fun s₈ u₈ => ?_
  have K₈ : Rest [.r3, .r4, .r5] s s₈ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans ((u₆.rest (by simp)).trans
      ((u₇.rest (by simp)).trans (u₈.rest (by simp))))))))
  have hs₈ := hs.of_rest K₈ (by decide)
  refine wp_str (hs.off_lt (by omega_arith)) (hs₈.ea (by omega_arith)) (hs₈.write hj) fun s₉ m₉ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₁₀ u₁₀ => ?_
  have d0 := hdig_lt (s.gpr .r7).toNat (j % 2)
  have d1 := hdig_lt (s.gpr .r9).toNat (j % 2)
  have d2 := hdig_lt (s.gpr .r8).toNat (j % 2)
  have a1 : (s₁.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) := by rw [u₁.gpr, BitVec.toNat_ofNat]; omega_arith
  have a2 : (s₂.gpr .r5).toNat = hdig (s.gpr .r9).toNat (j % 2) := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_ofNat]; omega_arith
  have a2r4 : s₂.gpr .r4 = s₁.gpr .r4 := u₂.other _ (by decide)
  have a3 : (s₃.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) + hdig (s.gpr .r9).toNat (j % 2) := by
    rw [u₃.gpr, dpVal, toNat_add_lt (by rw [a2r4, a1, a2]; omega_arith), a2r4, a1, a2]
  have h6₃ : s₃.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact h6
  have a4 : (s₄.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) + hdig (s.gpr .r9).toNat (j % 2) +
      (2 ^ 16 - 1) := by
    rw [u₄.gpr, dpVal, toNat_add_lt (by rw [a3, h6₃, toNat_mask16]; omega_arith), a3, h6₃, toNat_mask16]
  have a5 : (s₅.gpr .r5).toNat = hdig (s.gpr .r8).toNat (j % 2) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      BitVec.toNat_ofNat]; omega_arith
  have a5r4 : s₅.gpr .r4 = s₄.gpr .r4 := u₅.other _ (by decide)
  have a6 : (s₆.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) + hdig (s.gpr .r9).toNat (j % 2) +
      (2 ^ 16 - 1 - hdig (s.gpr .r8).toNat (j % 2)) := by
    rw [u₆.gpr, dpVal, VG.Proof.X25519.Arm.toNat_sub_le (by rw [a5r4, a4, a5]; omega_arith), a5r4, a4, a5]; omega_arith
  have a6r3 : s₆.gpr .r3 = s.gpr .r3 := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  have a7 : (s₇.gpr .r4).toNat = hdig (s.gpr .r7).toNat (j % 2) + hdig (s.gpr .r9).toNat (j % 2) +
      (2 ^ 16 - 1 - hdig (s.gpr .r8).toNat (j % 2)) + (s.gpr .r3).toNat := by
    rw [u₇.gpr, dpVal, toNat_add_lt (by rw [a6, a6r3]; omega_arith), a6, a6r3]
  have h6₇ : s₇.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide)]; exact h6₄
  have a8 : (s₈.gpr .r5).toNat = (s₇.gpr .r4).toNat % 2 ^ 16 := by rw [u₈.gpr, dpVal, toNat_and_r6 h6₇]
  have r4₉ : s₉.gpr .r4 = s₇.gpr .r4 := by rw [m₉.gpr, u₈.other _ (by decide)]
  have mem₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r3₁₀ : (s₁₀.gpr .r3).toNat = (s₇.gpr .r4).toNat / 2 ^ 16 := by rw [u₁₀.gpr, toNat_shr, r4₉]
  have w₁₀ : w32 s₁₀.mem base (acc + 4 * j) = (s₇.gpr .r4).toNat % 2 ^ 16 := by
    rw [u₁₀.mem, m₉.mem, w32_write_self, a8]
  refine k s₁₀ ?_ (by rw [w₁₀]; omega_arith) (by rw [w₁₀, r3₁₀, a7]; omega_arith) (by rw [r3₁₀, a7]; omega_arith)
    (K₈.trans ((m₉.rest _).trans (u₁₀.rest (by simp))))
  rw [u₁₀.mem, m₉.mem, mem₈]; exact writeW32_outside _ _ _ (by omega_arith)

/-- Word `k` of `[ra + a] + m - [rb + b]`. -/
def subWord (acc : Nat) (ra : Reg) (a : Nat) (rb : Reg) (b mo k : Nat) : List Instr :=
  [.ldr .r7 ra (a + 4 * k), .ldr .r8 rb (b + 4 * k), .ldr .r9 wb (mo + 4 * k)] ++ subDigit acc (2 * k) ++
    subDigit acc (2 * k + 1)

/-- The first `k` words of `[ra + a] + m - [rb + b]`. -/
def subK (acc : Nat) (ra : Reg) (a : Nat) (rb : Reg) (b mo k : Nat) : List Instr :=
  (List.range k).flatMap (subWord acc ra a rb b mo)

theorem subK_succ (acc : Nat) (ra : Reg) (a : Nat) (rb : Reg) (b mo k : Nat) :
    subK acc ra a rb b mo (k + 1) = subK acc ra a rb b mo k ++ subWord acc ra a rb b mo k := by
  simp only [subK, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The digits of the first `k` words of `[a] + m - [b]`, from the carry `c`:
`T + 2^(32k) c' + B + 1 = A + M + 2^(32k) + c` (`[a]` and `[b]` read at
`[ra + da]` and `[rb + db]`, `ra = r12 + ka`, `rb = r12 + kb`). -/
theorem subK_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc a b mo : Nat}
    {ra rb : Reg} {ka da kb db : Nat} (hra : s.gpr ra = s.gpr .r12 + BitVec.ofNat 32 ka) (hka : ka + da = a)
    (hrb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 kb) (hkb : kb + db = b)
    (hra' : ra ∉ [.r3, .r4, .r5, .r7, .r8, .r9]) (hrb' : rb ∉ [.r3, .r4, .r5, .r7, .r8, .r9])
    (h6 : s.gpr .r6 = VG.Proof.X25519.Arm.mask16) (hc : (s.gpr .r3).toNat ≤ 2) :
    ∀ {k : Nat}, acc + 4 * (2 * k) ≤ size → a + 4 * k ≤ size → b + 4 * k ≤ size → mo + 4 * k ≤ size →
    (acc + 4 * (2 * k) ≤ a ∨ a + 4 * k ≤ acc) → (acc + 4 * (2 * k) ≤ b ∨ b + 4 * k ≤ acc) →
    (acc + 4 * (2 * k) ≤ mo ∨ mo + 4 * k ≤ acc) →
    WP isa (.block (subK acc ra da rb db mo k)) s fun u =>
      Outside base acc (4 * (2 * k)) s.mem u.mem ∧ Digs u.mem base acc (2 * k) ∧ (u.gpr .r3).toNat ≤ 2 ∧
      dval u.mem base acc (2 * k) + 2 ^ (32 * k) * (u.gpr .r3).toNat + val32 s.mem base b k + 1 =
        val32 s.mem base a k + val32 s.mem base mo k + 2 ^ (32 * k) + (s.gpr .r3).toNat ∧
      Rest [.r3, .r4, .r5, .r7, .r8, .r9] s u
  | 0, _, _, _, _, _, _, _ => WP.block_nil ⟨VG.Proof.Mont.Outside.refl _ _ _ _,
      fun _ h => absurd h (Nat.not_lt_zero _), hc, by simp only [val32, dval, Nat.mul_zero, Nat.pow_zero]; omega_arith,
      Rest.refl _ _⟩
  | k + 1, hacc, ha, hb, hmo, hsa, hsb, hsm => by
    have hn := hs.nowrap
    rw [subK_succ]
    refine VG.Proof.X25519.Arm.WP.append (subK_ok hs hra hka hrb hkb hra' hrb' h6 hc (k := k) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
      fun s₁ ⟨O₁, D₁, C₁, V₁, K₁⟩ => ?_
    have hs₁ := hs.of_rest K₁ (by decide)
    simp only [subWord, List.cons_append, List.append_assoc]
    have ea₁ : State.addr (s₁.gpr ra + BitVec.ofNat 32 (da + 4 * k)) = off base (a + 4 * k) := by
      rw [← hka, Nat.add_assoc]
      exact hs₁.ea_off (by rw [K₁.gpr _ hra', K₁.gpr _ (by decide)]; exact hra) (by omega_arith)
    refine wp_ldr (hs.off_lt (d := da + 4 * k) (by omega_arith)) ea₁ (hs₁.read (d := a + 4 * k) (n := 4) (by omega_arith))
      fun s₂ u₂ => ?_
    have hs₂ := hs₁.of_rest (u₂.rest (ws := [.r7]) (by simp)) (by decide)
    have ea₂ : State.addr (s₂.gpr rb + BitVec.ofNat 32 (db + 4 * k)) = off base (b + 4 * k) := by
      rw [← hkb, Nat.add_assoc]
      refine hs₂.ea_off ?_ (by omega_arith)
      rw [u₂.other _ (ne_of_not_mem hrb'), u₂.other _ (by decide), K₁.gpr _ hrb',
        K₁.gpr _ (by decide)]
      exact hrb
    refine wp_ldr (hs.off_lt (d := db + 4 * k) (by omega_arith)) ea₂ (hs₂.read (d := b + 4 * k) (n := 4) (by omega_arith))
      fun s₃ u₃ => ?_
    have hs₃' := hs₂.of_rest (u₃.rest (ws := [.r8]) (by simp)) (by decide)
    refine wp_ldr (hs.off_lt (by omega_arith)) (hs₃'.ea (by omega_arith)) (hs₃'.read (d := mo + 4 * k) (n := 4) (by omega_arith))
      fun s₃' u₃' => ?_
    have K₃ : Rest [.r3, .r4, .r5, .r7, .r8, .r9] s s₃' :=
      K₁.trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₃'.rest (by simp))))
    have hs₃ := hs.of_rest K₃ (by decide)
    refine subDigit_ok hs₃ (j := 2 * k) (by rw [K₃.gpr _ (by decide)]; exact h6) (by omega_arith)
      (by rw [u₃'.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]; exact C₁)
      fun s₄ O₄ W₄ V₄ C₄ K₄ => ?_
    have K₄' := K₃.trans (K₄.mono (by simp))
    have hs₄ := hs.of_rest K₄' (by decide)
    refine subDigit_ok hs₄ (j := 2 * k + 1) (by rw [K₄'.gpr _ (by decide)]; exact h6) (by omega_arith) C₄
      fun u O₅ W₅ V₅ C₅ K₅ => WP.block_nil ?_
    have m₃ : s₃'.mem = s₁.mem := by rw [u₃'.mem, u₃.mem, u₂.mem]
    have hwa : (s₂.gpr .r7).toNat = w32 s.mem base (a + 4 * k) := by
      rw [u₂.gpr]; exact O₁.w32 (by omega_arith) (by omega_arith)
    have hwb : (s₃.gpr .r8).toNat = w32 s.mem base (b + 4 * k) := by
      rw [u₃.gpr, u₂.mem]; exact O₁.w32 (by omega_arith) (by omega_arith)
    have hwm : (s₃'.gpr .r9).toNat = w32 s.mem base (mo + 4 * k) := by
      rw [u₃'.gpr, u₃.mem, u₂.mem]; exact O₁.w32 (by omega_arith) (by omega_arith)
    have r7₃ : s₃'.gpr .r7 = s₂.gpr .r7 := by rw [u₃'.other _ (by decide), u₃.other _ (by decide)]
    have r8₃ : s₃'.gpr .r8 = s₃.gpr .r8 := u₃'.other _ (by decide)
    have r7₄ : s₄.gpr .r7 = s₂.gpr .r7 := by rw [K₄.gpr _ (by decide), r7₃]
    have r8₄ : s₄.gpr .r8 = s₃.gpr .r8 := by rw [K₄.gpr _ (by decide), r8₃]
    have r9₄ : s₄.gpr .r9 = s₃'.gpr .r9 := K₄.gpr _ (by decide)
    have r3₃ : s₃'.gpr .r3 = s₁.gpr .r3 := by
      rw [u₃'.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]
    rw [r7₃, hwa, r8₃, hwb, hwm, r3₃, show 2 * k % 2 = 0 by omega_arith] at V₄
    rw [r7₄, hwa, r8₄, hwb, r9₄, hwm, show (2 * k + 1) % 2 = 1 by omega_arith] at V₅
    have O₄' : Outside base acc (4 * (2 * (k + 1))) s₁.mem s₄.mem := by
      rw [← m₃]; exact O₄.mono (by omega_arith) (by omega_arith)
    have O₅' : Outside base acc (4 * (2 * (k + 1))) s₄.mem u.mem := O₅.mono (by omega_arith) (by omega_arith)
    have w0 : w32 u.mem base (acc + 4 * (2 * k)) = w32 s₄.mem base (acc + 4 * (2 * k)) :=
      O₅.w32 (by omega_arith) (by omega_arith)
    have low : ∀ j < 2 * k, w32 u.mem base (acc + 4 * j) = w32 s₁.mem base (acc + 4 * j) := fun j hj => by
      rw [O₅.w32 (by omega_arith) (by omega_arith), O₄.w32 (by omega_arith) (by omega_arith), m₃]
    refine ⟨(O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₄'.trans O₅'), fun j hj => ?_, C₅, ?_,
      K₄'.trans (K₅.mono (by simp))⟩
    · rcases Nat.lt_or_ge j (2 * k) with h | h
      · rw [low j h]; exact D₁ j h
      · obtain rfl | rfl : j = 2 * k ∨ j = 2 * k + 1 := by omega_arith
        · rw [w0]; exact W₄
        · exact W₅
    · have hd : dval u.mem base acc (2 * k) = dval s₁.mem base acc (2 * k) := dval_congr low
      have ea := word_digits (w32 s.mem base (a + 4 * k)) (BitVec.isLt _)
      have eb := word_digits (w32 s.mem base (b + 4 * k)) (BitVec.isLt _)
      have em := word_digits (w32 s.mem base (mo + 4 * k)) (BitVec.isLt _)
      have b0 := hdig_lt (w32 s.mem base (b + 4 * k)) 0
      have b1 := hdig_lt (w32 s.mem base (b + 4 * k)) 1
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega_arith, dval, dval, hd, w0, val32_append _ _ _ k 1,
        val32_append _ _ _ k 1, val32_append _ _ _ k 1, show 32 * (k + 1) = 32 * k + 32 by omega_arith, Nat.pow_add,
        show 16 * (2 * k + 1) = 32 * k + 16 by omega_arith, show 16 * (2 * k) = 32 * k by omega_arith, Nat.pow_add]
      simp only [val32, Nat.mul_zero, Nat.add_zero]
      generalize hdig (w32 s.mem base (a + 4 * k)) 0 = a0 at *
      generalize hdig (w32 s.mem base (a + 4 * k)) 1 = a1 at *
      generalize hdig (w32 s.mem base (b + 4 * k)) 0 = b0 at *
      generalize hdig (w32 s.mem base (b + 4 * k)) 1 = b1 at *
      generalize hdig (w32 s.mem base (mo + 4 * k)) 0 = m0 at *
      generalize hdig (w32 s.mem base (mo + 4 * k)) 1 = m1 at *
      have hw : w32 s₄.mem base (acc + 4 * (2 * k)) + 2 ^ 16 * w32 u.mem base (acc + 4 * (2 * k + 1)) +
          2 ^ 32 * (u.gpr .r3).toNat + w32 s.mem base (b + 4 * k) + 1 =
          w32 s.mem base (a + 4 * k) + w32 s.mem base (mo + 4 * k) + 2 ^ 32 + (s₁.gpr .r3).toNat := by omega_arith
      clear V₄ V₅ ea eb em
      generalize 2 ^ (32 * k) = P at *
      grind

/-! ## The operations -/

theorem addR_eq (M : Mod) (acc o a b : Nat) (ra rb ro : Reg) : addR M acc o a b ra rb ro =
    ([mask16, .mov .r3 (.imm 0)] : List Instr) ++ addK acc ra a rb b (words M) ++
      ([.str .r3 wb (acc + 4 * digits M)] : List Instr) ++ csub M acc ro o :=
  rfl

theorem subR_eq (M : Mod) (acc o a b : Nat) (ra rb ro : Reg) : subR M acc o a b ra rb ro =
    ([mask16, .mov .r3 (.imm 1)] : List Instr) ++ subK acc ra a rb b M.mo (words M) ++
      ([.dp .sub .r3 .r3 (.imm 1), .str .r3 wb (acc + 4 * digits M)] : List Instr) ++ csub M acc ro o :=
  rfl

/-- Where an operation's numbers are read and written: `[ra + ia]`,
`[rb + ib]` and `[ro + io]`, with each register `k` bytes into the working
space, so that the numbers are `a`, `b` and `o` bytes into it. -/
structure Ptrs (s : State) (ra rb ro : Reg) (ia ib io a b o : Nat) where
  ka : Nat
  kb : Nat
  ko : Nat
  ra : s.gpr ra = s.gpr .r12 + BitVec.ofNat 32 ka
  rb : s.gpr rb = s.gpr .r12 + BitVec.ofNat 32 kb
  ro : s.gpr ro = s.gpr .r12 + BitVec.ofNat 32 ko
  a : ka + ia = a
  b : kb + ib = b
  o : ko + io = o

/-- The numbers read and written through `r12` itself. -/
def Ptrs.base (s : State) (a b o : Nat) : Ptrs s .r12 .r12 .r12 a b o a b o :=
  ⟨0, 0, 0, by simp, by simp, by simp, Nat.zero_add _, Nat.zero_add _, Nat.zero_add _⟩

/-- `[o] = [a] [b] R⁻¹ mod m`, with `[a]`, `[b]` and `[o]` at `[ra + ia]`,
`[rb + ib]` and `[ro + io]`. -/
theorem mulR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    {ra rb ro : Reg} {ia ib io : Nat} (hP : Ptrs s ra rb ro ia ib io a b o) (hra : ra ∉ [.r0, .r6, .r7])
    (hrb : rb ∉ rowClob) (hro : ro ∉ clob)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mulR M acc io ia ib ra rb ro) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hW2 : W = 2 * M.n := hW ▸ rfl
  have hD : digits M = 2 * W := by rw [hW2, digits]; omega_arith
  have hacc : accLen M = 4 * (4 * W + 2) := by rw [accLen, hD]; omega_arith
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0; have := hs.small
  have hm0 := m_pos_of_inv hM.inv
  have hmv : val32 s.mem base M.mo W = m := by rw [hW2, ← wordsVal_eq_val32]; exact hM.val
  have hBv : val32 s.mem base b W < m := by rw [hW2, ← wordsVal_eq_val32]; exact hB
  have hML : MulLay W size acc a b M.mo :=
    ⟨by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith, by omega_arith⟩
  have himm : encodable (BitVec.ofNat 32 W) = true := hW ▸ words_encodable (by omega_arith)
  simp only [mulR, hW, hD]
  refine WP.seq (zeros_ok hs (k := 2 * (2 * W) + 2) (by omega_arith) fun s₁ O₁ Z₁ K₁ => ?_)
  refine wp_movw fun s₂ u₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm himm) fun s₅ u₅ => WP.block_nil ?_
  have K₅ : Rest rowClob s s₅ := (K₁.mono (by simp [rowClob])).trans ((u₂.rest (by simp [rowClob])).trans
    ((u₃.rest (by simp [rowClob])).trans ((u₄.rest (by simp [rowClob])).trans (u₅.rest (by simp [rowClob])))))
  have hs₅ := hs.of_rest K₅ (by decide)
  have mem₅ : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have O₅ : Outside base acc (4 * (4 * W + 2)) s.mem s₅.mem := by
    rw [mem₅]
    exact O₁.mono (Nat.le_refl _) (by omega_arith)
  have Z₅ : ∀ j < 4 * W + 2, w32 s₅.mem base (acc + 4 * j) = 0 := fun j hj => by
    rw [mem₅]; exact Z₁ j (by omega_arith)
  have hm₅ : val32 s₅.mem base M.mo W = m := by rw [O₅.val32 (by omega_arith) (by omega_arith), hmv]
  have hB₅ : val32 s₅.mem base b W < m := by rw [O₅.val32 (by omega_arith) (by omega_arith)]; exact hBv
  have r12₅ : s₅.gpr .r12 = s₂.gpr .r12 := by rw [u₅.other _ (by decide), u₄.other _ (by decide),
    u₃.other _ (by decide)]
  have hz : dval s₅.mem base (acc + 4 * (2 * 0)) (2 * W + 2) = 0 := dval_zero fun j hj => by
    rw [show acc + 4 * (2 * 0) + 4 * j = acc + 4 * j by omega_arith]; exact Z₅ j (by omega_arith)
  have I₀ : LoopInv base W acc hP.ka a b m 0 s₅ s₅ := by
    refine ⟨?_, ?_, ?_, ?_, VG.Proof.Mont.Outside.refl _ _ _ _, Rest.refl _ _, fun j hj => ?_, fun l h₁ h₂ => ?_,
      by rw [hz]; omega_arith, ⟨0, by rw [hz]; simp only [Nat.mul_zero, pval, Nat.zero_mul, Nat.add_zero]⟩⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, r12₅]; exact (BitVec.add_zero _).symm
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (fun h => hra (by simp [h])), u₂.other _ (fun h => hra (by simp [h])),
        K₁.gpr _ (fun h => hra (by simp at h; simp [h])), hP.ra, K₅.gpr .r12 (by decide), Nat.mul_zero, Nat.add_zero]
    · rw [u₅.gpr, Nat.sub_zero]
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    · rw [show acc + 4 * (2 * 0) + 4 * j = acc + 4 * j by omega_arith, Z₅ j (by omega_arith)]; decide
    · exact Z₅ l h₂
  have hb₅ : s₅.gpr rb = s₅.gpr .r12 + BitVec.ofNat 32 hP.kb := by
    rw [K₅.gpr _ hrb, K₅.gpr _ (by decide)]; exact hP.rb
  refine WP.seq (WP.mono (loop_ok hs₅ hP.a hb₅ hP.b hrb hW hD hML (by omega_arith) (by omega_arith) hm₅
    (minv16_inv hM.inv) hB₅ I₀) fun t I => ?_)
  have hot : t.gpr ro = t.gpr .r12 + BitVec.ofNat 32 hP.ko := by
    rw [(K₅.trans I.rest).gpr _ (not_mem_rowClob hro), (K₅.trans I.rest).gpr _ (by decide)]; exact hP.ro
  have ht := hs₅.of_rest I.rest (by decide)
  have hmt : val32 t.mem base M.mo W = m := by rw [I.out.val32 (by omega_arith) (by omega_arith), hm₅]
  -- The window's top digit is zero.
  have hmP : m < 2 ^ (32 * W) := by rw [← hmv]; exact val32_lt _ _ _ _
  have htop : dval t.mem base (acc + 4 * (2 * W)) (2 * W + 2) = dval t.mem base (acc + 4 * (2 * W)) (2 * W + 1) := by
    have hlt := I.lt
    rw [dval] at hlt ⊢
    have hp : 2 ^ (32 * W) * 2 ≤ 2 ^ (16 * (2 * W + 1)) := by
      rw [show 16 * (2 * W + 1) = 32 * W + 16 by omega_arith, Nat.pow_add]
      exact Nat.mul_le_mul_left _ (by decide)
    rcases Nat.eq_zero_or_pos (w32 t.mem base (acc + 4 * (2 * W) + 4 * (2 * W + 1))) with h | h
    · rw [h, Nat.zero_mul, Nat.add_zero]
    · have := Nat.mul_le_mul_right (2 ^ (16 * (2 * W + 1))) h
      omega_arith
  have hV : dval t.mem base (acc + 4 * (2 * W)) (2 * W + 1) < 2 * m := htop ▸ I.lt
  refine WP.mono (csub_ok ht hot hP.o hro hW hD (src := acc + 4 * (2 * W)) (o := o)
    (by omega_using [hacc, hL.acc_le])
    (by omega_using [hW2, hL.o_le])
    (by omega_using [hW2, hM.tmp])
    (by omega_using [hW2, hM.mo])
    (by omega_using [hW2, hacc, hL.acc_tmp])
    (by omega_using [hW2, hM.sep])
    (by omega_using [hW2, hacc, hL.acc_o])
    (by omega_using [hW2, hL.o_tmp]) hmt hm0 (I.digs.mono (by omega_arith)) hV)
    fun u ⟨O, V, K⟩ => ⟨⟨((K₅.trans I.rest).mono (by simp [rowClob, clob])).trans (K.mono (by simp [clob])), ?_⟩, ?_, ?_⟩
  · have O₅' : Outside base acc (accLen M) s.mem s₅.mem := by rw [hacc]; exact O₅
    have Ot : Outside base acc (accLen M) s₅.mem t.mem := by rw [hacc]; exact I.out
    refine ((Outs.of_outside O₅' (by simp)).trans (Outs.of_outside Ot (by simp))).trans ?_
    rw [show 4 * W = 8 * M.n by omega_arith] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, ← hW2, V]; exact Nat.mod_lt _ hm0
  · obtain ⟨U, hU⟩ := I.cong
    rw [htop, pval_words] at hU
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hW2, V,
      show 64 * M.n = 32 * W by omega_arith, ← O₅.val32 (d := a) (by omega_arith) (by omega_arith),
      ← O₅.val32 (d := b) (by omega_arith) (by omega_arith), Nat.mod_mul_mod, Nat.mul_comm, hU, Nat.add_mul_mod_self_right]

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mul_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (mul M acc o a b) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m :=
  mulR_ok hs hM hL (Ptrs.base s a b o) (by decide) (by decide) (by decide) hB

/-- `[o] = [a] + [b] mod m`, with `[a]`, `[b]` and `[o]` at `[ra + ia]`,
`[rb + ib]` and `[ro + io]`. -/
theorem addR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    {ra rb ro : Reg} {ia ib io : Nat} (hP : Ptrs s ra rb ro ia ib io a b o)
    (hra : ra ∉ [.r3, .r4, .r5, .r6, .r7, .r8, .r9]) (hrb : rb ∉ [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (hro : ro ∉ clob)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (addR M acc io ia ib ra rb ro)) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hW2 : W = 2 * M.n := hW ▸ rfl
  have hD : digits M = 2 * W := by rw [hW2, digits]; omega_arith
  have hacc : accLen M = 4 * (4 * W + 2) := by rw [accLen, hD]; omega_arith
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0
  have hm0 := m_pos_of_inv hM.inv
  rw [addR_eq, hW, hD]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have K₂ : Rest clob s s₂ := (u₁.rest (by simp [clob])).trans (u₂.rest (by simp [clob]))
  have hs₂ := hs.of_rest K₂ (by decide)
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [u₂.other _ (by decide), u₁.gpr]
  have mem₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have c₂ : (s₂.gpr .r3).toNat = 0 := by rw [u₂.gpr]; rfl
  have r12₂ : s₂.gpr .r12 = s.gpr .r12 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have hra₂ : s₂.gpr ra = s₂.gpr .r12 + BitVec.ofNat 32 hP.ka := by
    rw [u₂.other _ (ne_of_not_mem hra), u₁.other _ (ne_of_not_mem hra), r12₂]; exact hP.ra
  have hrb₂ : s₂.gpr rb = s₂.gpr .r12 + BitVec.ofNat 32 hP.kb := by
    rw [u₂.other _ (ne_of_not_mem hrb), u₁.other _ (ne_of_not_mem hrb), r12₂]; exact hP.rb
  refine VG.Proof.X25519.Arm.WP.append (addK_ok hs₂ (a := a) (b := b) (acc := acc) hra₂ hP.a hrb₂ hP.b
    (not_mem_sub hra) (not_mem_sub hrb) h6₂ (by omega_arith) (k := W)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨O₃, D₃, C₃, V₃, K₃⟩ => ?_
  have K₂₃ := K₂.trans (K₃.mono (by simp [clob]))
  have hs₃ := hs.of_rest K₂₃ (by decide)
  refine wp_str (hs.off_lt (by omega_arith)) (hs₃.ea (by omega_arith)) (hs₃.write (d := acc + 4 * (2 * W)) (n := 4) (by omega_arith))
    fun s₄ m₄ => ?_
  have hs₄ := hs₃.of_rest (m₄.rest []) (by decide)
  rw [mem₂, c₂, Nat.add_zero] at V₃
  rw [mem₂] at O₃
  have O₄ : Outside base acc (4 * (2 * W + 1)) s.mem s₄.mem := by
    rw [m₄.mem]
    exact (O₃.mono (Nat.le_refl _) (by omega_arith)).trans ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  have low : ∀ j < 2 * W, w32 s₄.mem base (acc + 4 * j) = w32 s₃.mem base (acc + 4 * j) := fun j hj => by
    rw [m₄.mem, w32_write_ne hn (size := size) (by omega_arith) (by omega_arith) (by omega_arith)]
  have top : w32 s₄.mem base (acc + 4 * (2 * W)) = (s₃.gpr .r3).toNat := by rw [m₄.mem, w32_write_self]
  have hsum : dval s₄.mem base acc (2 * W + 1) = val32 s.mem base a W + val32 s.mem base b W := by
    rw [dval, dval_congr low, top, show 16 * (2 * W) = 32 * W by omega_arith, Nat.mul_comm ((s₃.gpr .r3).toNat), ← V₃]
  have hd₄ : Digs s₄.mem base acc (2 * W + 1) := fun j hj => by
    rcases Nat.lt_or_ge j (2 * W) with h | h
    · rw [low j h]; exact D₃ j h
    · rw [show j = 2 * W by omega_arith, top]; omega_arith
  have hA : val32 s.mem base a W + val32 s.mem base b W < 2 * m := by
    rw [hW2, ← wordsVal_eq_val32, ← wordsVal_eq_val32]; exact hAB
  have hm₄ : val32 s₄.mem base M.mo W = m := by
    rw [O₄.val32 (by omega_arith) (by omega_arith), hW2, ← wordsVal_eq_val32]; exact hM.val
  have hro₄ : s₄.gpr ro = s₄.gpr .r12 + BitVec.ofNat 32 hP.ko := by
    rw [(K₂₃.trans (m₄.rest _)).gpr _ hro, (K₂₃.trans (m₄.rest _)).gpr _ (by decide)]; exact hP.ro
  refine WP.mono (csub_ok hs₄ hro₄ hP.o hro hW hD (src := acc) (o := o)
    (by omega_using [hacc, hL.acc_le])
    (by omega_using [hW2, hL.o_le])
    (by omega_using [hW2, hM.tmp])
    (by omega_using [hW2, hM.mo])
    (by omega_using [hW2, hacc, hL.acc_tmp])
    (by omega_using [hW2, hM.sep])
    (by omega_using [hW2, hacc, hL.acc_o])
    (by omega_using [hW2, hL.o_tmp]) hm₄ hm0 hd₄ (by rw [hsum]; exact hA)) fun u ⟨O, V, K⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · exact (K₂₃.trans (m₄.rest _)).trans (K.mono (by simp [clob]))
  · have O₄' : Outside base acc (accLen M) s.mem s₄.mem := O₄.mono (Nat.le_refl _) (by omega_arith)
    refine (Outs.of_outside O₄' (by simp)).trans ?_
    rw [show 4 * W = 8 * M.n by omega_arith] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hW2, V, hsum]

/-- `[o] = [a] + [b] mod m`. -/
theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (add M acc o a b)) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m :=
  addR_ok hs hM hL (Ptrs.base s a b o) (by decide) (by decide) (by decide) hAB

/-- `[o] = [a] - [b] mod m`, with `[a]`, `[b]` and `[o]` at `[ra + ia]`,
`[rb + ib]` and `[ro + io]`. -/
theorem subR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    {ra rb ro : Reg} {ia ib io : Nat} (hP : Ptrs s ra rb ro ia ib io a b o)
    (hra : ra ∉ [.r3, .r4, .r5, .r6, .r7, .r8, .r9]) (hrb : rb ∉ [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (hro : ro ∉ clob)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (subR M acc io ia ib ra rb ro)) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  have hW2 : W = 2 * M.n := hW ▸ rfl
  have hD : digits M = 2 * W := by rw [hW2, digits]; omega_arith
  have hacc : accLen M = 4 * (4 * W + 2) := by rw [accLen, hD]; omega_arith
  have := hL.acc_le; have := hL.o_le; have := hL.a_le; have := hL.b_le; have := hL.acc_o; have := hL.acc_a
  have := hL.acc_b; have := hL.acc_mo; have := hL.acc_tmp; have := hL.o_tmp
  have := hM.mo; have := hM.tmp; have := hM.sep; have := hM.n0
  have hm0 := m_pos_of_inv hM.inv
  have hmv : val32 s.mem base M.mo W = m := by rw [hW2, ← wordsVal_eq_val32]; exact hM.val
  have hAv : val32 s.mem base a W < m := by rw [hW2, ← wordsVal_eq_val32]; exact hA
  have hBv : val32 s.mem base b W < m := by rw [hW2, ← wordsVal_eq_val32]; exact hB
  have hmP : m < 2 ^ (32 * W) := by rw [← hmv]; exact val32_lt _ _ _ _
  rw [subR_eq, hW, hD]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have K₂ : Rest clob s s₂ := (u₁.rest (by simp [clob])).trans (u₂.rest (by simp [clob]))
  have hs₂ := hs.of_rest K₂ (by decide)
  have h6₂ : s₂.gpr .r6 = VG.Proof.X25519.Arm.mask16 := by rw [u₂.other _ (by decide), u₁.gpr]
  have mem₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have c₂ : (s₂.gpr .r3).toNat = 1 := by rw [u₂.gpr]; rfl
  have r12₂ : s₂.gpr .r12 = s.gpr .r12 := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  have hra₂ : s₂.gpr ra = s₂.gpr .r12 + BitVec.ofNat 32 hP.ka := by
    rw [u₂.other _ (ne_of_not_mem hra), u₁.other _ (ne_of_not_mem hra), r12₂]; exact hP.ra
  have hrb₂ : s₂.gpr rb = s₂.gpr .r12 + BitVec.ofNat 32 hP.kb := by
    rw [u₂.other _ (ne_of_not_mem hrb), u₁.other _ (ne_of_not_mem hrb), r12₂]; exact hP.rb
  refine VG.Proof.X25519.Arm.WP.append (subK_ok hs₂ (a := a) (b := b) (mo := M.mo) (acc := acc) hra₂ hP.a hrb₂ hP.b
    (not_mem_sub hra) (not_mem_sub hrb) h6₂ (by omega_arith)
    (k := W) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨O₃, D₃, C₃, V₃, K₃⟩ => ?_
  rw [mem₂, c₂, hmv] at V₃
  rw [mem₂] at O₃
  have hT : dval s₃.mem base acc (2 * W) < 2 ^ (32 * W) := by
    rw [show 32 * W = 16 * (2 * W) by omega_arith]; exact dval_lt D₃
  have hc1 : 1 ≤ (s₃.gpr .r3).toNat := by
    rcases Nat.eq_zero_or_pos (s₃.gpr .r3).toNat with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at V₃; omega_arith
    · exact h
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => ?_
  have K₂₄ := (K₂.trans (K₃.mono (by simp [clob]))).trans (u₄.rest (by simp [clob]))
  have hs₄ := hs.of_rest K₂₄ (by decide)
  have r3₄ : (s₄.gpr .r3).toNat = (s₃.gpr .r3).toNat - 1 := by
    rw [u₄.gpr, dpVal, VG.Proof.X25519.Arm.toNat_sub_le (by exact hc1)]; rfl
  refine wp_str (hs.off_lt (by omega_arith)) (hs₄.ea (by omega_arith)) (hs₄.write (d := acc + 4 * (2 * W)) (n := 4) (by omega_arith))
    fun s₅ m₅ => ?_
  have hs₅ := hs₄.of_rest (m₅.rest []) (by decide)
  have mem₄ : s₄.mem = s₃.mem := u₄.mem
  have O₅ : Outside base acc (4 * (2 * W + 1)) s.mem s₅.mem := by
    rw [m₅.mem, mem₄]
    exact (O₃.mono (Nat.le_refl _) (by omega_arith)).trans ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  have low : ∀ j < 2 * W, w32 s₅.mem base (acc + 4 * j) = w32 s₃.mem base (acc + 4 * j) := fun j hj => by
    rw [m₅.mem, mem₄, w32_write_ne hn (size := size) (by omega_arith) (by omega_arith) (by omega_arith)]
  have top : w32 s₅.mem base (acc + 4 * (2 * W)) = (s₃.gpr .r3).toNat - 1 := by
    rw [m₅.mem, w32_write_self, r3₄]
  have hdiff : dval s₅.mem base acc (2 * W + 1) = val32 s.mem base a W + m - val32 s.mem base b W := by
    rw [dval, dval_congr low, top, show 16 * (2 * W) = 32 * W by omega_arith]
    have e : ((s₃.gpr .r3).toNat - 1) * 2 ^ (32 * W) + 2 ^ (32 * W) = 2 ^ (32 * W) * (s₃.gpr .r3).toNat := by
      rw [Nat.mul_comm, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hc1]
    omega_arith
  have hd₅ : Digs s₅.mem base acc (2 * W + 1) := fun j hj => by
    rcases Nat.lt_or_ge j (2 * W) with h | h
    · rw [low j h]; exact D₃ j h
    · rw [show j = 2 * W by omega_arith, top]; omega_arith
  have hm₅ : val32 s₅.mem base M.mo W = m := by rw [O₅.val32 (by omega_arith) (by omega_arith), hmv]
  have hro₅ : s₅.gpr ro = s₅.gpr .r12 + BitVec.ofNat 32 hP.ko := by
    rw [(K₂₄.trans (m₅.rest _)).gpr _ hro, (K₂₄.trans (m₅.rest _)).gpr _ (by decide)]; exact hP.ro
  refine WP.mono (csub_ok hs₅ hro₅ hP.o hro hW hD (src := acc) (o := o)
    (by omega_using [hacc, hL.acc_le])
    (by omega_using [hW2, hL.o_le])
    (by omega_using [hW2, hM.tmp])
    (by omega_using [hW2, hM.mo])
    (by omega_using [hW2, hacc, hL.acc_tmp])
    (by omega_using [hW2, hM.sep])
    (by omega_using [hW2, hacc, hL.acc_o])
    (by omega_using [hW2, hL.o_tmp]) hm₅ hm0 hd₅ (by rw [hdiff]; omega_arith)) fun u ⟨O, V, K⟩ => ⟨⟨?_, ?_⟩, ?_⟩
  · exact (K₂₄.trans (m₅.rest _)).trans (K.mono (by simp [clob]))
  · have O₅' : Outside base acc (accLen M) s.mem s₅.mem := O₅.mono (Nat.le_refl _) (by omega_arith)
    refine (Outs.of_outside O₅' (by simp)).trans ?_
    rw [show 4 * W = 8 * M.n by omega_arith] at O
    exact O.mono (by simp)
  · rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32, ← hW2, V, hdiff]

/-- `[o] = [a] - [b] mod m`. -/
theorem sub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub M acc o a b)) s fun s' => OpKeep M base acc o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m :=
  subR_ok hs hM hL (Ptrs.base s a b o) (by decide) (by decide) (by decide) hA hB

end VG.Proof.Mont.Arm
