module

import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Mont.X86_64.Rounds
import VerifiedGarbage.Proof.Mont.X86_64.Blocks
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Mont.X86_64.ProdX
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.MulS
import VerifiedGarbage.Proof.Mont.X86_64.SqrM
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Mont.X86_64.Friendly
import VerifiedGarbage.Proof.Mont.X86_64.Round

/-! ### `Mont.X86_64.OpsReg`, which this module and modules that import it used -/

section

/-!
# Montgomery arithmetic on x86-64: the operations with the accumulator in registers

For a modulus `m` of at most six words in the working space (`ModOk`):
`mulR o a b` writes `[a] [b] R⁻¹ mod m` to `[o]` (`mulR_ok`), `addR` writes
`[a] + [b] mod m` (`addR_ok`) and `subR` writes `[a] - [b] mod m`
(`subR_ok`), for `[a]`, `[b]` below `m`. Each changes only the registers
`clob n`, the result and the temporary area (`OpKeep`). `Ops.lean` states
them for any number of words.
-/

@[expose] public section

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The registers the operations change: for four words, also `r14` and `r15`
(`sqrRX`'s). -/
def clob (n : Nat) : List Reg := .rax :: .rcx :: .rdx :: .rbp :: acc n ++ if n = 4 then [.r14, .r15] else []

theorem mem_clob {n : Nat} {r : Reg} (h : r ∈ .rax :: .rcx :: .rdx :: .rbp :: acc n) : r ∈ clob n :=
  List.mem_append_left _ h

/-- What an operation writing `[o]` keeps: the registers but `clob`, the
regions, and the memory but `[o]` and the temporary area. -/
structure OpKeep (M : Mod) (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob M.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : ∀ x, (ofs base x < o ∨ o + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

theorem fresh_low (n : Nat) (hn : n < 7) :
    Fresh (win n n n :: (List.range n).map (win n n)) := by
  have h := fresh_wins hn n
  rw [wins_split] at h
  refine ⟨?_, fun t ht => h.2 t ?_⟩
  · have hd := h.1
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false] at hd
    exact List.nodup_cons.mpr ⟨fun hm => hd.2.2 _ hm _ (by simp) rfl, hd.1⟩
  · simp only [List.mem_cons, List.mem_append] at ht ⊢
    grind

theorem fresh_low' (n : Nat) (hn : n < 7) : Fresh ((List.range n).map (win n n)) :=
  (fresh_low n hn).tail

/-- `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mulR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mulR M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn := hs.nowrap
  rw [mulR]
  split
  · -- A product by `mulRX` or `sqrRX`.
    rename_i k hk
    unfold prodK? at hk
    split at hk
    · rename_i hc
      obtain ⟨-, h4⟩ := hc
      split at hk
      · rename_i ws hr
        have fin : ∀ s', KeepRegs sqrClob s s' →
            (∀ x, (ofs base x < o ∨ o + 32 ≤ ofs base x) →
              (ofs base x < M.tmp ∨ M.tmp + 32 ≤ ofs base x) → s'.mem x = s.mem x) →
            OpKeep M base o s s' := fun s' kr hmem =>
          ⟨fun r hr' => kr.gpr r fun h => hr' (h4 ▸ (by decide : ∀ q ∈ sqrClob, q ∈ clob 4) r h),
            kr.rd, kr.wr, fun x hx hx' => hmem x (by rw [h4] at hx; exact hx) (by rw [h4] at hx'; exact hx')⟩
        rw [h4]
        split
        · rename_i hab
          subst hab
          exact WP.mono (sqrRX_ok hs hM h4 hr hk (by omega_arith) (by omega_arith) (h4 ▸ hB))
            fun s' ⟨kr, hmem, hlt, he⟩ => ⟨fin s' kr hmem, hlt, he⟩
        · exact WP.mono (mulRX_ok hs hM h4 hr hk (by omega_arith) (by omega_arith) (by omega_arith) (h4 ▸ hB))
            fun s' ⟨kr, hmem, hlt, he⟩ => ⟨fin s' kr hmem, hlt, he⟩
      · cases hk
    · cases hk
  dsimp only
  split
  · -- P-384's squaring.
    rename_i hc
    obtain ⟨hsp, -, rfl⟩ := hc
    obtain ⟨h6, -⟩ := Mod.ok_sparse hM.red hsp
    rw [h6] at ho ha hoT haT hoM hB ⊢
    refine WP.mono (sqrS_ok hs hM hsp ho ha hoT haT hoM hB) fun s' ⟨kr, hmem, hlt, he⟩ =>
      ⟨⟨fun r hr => kr.gpr r (not_mem_of hr (by rw [h6]; decide)), kr.rd, kr.wr,
        fun x hx hx' => hmem x (by rw [h6] at hx; exact hx) (by rw [h6] at hx'; exact hx')⟩, hlt, he⟩
  rw [mulG, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulRounds_ok hs hM.toR ha hb hB) fun s₂ ⟨⟨U, eU⟩, hT, k₂⟩ => ?_
  have hs₂ := hs.of_keeps k₂ (by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (acc_regs_lt _ hM.n7 _ h).2.2.2.2 rfl)
  have hmem₂ : s₂.mem = s.mem := k₂.2.1
  -- The accumulator's value as `csub` sees it: its top word is zero.
  have hsplit := wins_split M.n M.n
  have hmX : m < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have hlowlen : ((List.range M.n).map (win M.n M.n)).length = M.n := by simp
  have hV : regsVal s₂ ((List.range M.n).map (win M.n M.n)) +
      2 ^ (64 * M.n) * (s₂.gpr (win M.n M.n M.n)).toNat = regsVal s₂ (wins M.n M.n) := by
    rw [hsplit, regsVal_append, hlowlen]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [hsplit, regsVal_append, hlowlen] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have : (s₂.gpr (win M.n M.n (M.n + 1))).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * M.n) * 2 ^ 64 ≤ 2 ^ (64 * M.n) * ((s₂.gpr (win M.n M.n M.n)).toNat +
          2 ^ 64 * (s₂.gpr (win M.n M.n (M.n + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega_arith)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero]
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₂ (M := M) (m := m) hlowlen hM.n0 (fresh_low M.n hM.n7) hM.mo hM.tmp hM.sep
    (Mod.ok_sparse hM.red)
    (by rw [hmem₂]; exact hM.val) (by rw [hV]; exact hT)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact (fresh_low M.n hM.n7).head.2.2.2.2.2 h.symm
    · exact (fresh_low' M.n hM.n7).2 _ h |>.2.2.2.2 rfl)
  refine WP.mono (stores_ok _ hs₃ (o := o) (by rw [hlowlen]; omega_arith) (fresh_low' M.n hM.n7).1)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [hlowlen] at e₄ O₄
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · rw [k₄.gpr r (by simp), k₃.gpr r (fun h => hr (by
      refine mem_clob ?_
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (wins_sub_acc hM.n7 M.n r (by
          rw [hsplit]; simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (wins_sub_acc hM.n7 M.n r (by
          rw [hsplit]; simp only [List.mem_append]; exact Or.inl h))))))),
      k₂.1 r (fun h => hr (mem_clob (by simpa using h)))]
  · rw [k₄.rd, k₃.rd, k₂.2.2.1]
  · rw [k₄.wr, k₃.wr, k₂.2.2.2]
  · rw [O₄ x hx, O₃ x hx', hmem₂]
  · rw [e₄, e₃, hV]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₄, e₃, hV, Nat.mod_mul_mod, Nat.mul_comm, eU, ← hmem₂]
    simp only [Nat.add_mul_mod_self_right]

/-! ## Addition and subtraction -/

theorem low_len_lt : ∀ n < 7, (low n).length = n := by decide

theorem low_nodup_lt : ∀ n < 7, (top n :: low n).Nodup := by decide

theorem low_regs_lt : ∀ n < 7, ∀ t ∈ top n :: low n, t ≠ .rax ∧ t ≠ .rcx ∧ t ≠ .rdx := by decide

theorem low_regs_lt' : ∀ n < 7, ∀ t ∈ top n :: low n, t ≠ .rbp ∧ t ≠ .rdi := by decide

theorem low_sub_acc_lt : ∀ n < 7, ∀ t ∈ top n :: low n, t ∈ acc n := by decide

theorem fresh_top_low {n : Nat} (hn : n < 7) : Fresh (top n :: low n) :=
  ⟨low_nodup_lt n hn, fun t ht =>
    have h := low_regs_lt n hn t ht
    have h' := low_regs_lt' n hn t ht
    ⟨h.1, h.2.1, h.2.2, h'.1, h'.2⟩⟩

theorem low_ne_nil {n : Nat} (hn : n < 7) (h0 : 0 < n) : ∃ t ts, low n = t :: ts := by
  have := low_len_lt n hn
  cases h : low n with
  | nil => rw [h] at this; simp at this; omega_arith
  | cons t ts => exact ⟨t, ts, rfl⟩

/-- `[o] = [a] + [b] mod m`. -/
theorem addR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (addR M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  have hf := fresh_top_low hM.n7
  have hl := low_len_lt M.n hM.n7
  obtain ⟨t, ts, hts⟩ := low_ne_nil hM.n7 hM.n0
  have hsub : ∀ r ∈ top M.n :: low M.n, r ∈ clob M.n := fun r hr => by
    exact mem_clob (by
      simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (low_sub_acc_lt _ hM.n7 r hr)))))
  rw [addR, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok (low M.n) hs (a := a) (by omega_arith) hf.tail) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  rw [WP.block_append_iff]
  refine WP.mono (mov32zero_ok s₁ (top M.n)) fun s₂ ⟨z₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by simp [(hf.2 _ (List.mem_cons_self ..)).2.2.2.2.symm])
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainAdd_ok hs₂ (b := b) (by rw [← hts]; omega_arith) (hts ▸ hf.tail))
    fun s₃ ⟨c, c₃, e₃, k₃⟩ => ?_
  rw [← hts] at e₃ k₃ ⊢
  have hs₃ := hs₂.of_keeps k₃ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  have ht₃ : s₃.gpr (top M.n) = 0 := by
    rw [k₃.1 _ (List.nodup_cons.mp hf.1).1, z₂]
  rw [WP.block_append_iff]
  refine WP.mono (adcZero_ok s₃ (top M.n) c₃ ht₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by simp [(hf.2 _ (List.mem_cons_self ..)).2.2.2.2.symm])
  have hR₄ : regsVal s₄ (low M.n) = regsVal s₃ (low M.n) :=
    regsVal_congr fun q hq => k₄.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (List.nodup_cons.mp hf.1).1 (h ▸ hq))
  have hR₂ : regsVal s₂ (low M.n) = regsVal s₁ (low M.n) :=
    regsVal_congr fun q hq => k₂.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (List.nodup_cons.mp hf.1).1 (h ▸ hq))
  have hmem₄ : s₄.mem = s.mem := by rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  rw [hl, hR₂, e₁, k₂.2.1, k₁.2.1] at e₃
  have hV : regsVal s₄ (low M.n) + 2 ^ (64 * M.n) * (s₄.gpr (top M.n)).toNat =
      wordsVal s.mem base a M.n + wordsVal s.mem base b M.n := by rw [hR₄, e₄, e₃, hl]
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₄ (M := M) (m := m) hl hM.n0 hf hM.mo hM.tmp hM.sep
    (Mod.ok_sparse hM.red)
    (by rw [hmem₄]; exact hM.val) (by rw [hV]; exact hAB)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h | h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact hf.head.2.2.2.2.2 h.symm
    · exact (hf.tail.2 _ h).2.2.2.2 rfl)
  refine WP.mono (stores_ok _ hs₅ (o := o) (by rw [hl]; omega_arith) hf.tail.1) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₆ O₆
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_⟩
  · have hr' : r ∉ top M.n :: low M.n := fun h => hr (hsub r h)
    rw [k₆.gpr r (by simp), k₅.gpr r (fun h => hr (by
        simp only [List.mem_cons] at h
        rcases h with h | h | h | h | h | h
        · simp [clob, h]
        · simp [clob, h]
        · simp [clob, h]
        · simp [clob, h]
        · exact hsub r (by rw [h]; exact List.mem_cons_self ..)
        · exact hsub r (List.mem_cons_of_mem _ h))),
      k₄.1 r (fun h => hr' (by simp at h; simp [h])), k₃.1 r (fun h => hr' (List.mem_cons_of_mem _ h)),
      k₂.1 r (fun h => hr' (by simp at h; simp [h])), k₁.1 r (fun h => hr' (List.mem_cons_of_mem _ h))]
  · rw [k₆.rd, k₅.rd, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₆.wr, k₅.wr, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₆ x hx, O₅ x hx', hmem₄]
  · rw [e₆, e₅, hV]

/-- `[tmp] = [mo]` masked with `rax` (all ones if `c`, else zero), `k` words. -/
theorem masked_ok {size : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {mo tmp : Nat} (c : Bool),
    Scr s base size → mo + 8 * k ≤ size → tmp + 8 * k ≤ size →
    (mo + 8 * k ≤ tmp ∨ tmp + 8 * k ≤ mo) → s.gpr .rax = (if c then BitVec.allOnes 64 else 0) →
    WP isa (.block (masked k mo tmp)) s fun s' =>
      wordsVal s'.mem base tmp k = (if c then wordsVal s.mem base mo k else 0) ∧
      KeepRegs [.rdx] s s' ∧ Outside base tmp (8 * k) s.mem s'.mem
  | 0, s, _, _, _, c, _, _, _, _, _ => WP.block_nil ⟨by cases c <;> rfl, ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, s, base, mo, tmp, c, hs, hmo, htmp, hsep, hx => by
    have hn := hs.nowrap
    rw [masked, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc mo)), .alu .and .rdx (.reg .rax),
        .store (sc tmp) .rdx]) s (fun s₁ => s₁.mem = s.mem.writeW (off base tmp)
          (if c then word s.mem base mo else 0) ∧ KeepRegs [.rdx] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
        Option.map_some, State.load64, State.store64, ea_sc, RegUpd.gpr_setReg,
        RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
        RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, reduceCtorEq, ite_true,
        ite_false, hs.rdi, ld_sc hs (d := mo) (by omega_arith), st_sc hs (d := tmp) (by omega_arith), hx,
        Option.some.injEq, exists_eq_left']
      refine ⟨by cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true, BitVec.and_allOnes,
        BitVec.and_zero, BitVec.ofNat_eq_ofNat], ⟨fun r hr => ?_, rfl, rfl⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨m₁, k₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base tmp 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega_arith)
    refine WP.mono (masked_ok k c hs₁ (mo := mo + 8) (tmp := tmp + 8) (by omega_arith) (by omega_arith)
      (by omega_arith) (by rw [k₁.gpr _ (by decide), hx])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    refine ⟨?_, k₁.trans k₂, fun x hx => by rw [O₂ x (by omega_arith), O₁ x (by omega_arith)]⟩
    rw [wordsVal, O₂.word (by omega_arith) (by omega_arith), m₁, word_writeW_self, e₂,
      O₁.wordsVal (by omega_arith) (by omega_arith)]
    cases c <;> simp [wordsVal]

/-- `[o] = [a] - [b] mod m`. -/
theorem subR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) {o a b : Nat} (ho : o + 8 * M.n ≤ size)
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (subR M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  have hn := hs.nowrap
  have hf := fresh_top_low hM.n7
  have hl := low_len_lt M.n hM.n7
  have hmX : m < 2 ^ (64 * M.n) := hM.val ▸ wordsVal_lt _ _ _ _
  have htmp := hM.tmp
  obtain ⟨t, ts, hts⟩ := low_ne_nil hM.n7 hM.n0
  have hsub : ∀ r ∈ low M.n, r ∈ clob M.n := fun r hr => by
    refine mem_clob ?_
    simp only [List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (Or.inr (low_sub_acc_lt _ hM.n7 r (List.mem_cons_of_mem _ hr)))))
  rw [subR, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok (low M.n) hs (a := a) (by omega_arith) hf.tail) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainSub_ok hs₁ (b := b) (by rw [← hts]; omega_arith) (hts ▸ hf.tail))
    fun s₂ ⟨c, c₂, e₂, k₂⟩ => ?_
  rw [← hts] at e₂ k₂ ⊢
  have hs₂ := hs₁.of_keeps k₂ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₂ c₂) fun s₃ ⟨x₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (masked_ok M.n c hs₃ (mo := M.mo) (tmp := M.tmp) hM.mo hM.tmp hM.sep x₃)
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [WP.block_append_iff, hts]
  refine WP.mono (chainAdd_ok hs₄ (b := M.tmp) (by rw [← hts]; omega_arith) (hts ▸ hf.tail))
    fun s₅ ⟨c', _, e₅, k₅⟩ => ?_
  rw [← hts] at e₅ k₅ ⊢
  have hs₅ := hs₄.of_keeps k₅ (fun h => (hf.tail.2 _ h).2.2.2.2 rfl)
  refine WP.mono (stores_ok _ hs₅ (o := o) (by rw [hl]; omega_arith) hf.tail.1) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₁ e₂ e₅ e₆ O₆
  have hmem₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1, k₁.2.1]
  have hR₄ : regsVal s₄ (low M.n) = regsVal s₂ (low M.n) := by
    rw [regsVal_congr fun q hq => k₄.gpr q (by simp [(hf.tail.2 q hq).2.2.1]),
      regsVal_congr fun q hq => k₃.1 q (by simp [(hf.tail.2 q hq).1])]
  rw [hR₄, e₄, hmem₃, hM.val] at e₅
  rw [e₁, k₁.2.1] at e₂
  have hmem₄ : ∀ x, (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s₄.mem x = s.mem x :=
    fun x hx => by rw [O₄ x hx, hmem₃]
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_⟩
  · have hr' : r ∉ low M.n := fun h => hr (hsub r h)
    rw [k₆.gpr r (by simp), k₅.1 r hr', k₄.gpr r (fun h => hr (by simp at h; simp [clob, h])),
      k₃.1 r (fun h => hr (by simp at h; simp [clob, h])), k₂.1 r hr', k₁.1 r hr']
  · rw [k₆.rd, k₅.2.2.1, k₄.rd, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₆.wr, k₅.2.2.2, k₄.wr, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₆ x hx, k₅.2.1, hmem₄ x hx']
  · rw [e₆]
    have hR₂ := regsVal_lt s₂ (low M.n)
    have hR₅ := regsVal_lt s₅ (low M.n)
    rw [hl] at hR₂ hR₅
    cases c <;> cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero, Bool.false_eq_true, ite_false, ite_true] at e₂ e₅
    · rw [show wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n =
        (wordsVal s.mem base a M.n - wordsVal s.mem base b M.n) + m by omega_arith, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    · omega_arith
    · omega_arith
    · rw [Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith

end VG.Proof.Mont.X86_64

end

end

/-!
# Montgomery arithmetic on x86-64: P-521's product by columns

`mulP o a b` (`Impl/Mont/X86_64.lean`) for P-521's `p = 2⁵²¹ - 1`: a term
adds a product to the three-word accumulator (`pTerm_ok`), a column adds its
terms and stores its low word (`pCol_ok`), and the eighteen columns
(`pCols_ok`, by induction on them) leave `(a b + U p) / 2⁵⁷⁶` in the
temporary area and `r9`, for the reduction's `U < 2⁵⁷⁶`: the low words of the
first nine columns, each of which column `k + 8` adds 512 times. Then
`csubW` (`mulP_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry mulx_arith)

/-! ## The accumulator -/

/-- The accumulator of column `c`, lowest word first. -/
def pAccs (c : Nat) : List Reg := [pAcc c 0, pAcc c 1, pAcc c 2]

theorem pAcc_mod (c k : Nat) : pAcc c k = [Reg.r9, .r10, .r11].getD ((c + k) % 3) .r9 := rfl

theorem pAccs_cases (c : Nat) :
    pAccs c = [.r9, .r10, .r11] ∨ pAccs c = [.r10, .r11, .r9] ∨ pAccs c = [.r11, .r9, .r10] := by
  simp only [pAccs, pAcc_mod]
  rcases (by omega_using [] : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2) with h | h | h <;>
  simp only [Nat.add_mod c, h] <;> simp

theorem pAccs_succ (c : Nat) : pAccs (c + 1) = [pAcc c 1, pAcc c 2, pAcc c 0] := by
  simp only [pAccs, pAcc_mod]
  refine List.cons_eq_cons.mpr ⟨by rw [Nat.add_right_comm], List.cons_eq_cons.mpr
    ⟨by rw [Nat.add_assoc], List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  rw [show c + 1 + 2 = c + 3 by omega_using [], Nat.add_mod_right, Nat.add_zero]

/-- The accumulator's registers are distinct, and none of `rax`, `rcx`,
`rdx`, `rdi`. -/
theorem pAccs_ok (c : Nat) :
    [pAcc c 0, pAcc c 1, pAcc c 2, .rax, .rcx, .rdx, .rdi].Nodup ∧
      ∀ r ∈ pAccs c, r ∈ [Reg.r9, .r10, .r11] := by
  have := pAccs_cases c
  simp only [pAccs, List.cons.injEq, and_true] at this ⊢
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

/-! ## A term -/

/-- The value of a term's second factor: the word at `dy`, or 512. -/
def pY (m : Mem) (base : Addr) : Option Nat → Nat
  | some d => (word m base d).toNat
  | none => 512

/-- `rcx = y`. -/
theorem pLoadY_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dy : Option Nat}
    (hdy : ∀ d, dy = some d → d + 8 ≤ size) :
    WP isa (.block [.mov .rcx (pSrc dy)]) s
      fun s' => (s'.gpr .rcx).toNat = pY s.mem base dy ∧ Keeps [.rcx] s s' := by
  cases dy with
  | some d =>
    rw [pSrc]
    refine WP.mono (movRcx_ok hs (hdy d rfl)) fun s' ⟨e, k⟩ => ⟨by rw [e]; rfl, k⟩
  | none =>
    apply WP.of_runBlock
    simp only [pSrc, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- `rdx:rax = [dx] · rcx`, then `r0–r2 += rdx:rax`, for distinct `r0–r2`
other than `rax`, `rcx`, `rdx`, if the sum fits. -/
theorem pMulAcc_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {r0 r1 r2 : Reg}
    (hd : [r0, r1, r2, .rax, .rcx, .rdx, .rdi].Nodup) {dx : Nat} (hdx : dx + 8 ≤ size)
    (hb : regsVal s [r0, r1, r2] + (word s.mem base dx).toNat * (s.gpr .rcx).toNat < 2 ^ 192) :
    WP isa (.block [.mov .rax (.mem (sc dx)), .mul .rcx, .alu .add r0 (.reg .rax),
      .alu .adc r1 (.reg .rdx), .alu .adc r2 (.imm 0)]) s fun s' =>
      regsVal s' [r0, r1, r2] = regsVal s [r0, r1, r2] + (word s.mem base dx).toNat * (s.gpr .rcx).toNat ∧
      Keeps [.rax, .rdx, r0, r1, r2] s s' ∧
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = (word s.mem base dx).toNat * (s.gpr .rcx).toNat := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0c, h0d, h0i⟩, ⟨h12, h1a, h1c, h1d, h1i⟩, ⟨h2a, h2c, h2d, h2i⟩, -⟩ := hd
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, load_sc hs hdx, readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false,
    reduceCtorEq, Ne.symm h01, Ne.symm h02, Ne.symm h12, h0a, h1a, h2a, h0d, h1d, h2d,
    Ne.symm h0d, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩
  · simp only [regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, ite_true, ite_false,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12, Nat.mul_zero, Nat.add_zero]
    have em := mulx_arith (word s.mem base dx) (s.gpr .rcx)
    generalize BitVec.ofNat 64 ((word s.mem base dx).toNat * (s.gpr .rcx).toNat) = lo at em ⊢
    generalize BitVec.ofNat 64 ((word s.mem base dx).toNat * (s.gpr .rcx).toNat / 2 ^ 64) = hi at em ⊢
    have e0 := add_carry (s.gpr r0) lo
    generalize decide (2 ^ 64 ≤ (s.gpr r0).toNat + lo.toNat) = c0 at e0 ⊢
    have e1 := adc_carry (s.gpr r1) hi c0
    generalize decide (2 ^ 64 ≤ (s.gpr r1).toNat + hi.toNat + c0.toNat) = c1 at e1 ⊢
    have e2 := adc_carry (s.gpr r2) 0 c1
    generalize decide (2 ^ 64 ≤ (s.gpr r2).toNat + (0 : BitVec 64).toNat + c1.toNat) = c2 at e2
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hb
    have z : (0 : BitVec 64).toNat = 0 := rfl
    have := Bool.toNat_le c2
    have := (s.gpr r0 + lo).isLt; have := (s.gpr r1 + hi + (BitVec.ofBool c0).setWidth 64).isLt
    have := (s.gpr r2 + 0 + (BitVec.ofBool c1).setWidth 64).isLt
    rw [z] at e2
    rcases Nat.lt_or_ge c2.toNat 1 with h | h <;> omega_using [em, e0, e1, e2, h, hb]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2, ite_false]
  · simp only [Ne.symm h0a, Ne.symm h1a, Ne.symm h2a, Ne.symm h1d, Ne.symm h2d, ite_false]
    exact mulx_arith (word s.mem base dx) (s.gpr .rcx)

/-- A term: `acc += [dx] · y`. -/
theorem pTerm_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Nat) {dx : Nat}
    (hdx : dx + 8 ≤ size) {dy : Option Nat} (hdy : ∀ d, dy = some d → d + 8 ≤ size)
    (hb : regsVal s (pAccs c) + (word s.mem base dx).toNat * pY s.mem base dy < 2 ^ 192) :
    WP isa (.block (pTerm c dx dy)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + (word s.mem base dx).toNat * pY s.mem base dy ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s' ∧
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = (word s.mem base dx).toNat * pY s.mem base dy := by
  have hok := pAccs_ok c
  rw [pTerm, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (pLoadY_ok hs hdy) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hacc : regsVal s₁ (pAccs c) = regsVal s (pAccs c) := regsVal_congr fun r hr => k₁.1 r (by
    have := hok.2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    rcases this with rfl | rfl | rfl <;> decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.mono (pMulAcc_ok hs₁ hok.1 hdx (by
    rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, hacc, hm₁, e₁]; exact hb))
    fun s₂ ⟨e₂, k₂, x₂⟩ => ⟨?_, ?_, ?_⟩
  · rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, hacc, hm₁, e₁] at e₂
    exact e₂
  · exact (k₁.mono (by simp)).trans (k₂.mono (by simp [pAccs]))
  · rw [x₂, hm₁, e₁]

/-- The sum of terms. -/
def pSum (m : Mem) (base : Addr) (ts : List (Nat × Option Nat)) : Nat :=
  (ts.map fun t => (word m base t.1).toNat * pY m base t.2).sum

/-- Where a term reads: in the working space. -/
def PIn (size : Nat) (t : Nat × Option Nat) : Prop := t.1 + 8 ≤ size ∧ ∀ d, t.2 = some d → d + 8 ≤ size

/-- A column's terms, by induction on them. -/
theorem pTerms_ok (c : Nat) {size : Nat} : ∀ (ts : List (Nat × Option Nat)) {s : State} {base : Addr},
    Scr s base size → (∀ t ∈ ts, PIn size t) → regsVal s (pAccs c) + pSum s.mem base ts < 2 ^ 192 →
    WP isa (.block (ts.flatMap fun t => pTerm c t.1 t.2)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + pSum s.mem base ts ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s'
  | [], s, _, _, _, _ => WP.block_nil ⟨by simp [pSum], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, hs, hin, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    have ht := hin t List.mem_cons_self
    simp only [pSum, List.map_cons, List.sum_cons] at hb
    refine WP.mono (pTerm_ok hs c ht.1 ht.2 (by omega_using [hb])) fun s₁ ⟨e₁, k₁, _⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by have := (pAccs_ok c).2; simp only [List.mem_cons, not_or]; grind)
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    refine WP.mono (pTerms_ok c ts hs₁ (fun t' ht' => hin t' (List.mem_cons_of_mem _ ht'))
      (by rw [e₁, hm₁]; simp only [pSum] at hb ⊢; omega_using [hb])) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
    rw [e₂, e₁, hm₁]
    simp only [pSum, List.map_cons, List.sum_cons]
    omega_using []

/-- A column's end: its low word stored at `t` and cleared. -/
theorem pEnd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Nat) {t : Nat}
    (ht : t + 8 ≤ size) :
    WP isa (.block [.store (sc t) (pAcc c 0), .mov32 (pAcc c 0) (.imm 0)]) s fun s' =>
      s'.mem = s.mem.writeW (off base t) (s.gpr (pAcc c 0)) ∧
      regsVal s (pAccs c) = (s.gpr (pAcc c 0)).toNat + 2 ^ 64 * regsVal s' (pAccs (c + 1)) ∧
      KeepRegs [pAcc c 0] s s' := by
  have hok := pAccs_ok c
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hok
  obtain ⟨⟨h01, h02, -, -, -, -⟩, ⟨h12, -, -, -, -⟩, -, -⟩ := hok.1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, store_sc hs ht, readSrc32,
    Option.map_some, State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [pAccs_succ]
    simp only [pAccs, regsVal, RegUpd.gpr_setReg, ite_true, Ne.symm h01, Ne.symm h02, ite_false,
      Nat.mul_zero, Nat.add_zero]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- Column `c`: its terms, and its low word stored at `[tmp + 8 (c mod 9)]`;
the rest of the accumulator is the next column's. -/
theorem pCol_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {a b c : Nat}
    (htmp : M.tmp + 72 ≤ size) (hin : ∀ t ∈ pTerms M a b c, PIn size t)
    (hb : regsVal s (pAccs c) + pSum s.mem base (pTerms M a b c) < 2 ^ 192) :
    WP isa (.block (pCol M a b c)) s fun s' =>
      (word s'.mem base (M.tmp + 8 * (c % 9))).toNat + 2 ^ 64 * regsVal s' (pAccs (c + 1)) =
        regsVal s (pAccs c) + pSum s.mem base (pTerms M a b c) ∧
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' ∧
      Outside base (M.tmp + 8 * (c % 9)) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hc9 := Nat.mod_lt c (show 0 < 9 by decide)
  have hsub := (pAccs_ok c).2
  rw [pCol, WP.block_append_iff]
  refine WP.mono (pTerms_ok c _ hs hin hb) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by simp only [List.mem_cons, not_or]; grind)
  refine WP.mono (pEnd_ok hs₁ c (t := M.tmp + 8 * (c % 9)) (by omega_using [htmp])) fun s₂ ⟨m₂, e₂, k₂⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [m₂, word_writeW_self, ← e₂, e₁]
  · refine ⟨fun r hr => ?_, k₂.rd.trans k₁.2.2.1, k₂.wr.trans k₁.2.2.2⟩
    have hr' : r ∉ pAccs c := fun h => hr (by
      have := hsub r h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      grind)
    have h1 : r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs c := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨hr.1, hr.2.1, hr.2.2.1, hr'⟩
    have h2 : r ∉ [pAcc c 0] := fun h => hr' (by
      simp only [List.mem_singleton] at h
      simp [h, pAccs])
    rw [k₂.gpr r h2, k₁.1 r h1]
  · rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega_using [htmp, hnw])

/-! ## The columns' arithmetic -/

theorem pow64_succ' (n : Nat) : (2 ^ 64) ^ (n + 1) = 2 ^ 64 * (2 ^ 64) ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- `Σ_{j<n} 2^(64 j) f (k + j)`, in Horner form. -/
def hval (f : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => f k + 2 ^ 64 * hval f (k + 1) n

theorem hval_succ_last (f : Nat → Nat) : ∀ k n, hval f k (n + 1) = hval f k n + (2 ^ 64) ^ n * f (k + n)
  | k, 0 => by simp [hval]
  | k, n + 1 => by
    rw [hval, hval_succ_last f (k + 1) n, hval, pow64_succ', show k + 1 + n = k + (n + 1) by omega_using []]
    generalize (2 ^ 64) ^ n = Q
    grind

theorem hval_congr {f g : Nat → Nat} : ∀ {k n : Nat}, (∀ c, k ≤ c → c < k + n → f c = g c) →
    hval f k n = hval g k n
  | _, 0, _ => rfl
  | k, n + 1, h => by
    rw [hval, hval, h k (Nat.le_refl _) (by omega_using []), hval_congr fun c h1 h2 => h c (by omega_using [h1]) (by omega_using [h2])]

theorem hval_lt {f : Nat → Nat} : ∀ {k n : Nat}, (∀ c, k ≤ c → c < k + n → f c < 2 ^ 64) →
    hval f k n < (2 ^ 64) ^ n
  | _, 0, _ => Nat.one_pos
  | k, n + 1, h => by
    rw [hval, pow64_succ']
    exact word_add_lt (h k (Nat.le_refl _) (by omega_using [])) (hval_lt fun c h1 h2 => h c (by omega_using [h1]) (by omega_using [h2]))

theorem hval_add (f : Nat → Nat) : ∀ k n m, hval f k (n + m) = hval f k n + (2 ^ 64) ^ n * hval f (k + n) m
  | k, 0, m => by simp [hval]
  | k, n + 1, m => by
    rw [show n + 1 + m = (n + m) + 1 by omega_using [], hval, hval_add f (k + 1) n m, hval, pow64_succ',
      show k + 1 + n = k + (n + 1) by omega_using []]
    generalize (2 ^ 64) ^ n = Q
    grind

theorem wordsVal_hval (m : Mem) (base : Addr) (d : Nat) : ∀ k n,
    wordsVal m base (d + 8 * k) n = hval (fun j => (word m base (d + 8 * j)).toNat) k n
  | _, 0 => rfl
  | k, n + 1 => by
    rw [wordsVal, hval, show d + 8 * k + 8 = d + 8 * (k + 1) by omega_using [], wordsVal_hval m base d (k + 1) n]

/-- Column `c`'s sum: its products `A i · B j` (`i + j = c`) and, for
`8 ≤ c ≤ 16`, `512 l_{c-8}`. -/
def pColSum (A B l : Nat → Nat) (c : Nat) : Nat :=
  (((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map fun i => A i * B (c - i)).sum +
    if 8 ≤ c ∧ c ≤ 16 then l (c - 8) * 512 else 0

/-- The eighteen columns: the product, and `2⁵²¹ Σ_{k<9} 2^(64 k) l_k`. -/
theorem pColSum_total (A B l : Nat → Nat) :
    hval (pColSum A B l) 0 18 = hval A 0 9 * hval B 0 9 + 512 * (2 ^ 64) ^ 8 * hval l 0 9 := by
  simp only [hval, pColSum, List.range, List.range.loop, List.filter_cons, List.filter_nil,
    decide_eq_true_eq, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, and_true, and_false,
    ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.zero_add]
  generalize 2 ^ 64 = X
  grind

theorem sum_le_mul {L : List Nat} {K : Nat} (h : ∀ x ∈ L, x ≤ K) : L.sum ≤ L.length * K := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h x List.mem_cons_self
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega_arith

/-- A column's sum is below `10 · 2¹²⁸`, for words. -/
theorem pColSum_lt {A B l : Nat → Nat} (c : Nat) (hA : ∀ i, A i < 2 ^ 64) (hB : ∀ j, B j < 2 ^ 64)
    (hl : 8 ≤ c → c ≤ 16 → l (c - 8) < 2 ^ 64) : pColSum A B l c < 10 * 2 ^ 128 := by
  unfold pColSum
  have h1 := sum_le_mul (L := ((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map
      fun i => A i * B (c - i)) (K := 2 ^ 128) fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have := Nat.mul_le_mul (Nat.le_of_lt (hA i)) (Nat.le_of_lt (hB (c - i)))
    exact Nat.le_trans this (by decide)
  have h2 : (((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map fun i => A i * B (c - i)).length ≤ 9 := by
    rw [List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have h3 := Nat.mul_le_mul_right (2 ^ 128) h2
  split
  · have := hl (by omega_arith) (by omega_arith); omega_using [h1, h3, this]
  · omega_using [h1, h3]

/-- A column's terms' sum, from the words they read. -/
theorem pSum_pTerms {m : Mem} {base : Addr} {M : Mod} {a b c : Nat} {A B l : Nat → Nat}
    (hA : ∀ i < 9, (word m base (a + 8 * i)).toNat = A i)
    (hB : ∀ j < 9, (word m base (b + 8 * j)).toNat = B j)
    (hl : 8 ≤ c → c ≤ 16 → (word m base (M.tmp + 8 * (c - 8))).toNat = l (c - 8)) :
    pSum m base (pTerms M a b c) = pColSum A B l c := by
  simp only [pSum, pTerms, pColSum, List.map_append, List.sum_append, List.map_map]
  have e1 : (((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map ((fun t : Nat × Option Nat =>
      (word m base t.1).toNat * pY m base t.2) ∘ fun i => (a + 8 * i, some (b + 8 * (c - i))))).sum =
      (((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map fun i => A i * B (c - i)).sum := by
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    simp only [Function.comp, pY, hA i hi.1, hB (c - i) hi.2.2]
  rw [e1]
  refine congrArg (_ + ·) ?_
  split
  · rename_i h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, pY,
      hl h.1 h.2]
  · simp

/-- A family of column sums `S l c` (given the reduction's `u`s, `l`): column
`c`'s depends on `l` only at `c - 8` (for `8 ≤ c ≤ 16`), and is below
`2¹³³` if that is a word. -/
structure ColSum (S : (Nat → Nat) → Nat → Nat) : Prop where
  congr : ∀ l l' c, (8 ≤ c → c ≤ 16 → l (c - 8) = l' (c - 8)) → S l c = S l' c
  lt : ∀ l c, (8 ≤ c → c ≤ 16 → l (c - 8) < 2 ^ 64) → S l c < 2 ^ 133

/-- What column `c < 18` of a product by columns `col` does, from a state
whose memory differs from `m₀` only in the temporary area, which holds the
reduction's `u_{c-8}` (`l`): it adds its sum `S l c` to the accumulator
(below `2¹²⁸`) and stores its low word at `[tmp + 8 (c mod 9)]`. -/
def ColOk (M : Mod) (base : Addr) (size : Nat) (m₀ : Mem) (col : Nat → List Instr)
    (S : (Nat → Nat) → Nat → Nat) (P : State → Prop := fun _ => True) : Prop :=
  ∀ c < 18, ∀ (s : State) (l : Nat → Nat), Scr s base size → P s → Outside base M.tmp 72 m₀ s.mem →
    regsVal s (pAccs c) < 2 ^ 128 →
    (8 ≤ c → c ≤ 16 → (word s.mem base (M.tmp + 8 * (c - 8))).toNat = l (c - 8)) →
    WP isa (.block (col c)) s fun s' =>
      (word s'.mem base (M.tmp + 8 * (c % 9))).toNat + 2 ^ 64 * regsVal s' (pAccs (c + 1)) =
        regsVal s (pAccs c) + S l c ∧
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' ∧
      Outside base (M.tmp + 8 * (c % 9)) 8 s.mem s'.mem

/-- The first `n` columns: the low words (`l`) of those not yet overwritten in
the temporary area, and the accumulator, `hval (S l) 0 n =
hval l 0 n + 2^(64 n) acc`. -/
theorem cols_ok {s₀ : State} {base : Addr} {size : Nat} (hs : Scr s₀ base size) {M : Mod}
    {col : Nat → List Instr} {S : (Nat → Nat) → Nat → Nat} {P : State → Prop} (htmp : M.tmp + 72 ≤ size)
    (hS : ColSum S) (hcol : ColOk M base size s₀.mem col S P) (hP₀ : P s₀)
    (hP : ∀ s s', P s → KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' → P s')
    (h0 : regsVal s₀ (pAccs 0) = 0) :
    ∀ n ≤ 18, WP isa (.block ((List.range n).flatMap col)) s₀ fun s =>
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s₀ s ∧ Outside base M.tmp 72 s₀.mem s.mem ∧
      regsVal s (pAccs n) < 2 ^ 128 ∧
      ∃ l : Nat → Nat, (∀ c < n, l c < 2 ^ 64) ∧
        (∀ c < n, n ≤ c + 9 → (word s.mem base (M.tmp + 8 * (c % 9))).toNat = l c) ∧
        hval (S l) 0 n = hval l 0 n + (2 ^ 64) ^ n * regsVal s (pAccs n)
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _, by rw [h0]; decide,
      fun _ => 0, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      by simp [hval, h0]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (cols_ok hs htmp hS hcol hP₀ hP h0 n (by omega_using [hn]))
      fun s ⟨k, O, hacc, l, hl64, hlm, e⟩ => ?_
    have hnw := hs.nowrap
    have hsS : Scr s base size := hs.of_keepRegs k (by decide)
    have hL : 8 ≤ n → n ≤ 16 → (word s.mem base (M.tmp + 8 * (n - 8))).toNat = l (n - 8) :=
      fun h1 h2 => by
        have := hlm (n - 8) (by omega_arith) (by omega_using [])
        rwa [Nat.mod_eq_of_lt (show n - 8 < 9 by omega_using [h2])] at this
    have hcl := hS.lt l n fun h1 h2 => hl64 _ (by omega_using [h1])
    have hn9 := Nat.mod_lt n (show 0 < 9 by decide)
    refine WP.mono (hcol n (by omega_using [hn]) s l hsS (hP _ _ hP₀ k) O hacc hL) fun s' ⟨e', k', O'⟩ => ?_
    refine ⟨k.trans k', O.trans (O'.mono (by omega_using []) (by omega_using [])), by omega_using [hacc, hcl, e'],
      fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c, ?_, ?_, ?_⟩
    · intro c hc
      by_cases h : c = n
      · simp only [h, ite_true]; exact (word _ _ _).isLt
      · simp only [h, ite_false]; exact hl64 c (by omega_using [hc, h])
    · intro c hc hc9
      by_cases h : c = n
      · subst h; simp
      · simp only [h, ite_false]
        have hc9' := Nat.mod_lt c (show 0 < 9 by decide)
        have hne : c % 9 ≠ n % 9 := by omega_using [hc, hc9, h]
        rw [O'.word (by omega_using [hne]) (by omega_using [htmp, hnw])]
        exact hlm c (by omega_using [hc, hne]) (by omega_using [hc9])
    · rw [hval_succ_last, hval_succ_last, Nat.zero_add]
      simp only [↓reduceIte]
      have hcs : ∀ c, 0 ≤ c → c < 0 + n →
          S (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c) c = S l c :=
        fun c _ hc => hS.congr _ _ c fun _ _ => by simp only [show c - 8 ≠ n by omega_using [hc], ite_false]
      have hcn : S (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c) n =
          S l n := hS.congr _ _ n fun _ _ => by simp only [show n - 8 ≠ n by omega_arith, ite_false]
      rw [hval_congr hcs, hcn, e, hval_congr (g := l) (fun c _ hc => ite_eq_right_iff.mpr (fun h => absurd h
          (by omega_using [hc]))), pow64_succ']
      rw [Nat.mul_comm (2 ^ 64) ((2 ^ 64) ^ n), Nat.mul_assoc]
      generalize (2 ^ 64) ^ n = Q
      rw [Nat.add_assoc, ← Nat.mul_add, ← e', Nat.mul_add]
      omega_using []

/-- `mulP`'s column sums. -/
theorem colSum_p (A B : Nat → Nat) (hA : ∀ i, A i < 2 ^ 64) (hB : ∀ j, B j < 2 ^ 64) :
    ColSum (pColSum A B) where
  congr l l' c h := by
    unfold pColSum
    split
    · rename_i hc; rw [h hc.1 hc.2]
    · rfl
  lt l c h := Nat.lt_of_lt_of_le (pColSum_lt c hA hB h) (by decide)

/-- `mulP`'s columns. -/
theorem pCol_colOk {base : Addr} {size : Nat} {m₀ : Mem} {M : Mod} {a b : Nat}
    (htmp : M.tmp + 72 ≤ size) (ha : a + 72 ≤ size) (hb : b + 72 ≤ size)
    (haT : a + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ a) (hbT : b + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ b) :
    ColOk M base size m₀ (pCol M a b)
      (pColSum (fun i => (word m₀ base (a + 8 * i)).toNat) (fun j => (word m₀ base (b + 8 * j)).toNat)) :=
  fun c hc s l hsS _ O hacc hL => by
    have hnw := hsS.nowrap
    have hA : ∀ i < 9, (word s.mem base (a + 8 * i)).toNat = (word m₀ base (a + 8 * i)).toNat :=
      fun i hi => by rw [O.word (by omega_using [haT, hi]) (by omega_using [ha, hnw, hi])]
    have hB : ∀ j < 9, (word s.mem base (b + 8 * j)).toNat = (word m₀ base (b + 8 * j)).toNat :=
      fun j hj => by rw [O.word (by omega_using [hbT, hj]) (by omega_using [hb, hnw, hj])]
    have hsum := pSum_pTerms (M := M) (c := c) hA hB hL
    have hcol := pColSum_lt (A := fun i => (word m₀ base (a + 8 * i)).toNat)
      (B := fun j => (word m₀ base (b + 8 * j)).toNat) (l := l) c (fun i => (word _ _ _).isLt)
      (fun j => (word _ _ _).isLt) (fun h1 h2 => by rw [← hL h1 h2]; exact (word _ _ _).isLt)
    have hin : ∀ t ∈ pTerms M a b c, PIn size t := by
      intro t ht
      simp only [pTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with ⟨i, ⟨hi, -, hj⟩, rfl⟩ | ht
      · exact ⟨by omega_arith, fun d hd => by simp only [Option.some.injEq] at hd; omega_using [hb, hj, hd]⟩
      · split at ht
        · simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨by omega_arith, fun d hd => by simp at hd⟩
        · simp at ht
    refine WP.mono (pCol_ok hsS htmp hin (by rw [hsum]; omega_using [hacc, hcol])) fun s' ⟨e', k', O'⟩ =>
      ⟨by rw [e', hsum], k', O'⟩

theorem hval_shift (f : Nat → Nat) (d : Nat) : ∀ k n, hval f (k + d) n = hval (fun j => f (j + d)) k n
  | _, 0 => rfl
  | k, n + 1 => by
    rw [hval, hval, show k + d + 1 = (k + 1) + d by omega_using [], hval_shift f d (k + 1) n]

/-- The modulus of a friendly reduction by `p521Ws` is P-521's `p = 2⁵²¹ - 1`,
with `2⁵²¹ = 512 (2⁶⁴)⁸`. -/
theorem p521_of_red {M : Mod} {m : Nat} (hred : M.red = .friendly p521Ws) (h : M.ok m = true) :
    M.n = 9 ∧ m + 1 = 512 * (2 ^ 64) ^ 8 := by
  have h' := Mod.ok_red h
  rw [hred] at h'
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨⟨hn, hm⟩, hw⟩, -⟩ := h'
  have h1 : (m + 1) % 2 ^ 64 = 0 := by omega_using [hm]
  have hw' : mwVal p521Ws = 2 ^ 9 * (2 ^ 64) ^ 7 := by
    simp only [mwVal, p521Ws, MWord.val, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  have h2 := Nat.div_add_mod (m + 1) (2 ^ 64)
  rw [← hw, hw', h1, Nat.add_zero] at h2
  refine ⟨by rw [← hn]; rfl, ?_⟩
  rw [← h2, Nat.pow_succ]

/-- The arithmetic of `mulP`: from the columns' value `A B + 2⁵²¹ U =
U + 2⁵⁷⁶ W + 2¹¹⁵² acc` (`X = 2⁶⁴`), the top `acc` is zero and
`2⁵⁷⁶ W = A B + U p < 2⁵⁷⁶ · 2p`. -/
theorem mulP_arith {X A B U W m acc : Nat} (hX : 1024 ≤ X) (hm : m + 1 = 512 * X ^ 8)
    (hA : A < X ^ 9) (hB : B < m) (hU : U < X ^ 9)
    (e : A * B + 512 * X ^ 8 * U = U + X ^ 9 * W + X ^ 9 * X ^ 9 * acc) :
    acc = 0 ∧ W < 2 * m ∧ X ^ 9 * W = A * B + U * m := by
  have hX9 : X ^ 9 = X * X ^ 8 := by rw [Nat.pow_succ, Nat.mul_comm]
  have hUm : U * (m + 1) = U * m + U := by rw [Nat.mul_add, Nat.mul_one]
  have eT : X ^ 9 * (W + X ^ 9 * acc) = A * B + U * m := by
    rw [hm] at hUm
    rw [Nat.mul_add, ← Nat.mul_assoc]
    have : 512 * X ^ 8 * U = U * (512 * X ^ 8) := Nat.mul_comm _ _
    omega_using [e, hUm, this]
  have hAB : A * B < X ^ 9 * m := Nat.mul_lt_mul'' hA hB
  have hUm' : U * m < X ^ 9 * m := Nat.mul_lt_mul_of_pos_right hU (by omega_using [hB])
  have hT : W + X ^ 9 * acc < 2 * m := by
    have : X ^ 9 * (W + X ^ 9 * acc) < X ^ 9 * (2 * m) := by rw [eT, Nat.mul_left_comm]; omega_using [hAB, hUm']
    exact Nat.lt_of_mul_lt_mul_left this
  have h2m : 2 * m < X ^ 9 := by
    have : 1024 * X ^ 8 ≤ X * X ^ 8 := Nat.mul_le_mul_right _ hX
    omega_using [hm, hX9, this]
  have hacc : acc = 0 := by
    rcases Nat.eq_zero_or_pos acc with h | h
    · exact h
    · have : X ^ 9 * 1 ≤ X ^ 9 * acc := Nat.mul_le_mul_left _ h
      omega_using [hT, h2m, this]
  rw [hacc, Nat.mul_zero, Nat.add_zero] at eT hT
  exact ⟨hacc, hT, eT⟩

/-- `[o] = A B R⁻¹ mod p` for P-521's `p`, `R = 2⁵⁷⁶`, by columns whose sums
add up to `A B` and the reduction's `2⁵²¹ U`. -/
theorem prodCols_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o : Nat}
    (ho : o + 8 * M.n ≤ size) (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o)
    (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o) {col : Nat → List Instr}
    {S : (Nat → Nat) → Nat → Nat} (hS : ColSum S) (hcol : ColOk M base size s.mem col S) {A B : Nat}
    (hA : A < 2 ^ (64 * M.n)) (hB : B < m)
    (htot : ∀ l, hval (S l) 0 18 = A * B + 512 * (2 ^ 64) ^ 8 * hval l 0 9) :
    WP isa (.block (prodCols M o col)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧ wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m = A * B % m := by
  obtain ⟨hn9, hm⟩ := p521_of_red hred hM.red
  rw [Nat.pow_mul]
  have hnw := hs.nowrap
  have hmo := hM.mo
  have htmp := hM.tmp
  have hsep := hM.sep
  rw [Nat.pow_mul, hn9] at hA
  rw [hn9] at ho hoT hoM hmo htmp hsep ⊢
  rw [prodCols, List.append_assoc, WP.block_append_iff,
    show ([.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] : List Instr) =
      zeros [.r9, .r10, .r11] from rfl]
  refine WP.mono (zeros_ok s [.r9, .r10, .r11]) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h0 : regsVal s₁ (pAccs 0) = 0 := by
    simp only [show pAccs 0 = [.r9, .r10, .r11] from rfl, regsVal, z₁ .r9 (by simp),
      z₁ .r10 (by simp), z₁ .r11 (by simp)]
    rfl
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (cols_ok hs₁ (M := M) (by omega_using [htmp]) hS (by rw [hm₁]; exact hcol) trivial (fun _ _ _ _ => trivial)
    h0 18 (Nat.le_refl _))
    fun s₂ ⟨k₂, O₂, _, l, hl64, hlm, e₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- The value of the columns.
  rw [htot, hval_add l 0 9 9, Nat.zero_add,
    show (2 ^ 64) ^ 18 = (2 ^ 64) ^ 9 * (2 ^ 64) ^ 9 by rw [← Nat.pow_add]] at e₂
  have hW : wordsVal s₂.mem base M.tmp 9 = hval l 9 9 := by
    rw [show M.tmp = M.tmp + 8 * 0 from rfl, wordsVal_hval s₂.mem base M.tmp 0 9,
      show (9 : Nat) = 0 + 9 from rfl, hval_shift l 9 0 9]
    exact hval_congr fun c _ hc => by
      have := hlm (c + 9) (by omega_using [hc]) (by omega_using [])
      rwa [show (c + 9) % 9 = c by omega_using [hc]] at this
  have hU : hval l 0 9 < (2 ^ 64) ^ 9 := hval_lt fun c _ hc => hl64 c (by omega_using [hc])
  rw [← hW, show pAccs 18 = [.r9, .r10, .r11] from rfl] at e₂
  obtain ⟨hacc0, hT2, eT⟩ := mulP_arith (by decide) hm hA hB hU e₂
  have hr9 : (s₂.gpr .r9).toNat = 0 := by simp only [regsVal] at hacc0; omega_using [hacc0]
  have hmo₂ : wordsVal s₂.mem base M.mo 9 = m := by
    rw [O₂.wordsVal (by omega_using [hsep]) (by omega_using [hnw, hmo]), hm₁, ← hn9, hM.val]
  refine WP.mono (csubW_ok hs₂ (M := M) (o := o) (m := m) (by omega_using [hn9]) (by omega_using [hn9, hmo]) (by omega_using [hn9, htmp])
    (by omega_using [ho, hn9]) (by omega_using [hoT, hn9]) (by omega_using [hoM, hn9]) (by rw [hn9]; exact hmo₂)
    (by rw [hr9, Nat.mul_zero, Nat.add_zero, hn9]; exact hT2)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hr9, Nat.mul_zero, Nat.add_zero, hn9] at e₃
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · have hcl : ∀ q ∈ [Reg.rax, .rcx, .rdx, .r8, .r9, .r10, .r11], q ∈ clob M.n := by
      rw [hn9]; decide
    rw [k₃.gpr r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind))),
      k₂.gpr r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind))),
      k₁.1 r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)))]
  · rw [k₃.rd, k₂.rd, k₁.2.2.1]
  · rw [k₃.wr, k₂.wr, k₁.2.2.2]
  · rw [O₃ x (by omega_using [hx]), O₂ x (by omega_using [hn9, hx']), hm₁]
  · rw [e₃]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₃, Nat.mod_mul_mod, Nat.mul_comm, eT]
    simp only [Nat.add_mul_mod_self_right]

/-- `[o] = [a] [b] R⁻¹ mod p` for P-521's `p`, `R = 2⁵⁷⁶`. -/
theorem mulP_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o a b : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mulP M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn9 := (p521_of_red hred hM.red).1
  have htmp := hM.tmp
  rw [hn9] at ha hb haT hbT htmp
  have hv : ∀ x, wordsVal s.mem base x M.n = hval (fun i => (word s.mem base (x + 8 * i)).toNat) 0 9 := fun x => by
    rw [hn9, ← wordsVal_hval s.mem base x 0 9, Nat.mul_zero, Nat.add_zero]
  rw [mulP, hv a, hv b]
  exact prodCols_ok hs hM hred ho hoT hoM (colSum_p _ _ (fun _ => (word _ _ _).isLt) (fun _ => (word _ _ _).isLt))
    (pCol_colOk (by omega_using [htmp]) (by omega_using [ha]) (by omega_using [hb]) (by omega_using [haT])
        (by omega_using [hbT])) (by rw [← hv a]; exact wordsVal_lt _ _ _ _)
    (by rw [← hv b]; exact hB) fun l => pColSum_total _ _ l

end VG.Proof.Mont.X86_64
