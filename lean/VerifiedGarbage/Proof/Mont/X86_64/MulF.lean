import VerifiedGarbage.Proof.Mont.X86_64.MulP

/-!
# Montgomery arithmetic on x86-64: nine words by columns, for any modulus

`mulF o a b` (`Impl/Mont/X86_64.lean`), Montgomery multiplication by columns
for a modulus `m` of nine words: column `c` adds its products and the
reduction's `u_k m_j` (`pTerms_ok`, `MulP.lean`), and for `c < 9` computes
`u_c = t₀ m' mod 2⁶⁴`, stores it and adds `u_c m₀`, which clears the low word
(`fRed_ok`); the eighteen columns (`fCols_ok`, by induction on them) leave
`(a b + U m) / 2⁵⁷⁶ < 2m` in the temporary area and `r9`, for the `u`s'
`U < 2⁵⁷⁶`. Then `csubW` (`mulF_ok`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-! ## The reduction's `u` -/

/-- `rcx = u = r · minv mod 2⁶⁴`, also stored at `t`. -/
theorem fU_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (r : Reg)
    (minv : BitVec 64) {t : Nat} (ht : t + 8 ≤ size) :
    WP isa (.block [.mov .rax (.reg r), .movImm64 .rcx minv, .mul .rcx, .mov .rcx (.reg .rax),
      .store (sc t) .rcx]) s fun s' =>
      (s'.gpr .rcx).toNat = (s.gpr r).toNat * minv.toNat % 2 ^ 64 ∧
      s'.mem = s.mem.writeW (off base t) (s'.gpr .rcx) ∧ KeepRegs [.rax, .rcx, .rdx] s s' := by
  rw [show ([.mov .rax (.reg r), .movImm64 .rcx minv, .mul .rcx, .mov .rcx (.reg .rax),
      .store (sc t) .rcx] : List Instr) = [.mov .rax (.reg r), .movImm64 .rcx minv, .mul .rcx,
      .mov .rcx (.reg .rax)] ++ [.store (sc t) .rcx] from rfl, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rax (.reg r), .movImm64 .rcx minv, .mul .rcx,
      .mov .rcx (.reg .rax)]) s (fun s₁ => (s₁.gpr .rcx).toNat = (s.gpr r).toNat * minv.toNat % 2 ^ 64 ∧
        Keeps [.rax, .rcx, .rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul, Option.map_some,
      RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
      exists_eq_left']
    refine ⟨BitVec.toNat_ofNat _ _, fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hq.1, hq.2.1, hq.2.2, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (storeReg_ok hs₁ .rcx ht) fun s₂ ⟨m₂, g₂, _, k₂⟩ => ⟨?_, ?_, ?_⟩
  · rw [g₂]; exact e₁
  · rw [m₂, g₂, k₁.2.1]
  · exact ⟨fun q hq => by rw [g₂]; exact k₁.1 q hq, k₂.rd.trans k₁.2.2.1, k₂.wr.trans k₁.2.2.2⟩

/-! ## A column -/

/-- A sum of terms read from words is below `L · 2¹²⁸` for `L` terms. -/
theorem pSum_le (m : Mem) (base : Addr) (ts : List (Nat × Option Nat)) (h : ∀ t ∈ ts, t.2.isSome) :
    pSum m base ts ≤ ts.length * 2 ^ 128 := by
  unfold pSum
  have := sum_le_mul (L := ts.map fun t => (word m base t.1).toNat * pY m base t.2) (K := 2 ^ 128) fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (h t ht)
    simp only [hd, pY]
    have := Nat.mul_le_mul (Nat.le_of_lt (word m base t.1).isLt) (Nat.le_of_lt (word m base d).isLt)
    exact Nat.le_trans this (by decide)
  rwa [List.length_map] at this

theorem fTerms_some (M : Mod) (a b c : Nat) : ∀ t ∈ fTerms M a b c, t.2.isSome := by
  intro t ht
  simp only [fTerms, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨_, -, rfl⟩ | ⟨_, -, rfl⟩ <;> rfl

theorem fTerms_length (M : Mod) (a b c : Nat) : (fTerms M a b c).length ≤ 2 * M.n := by
  simp only [fTerms, List.length_append, List.length_map]
  have h1 := List.length_filter_le (fun i => decide (i ≤ c ∧ c - i < M.n)) (List.range M.n)
  have h2 := List.length_filter_le (fun k => decide (k < c ∧ c - k < M.n)) (List.range M.n)
  simp only [List.length_range] at h1 h2
  omega

/-- Column `c` of `mulF` (nine words): its terms; then for `c < 9` the
reduction's `u_c`, stored at `[tmp + 8c]`, whose `u_c m₀` clears the low word,
and for `c ≥ 9` the low word stored at `[tmp + 8 (c - 9)]`; the rest of the
accumulator is the next column's. -/
theorem fCol_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {a b c : Nat}
    (hn : M.n = 9) (hc : c < 18) (htmp : M.tmp + 72 ≤ size) (hmo : M.mo + 72 ≤ size)
    (hsep : M.mo + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ M.mo)
    (hinv : ((word s.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (hin : ∀ t ∈ fTerms M a b c, PIn size t)
    (hb : regsVal s (pAccs (c + 9)) + pSum s.mem base (fTerms M a b c) < 19 * 2 ^ 128) :
    WP isa (.block (fCol M a b c)) s fun s' =>
      (if c < 9 then 0 else (word s'.mem base (M.tmp + 8 * (c % 9))).toNat) +
          2 ^ 64 * regsVal s' (pAccs (c + 1 + 9)) =
        regsVal s (pAccs (c + 9)) + pSum s.mem base (fTerms M a b c) +
          (if c < 9 then (word s'.mem base (M.tmp + 8 * (c % 9))).toNat * (word s.mem base M.mo).toNat
            else 0) ∧
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' ∧
      Outside base (M.tmp + 8 * (c % 9)) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hc9 := Nat.mod_lt c (show 0 < 9 by decide)
  have hok := pAccs_ok (c + 9)
  have hsub := hok.2
  have hrdi : Reg.rdi ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs (c + 9) := by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h
    all_goals first | exact absurd h (by decide) | exact absurd (hsub _ h) (by decide)
  have hkeep : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .r9, .r10, .r11] → r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs (c + 9) :=
    fun r hr h => hr (by
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · have := hsub r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at this; grind)
  rw [fCol, hn, WP.block_append_iff]
  refine WP.mono (pTerms_ok (c + 9) _ hs hin (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ hrdi
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  split
  · rename_i hc'
    have hcm : c % 9 = c := Nat.mod_eq_of_lt hc'
    rw [fRed, hn, show ([.mov .rax (.reg (pAcc (c + 9) 0)), .movImm64 .rcx M.minv, .mul .rcx,
        .mov .rcx (.reg .rax), .store (sc (M.tmp + 8 * c)) .rcx, .mov .rax (.mem (sc M.mo)), .mul .rcx,
        .alu .add (pAcc (c + 9) 0) (.reg .rax), .alu .adc (pAcc (c + 9) 1) (.reg .rdx),
        .alu .adc (pAcc (c + 9) 2) (.imm 0)] : List Instr) =
        [.mov .rax (.reg (pAcc (c + 9) 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax),
          .store (sc (M.tmp + 8 * c)) .rcx] ++ [.mov .rax (.mem (sc M.mo)), .mul .rcx,
        .alu .add (pAcc (c + 9) 0) (.reg .rax), .alu .adc (pAcc (c + 9) 1) (.reg .rdx),
        .alu .adc (pAcc (c + 9) 2) (.imm 0)] from rfl, WP.block_append_iff]
    refine WP.mono (fU_ok hs₁ (pAcc (c + 9) 0) M.minv (t := M.tmp + 8 * c) (by omega))
      fun s₂ ⟨u₂, m₂, k₂⟩ => ?_
    have hs₂ := hs₁.of_keepRegs k₂ (by decide)
    have O₂ : Outside base (M.tmp + 8 * c) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    have hmo₂ : word s₂.mem base M.mo = word s.mem base M.mo := by
      rw [O₂.word (by omega) (by omega), hm₁]
    have hacc₂ : regsVal s₂ (pAccs (c + 9)) = regsVal s₁ (pAccs (c + 9)) :=
      regsVal_congr fun r hr => k₂.gpr r (by
        have := hsub r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
        grind)
    have hlow := regsVal_lt s₁ [pAcc (c + 9) 1, pAcc (c + 9) 2]
    have hu₂ : (s₂.gpr .rcx).toNat < 2 ^ 64 := (s₂.gpr .rcx).isLt
    refine WP.mono (pMulAcc_ok hs₂ hok.1 (dx := M.mo) (by omega) (by
      rw [show [pAcc (c + 9) 0, pAcc (c + 9) 1, pAcc (c + 9) 2] = pAccs (c + 9) from rfl, hacc₂, e₁, hmo₂]
      have := Nat.mul_le_mul (Nat.le_of_lt (word s.mem base M.mo).isLt) (Nat.le_of_lt hu₂)
      have : (2 ^ 64 - 1) * (2 ^ 64 - 1) < 2 ^ 128 := by decide
      omega)) fun s₃ ⟨e₃, k₃, _⟩ => ?_
    rw [show [pAcc (c + 9) 0, pAcc (c + 9) 1, pAcc (c + 9) 2] = pAccs (c + 9) from rfl, hacc₂, hmo₂] at e₃
    have hm₃ : s₃.mem = s₂.mem := k₃.2.1
    -- The low word is now zero.
    have hz : (s₃.gpr (pAcc (c + 9) 0)).toNat = 0 := by
      have e0 : regsVal s₁ (pAccs (c + 9)) % 2 ^ 64 = (s₁.gpr (pAcc (c + 9) 0)).toNat := by
        simp only [pAccs, regsVal]; omega
      have e3 : regsVal s₃ (pAccs (c + 9)) % 2 ^ 64 = (s₃.gpr (pAcc (c + 9) 0)).toNat := by
        simp only [pAccs, regsVal]; omega
      have hu : (s₂.gpr .rcx).toNat = (s₁.gpr (pAcc (c + 9) 0)).toNat * M.minv.toNat % 2 ^ 64 := u₂
      rw [← e3, e₃, hu, Nat.add_mod, e0, Nat.mul_comm (word s.mem base M.mo).toNat]
      have := mont_low (s₁.gpr (pAcc (c + 9) 0)).toNat M.minv.toNat (word s.mem base M.mo).toNat hinv
      rwa [Nat.add_mod, Nat.mod_eq_of_lt (s₁.gpr (pAcc (c + 9) 0)).isLt] at this
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.zero_add, hcm, hm₃, m₂, word_writeW_self, show c + 1 + 9 = c + 9 + 1 by omega, pAccs_succ]
      have h3 : regsVal s₃ (pAccs (c + 9)) =
          2 ^ 64 * regsVal s₃ [pAcc (c + 9) 1, pAcc (c + 9) 2, pAcc (c + 9) 0] := by
        simp only [pAccs, regsVal, hz]; omega
      rw [← h3, e₃, e₁, Nat.mul_comm (word s.mem base M.mo).toNat]
    · refine ⟨fun r hr => ?_, k₃.2.2.1.trans (k₂.rd.trans k₁.2.2.1), k₃.2.2.2.trans (k₂.wr.trans k₁.2.2.2)⟩
      have h1 := hkeep r hr
      have h3 : r ∉ [Reg.rax, .rdx, pAcc (c + 9) 0, pAcc (c + 9) 1, pAcc (c + 9) 2] := fun h => h1 (by
        simp only [pAccs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)
      have h2 : r ∉ [Reg.rax, .rcx, .rdx] := fun h => h1 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)
      rw [k₃.1 r h3, k₂.gpr r h2, k₁.1 r h1]
    · rw [hcm, hm₃]; exact fun x hx => by rw [O₂ x hx, hm₁]
  · rename_i hc'
    have hcm : c % 9 = c - 9 := by omega
    refine WP.mono (pEnd_ok hs₁ (c + 9) (t := M.tmp + 8 * (c - 9)) (by omega)) fun s₂ ⟨m₂, e₂, k₂⟩ => ?_
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.add_zero, hcm, m₂, word_writeW_self, ← e₁, e₂,
        show c + 1 + 9 = c + 9 + 1 by omega]
      rfl
    · refine ⟨fun r hr => ?_, k₂.rd.trans k₁.2.2.1, k₂.wr.trans k₁.2.2.2⟩
      have h1 := hkeep r hr
      rw [k₂.gpr r (fun h => h1 (by simp only [List.mem_singleton] at h; simp [h, pAccs])), k₁.1 r h1]
    · rw [hcm, m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega)

/-! ## The columns' arithmetic -/

/-- `Σ f i · g j` over `i + j = c`, `i, j < 9`. -/
def prodCol (f g : Nat → Nat) (c : Nat) : Nat :=
  (((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map fun i => f i * g (c - i)).sum

/-- `Σ l k · g j` over `k + j = c`, `k < c`, `k, j < 9`: the reduction's terms
but the column's own `u`. -/
def redCol (l g : Nat → Nat) (c : Nat) : Nat :=
  (((List.range 9).filter fun k => k < c ∧ c - k < 9).map fun k => l k * g (c - k)).sum

/-- Column `c`'s sum: its products, its reduction's terms, and for `c < 9`
its own `u_c m₀`. -/
def fColSum (A B Mw l : Nat → Nat) (c : Nat) : Nat :=
  prodCol A B c + redCol l Mw c + if c < 9 then l c * Mw 0 else 0

/-- The eighteen columns: `A B + U m`. -/
theorem fColSum_total (A B Mw l : Nat → Nat) :
    hval (fColSum A B Mw l) 0 18 = hval A 0 9 * hval B 0 9 + hval l 0 9 * hval Mw 0 9 := by
  simp only [hval, fColSum, prodCol, redCol, List.range, List.range.loop, List.filter_cons, List.filter_nil,
    decide_eq_true_eq, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, and_true, and_false,
    ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
  generalize 2 ^ 64 = X
  grind

/-- A column's terms' sum, from the words they read. -/
theorem pSum_fTerms {m : Mem} {base : Addr} {M : Mod} {a b c : Nat} {A B Mw l : Nat → Nat} (hn : M.n = 9)
    (hA : ∀ i < 9, (word m base (a + 8 * i)).toNat = A i)
    (hB : ∀ j < 9, (word m base (b + 8 * j)).toNat = B j)
    (hM : ∀ j < 9, (word m base (M.mo + 8 * j)).toNat = Mw j)
    (hl : ∀ k < 9, k < c → c - k < 9 → (word m base (M.tmp + 8 * k)).toNat = l k) :
    pSum m base (fTerms M a b c) = prodCol A B c + redCol l Mw c := by
  simp only [pSum, fTerms, hn, List.map_append, List.sum_append, List.map_map, prodCol, redCol]
  refine congrArg₂ (· + ·) (congrArg List.sum (List.map_congr_left fun i hi => ?_))
    (congrArg List.sum (List.map_congr_left fun k hk => ?_))
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    simp only [Function.comp, pY, hA i hi.1, hB (c - i) hi.2.2]
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
    simp only [Function.comp, pY, hl k hk.1 hk.2.1 hk.2.2, hM (c - k) hk.2.2]

theorem fColSum_congr {A B Mw l l' : Nat → Nat} {c : Nat} (h : ∀ k ≤ c, l' k = l k) :
    fColSum A B Mw l' c = fColSum A B Mw l c := by
  unfold fColSum redCol
  rw [List.map_congr_left fun k hk => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
    rw [h k (by omega)]]
  split
  · rw [h c (Nat.le_refl _)]
  · rfl

/-- The first `n` columns of `mulF`: the words they wrote (`l`: the `u`s and
the result's low words) where not yet overwritten, and the accumulator,
`hval (fColSum A B m l) 0 n = hval e 0 n + 2^(64 n) acc` for the low words
`e` (zero for the first nine). -/
theorem fCols_ok {s₀ : State} {base : Addr} {size : Nat} (hs : Scr s₀ base size) {M : Mod} {a b : Nat}
    (hn : M.n = 9) (htmp : M.tmp + 72 ≤ size) (hmo : M.mo + 72 ≤ size) (ha : a + 72 ≤ size)
    (hb : b + 72 ≤ size) (hsep : M.mo + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ M.mo)
    (haT : a + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ a) (hbT : b + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ b)
    (hinv : ((word s₀.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (h0 : regsVal s₀ (pAccs 9) = 0) :
    ∀ n ≤ 18, WP isa (.block ((List.range n).flatMap (fCol M a b))) s₀ fun s =>
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s₀ s ∧ Outside base M.tmp 72 s₀.mem s.mem ∧
      regsVal s (pAccs (n + 9)) < 2 ^ 128 ∧
      ∃ l : Nat → Nat, (∀ c < n, l c < 2 ^ 64) ∧
        (∀ c < n, n ≤ c + 9 → (word s.mem base (M.tmp + 8 * (c % 9))).toNat = l c) ∧
        hval (fColSum (fun i => (word s₀.mem base (a + 8 * i)).toNat)
          (fun j => (word s₀.mem base (b + 8 * j)).toNat) (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat) l)
          0 n = hval (fun c => if c < 9 then 0 else l c) 0 n + (2 ^ 64) ^ n * regsVal s (pAccs (n + 9))
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _, by rw [h0]; decide,
      fun _ => 0, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      by simp [hval, h0]⟩
  | n + 1, hn18 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (fCols_ok hs hn htmp hmo ha hb hsep haT hbT hinv h0 n (by omega))
      fun s ⟨k, O, hacc, l, hl64, hlm, e⟩ => ?_
    have hnw := hs.nowrap
    have hsS : Scr s base size := hs.of_keepRegs k (by decide)
    have hA : ∀ i < 9, (word s.mem base (a + 8 * i)).toNat = (word s₀.mem base (a + 8 * i)).toNat :=
      fun i hi => by rw [O.word (by omega) (by omega)]
    have hB : ∀ j < 9, (word s.mem base (b + 8 * j)).toNat = (word s₀.mem base (b + 8 * j)).toNat :=
      fun j hj => by rw [O.word (by omega) (by omega)]
    have hM : ∀ j < 9, (word s.mem base (M.mo + 8 * j)).toNat = (word s₀.mem base (M.mo + 8 * j)).toNat :=
      fun j hj => by rw [O.word (by omega) (by omega)]
    have hL : ∀ k < 9, k < n → n - k < 9 → (word s.mem base (M.tmp + 8 * k)).toNat = l k :=
      fun k h9 hk hk' => by
      have := hlm k hk (by omega)
      rwa [Nat.mod_eq_of_lt (show k < 9 by omega)] at this
    have hsum := pSum_fTerms (M := M) (c := n) hn hA hB hM hL
    have hpl := pSum_le s.mem base (fTerms M a b n) (fTerms_some M a b n)
    have hlen := fTerms_length M a b n
    rw [hn] at hlen
    have hlen' := Nat.mul_le_mul_right (2 ^ 128) hlen
    have hin : ∀ t ∈ fTerms M a b n, PIn size t := by
      intro t ht
      simp only [fTerms, hn, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with ⟨i, ⟨hi, -, hj⟩, rfl⟩ | ⟨i, ⟨hi, -, hj⟩, rfl⟩
      · exact ⟨by omega, fun d hd => by simp only [Option.some.injEq] at hd; omega⟩
      · exact ⟨by omega, fun d hd => by simp only [Option.some.injEq] at hd; omega⟩
    have hinv' : ((word s.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0 := by
      rw [O.word (by omega) (by omega)]; exact hinv
    have hn9 := Nat.mod_lt n (show 0 < 9 by decide)
    refine WP.mono (fCol_ok hsS hn (by omega) htmp hmo hsep hinv' hin (by omega)) fun s' ⟨e', k', O'⟩ => ?_
    have hm0 := hM 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at hm0
    rw [hm0] at e'
    have hw := (word s'.mem base (M.tmp + 8 * (n % 9))).isLt
    have hm64 := (word s₀.mem base M.mo).isLt
    refine ⟨k.trans k', O.trans (O'.mono (by omega) (by omega)), ?_,
      fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c, ?_, ?_, ?_⟩
    · have hp : (word s'.mem base (M.tmp + 8 * (n % 9))).toNat * (word s₀.mem base M.mo).toNat ≤
          (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
      rw [show n + 1 + 9 = n + 1 + 9 from rfl]
      split at e' <;> omega
    · intro c hc
      by_cases h : c = n
      · simp only [h, ite_true]; exact hw
      · simp only [h, ite_false]; exact hl64 c (by omega)
    · intro c hc hc9
      by_cases h : c = n
      · subst h; simp
      · simp only [h, ite_false]
        have hc9' := Nat.mod_lt c (show 0 < 9 by decide)
        have hne : c % 9 ≠ n % 9 := by omega
        rw [O'.word (by omega) (by omega)]
        exact hlm c (by omega) (by omega)
    · rw [hval_succ_last, hval_succ_last, Nat.zero_add]
      rw [hval_congr (g := fColSum (fun i => (word s₀.mem base (a + 8 * i)).toNat)
          (fun j => (word s₀.mem base (b + 8 * j)).toNat) (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat) l)
          (fun c _ hc => fColSum_congr fun k hk => ite_eq_right_iff.mpr fun h => absurd h (by omega)),
        hval_congr (f := fun c => if c < 9 then 0 else
            (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c) c)
          (g := fun c => if c < 9 then 0 else l c)
          (fun c _ hc => by simp only [show c ≠ n by omega, ite_false]),
        e]
      have hcol : fColSum (fun i => (word s₀.mem base (a + 8 * i)).toNat)
          (fun j => (word s₀.mem base (b + 8 * j)).toNat) (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat)
          (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c) n =
          pSum s.mem base (fTerms M a b n) +
            if n < 9 then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat * (word s₀.mem base M.mo).toNat
            else 0 := by
        rw [hsum]
        unfold fColSum
        rw [show redCol (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c)
            (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat) n =
            redCol l (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat) n by
          unfold redCol
          refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
          simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
          simp only [show k ≠ n by omega, ite_false]]
        split <;> simp only [ite_true, Nat.mul_zero, Nat.add_zero, Nat.add_assoc]
      rw [hcol, pow64_succ', Nat.mul_comm (2 ^ 64) ((2 ^ 64) ^ n), Nat.mul_assoc]
      generalize (2 ^ 64) ^ n = Q
      rw [Nat.add_assoc, ← Nat.mul_add, ← Nat.add_assoc, ← e', Nat.mul_add]
      simp only [↓reduceIte, Nat.add_assoc]

theorem hval_zero : ∀ k n, hval (fun _ => 0) k n = 0
  | _, 0 => rfl
  | k, n + 1 => by rw [hval, hval_zero (k + 1) n]

/-- The arithmetic of `mulF`: from the columns' value `A B + U m =
2⁵⁷⁶ W + 2¹¹⁵² acc` (`X = 2⁶⁴`), `acc ≤ 1` and `W + 2⁵⁷⁶ acc < 2m`. -/
theorem mulF_arith {X A B U W m acc : Nat} (hm : m < X ^ 9) (hA : A < X ^ 9) (hB : B < m) (hU : U < X ^ 9)
    (e : A * B + U * m = X ^ 9 * W + X ^ 9 * X ^ 9 * acc) :
    acc ≤ 1 ∧ W + X ^ 9 * acc < 2 * m ∧ X ^ 9 * (W + X ^ 9 * acc) = A * B + U * m := by
  have eT : X ^ 9 * (W + X ^ 9 * acc) = A * B + U * m := by rw [Nat.mul_add, ← Nat.mul_assoc]; omega
  have hAB : A * B < X ^ 9 * m := Nat.mul_lt_mul'' hA hB
  have hUm' : U * m < X ^ 9 * m := Nat.mul_lt_mul_of_pos_right hU (by omega)
  have hT : W + X ^ 9 * acc < 2 * m := by
    have : X ^ 9 * (W + X ^ 9 * acc) < X ^ 9 * (2 * m) := by rw [eT, Nat.mul_left_comm]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨?_, hT, eT⟩
  rcases Nat.lt_or_ge acc 2 with h | h
  · omega
  · have : X ^ 9 * 2 ≤ X ^ 9 * acc := Nat.mul_le_mul_left _ h
    omega

/-- `[o] = [a] [b] R⁻¹ mod m` for a modulus `m` of nine words, `R = 2⁵⁷⁶`. -/
theorem mulF_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hn9 : M.n = 9) {o a b : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mulF M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  rw [Nat.pow_mul]
  have hnw := hs.nowrap
  have hmo := hM.mo
  have htmp := hM.tmp
  have hsep := hM.sep
  have hmv := hM.val
  have hinv := hM.inv
  rw [hn9] at ho ha hb hoT haT hbT hoM hB hmo htmp hsep hmv ⊢
  rw [mulF, hn9, List.append_assoc, WP.block_append_iff,
    show ([.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] : List Instr) =
      zeros [.r9, .r10, .r11] from rfl]
  refine WP.mono (zeros_ok s [.r9, .r10, .r11]) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h0 : regsVal s₁ (pAccs 9) = 0 := by
    simp only [show pAccs 9 = [.r9, .r10, .r11] from rfl, regsVal, z₁ .r9 (by simp),
      z₁ .r10 (by simp), z₁ .r11 (by simp)]
    rfl
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hinv₁ : ((word s₁.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hm₁]
    rw [← hmv, show wordsVal s.mem base M.mo 9 = (word s.mem base M.mo).toNat +
      2 ^ 64 * wordsVal s.mem base (M.mo + 8) 8 from rfl, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm,
      Nat.add_mul_mod_self_left] at hinv
    exact hinv
  rw [WP.block_append_iff]
  refine WP.mono (fCols_ok hs₁ hn9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hinv₁ h0 18 (Nat.le_refl _)) fun s₂ ⟨k₂, O₂, _, l, hl64, hlm, e₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- The value of the columns.
  rw [fColSum_total, hval_add _ 0 9 9, Nat.zero_add,
    hval_congr (k := 0) (n := 9) (g := fun _ => 0) (fun c _ hc => ite_eq_left_iff.mpr fun h => absurd (by omega) h), hval_zero,
    hval_congr (k := 9) (n := 9) (g := l) (fun c hc _ => ite_eq_right_iff.mpr fun h => absurd h (by omega)), Nat.zero_add,
    show (2 ^ 64) ^ 18 = (2 ^ 64) ^ 9 * (2 ^ 64) ^ 9 by rw [← Nat.pow_add]] at e₂
  have hA : wordsVal s.mem base a 9 = hval (fun i => (word s₁.mem base (a + 8 * i)).toNat) 0 9 := by
    rw [← wordsVal_hval s₁.mem base a 0 9, hm₁, Nat.mul_zero, Nat.add_zero]
  have hBv : wordsVal s.mem base b 9 = hval (fun j => (word s₁.mem base (b + 8 * j)).toNat) 0 9 := by
    rw [← wordsVal_hval s₁.mem base b 0 9, hm₁, Nat.mul_zero, Nat.add_zero]
  have hMv : m = hval (fun j => (word s₁.mem base (M.mo + 8 * j)).toNat) 0 9 := by
    rw [← wordsVal_hval s₁.mem base M.mo 0 9, hm₁, Nat.mul_zero, Nat.add_zero, hmv]
  have hW : wordsVal s₂.mem base M.tmp 9 = hval l 9 9 := by
    rw [show M.tmp = M.tmp + 8 * 0 from rfl, wordsVal_hval s₂.mem base M.tmp 0 9,
      show (9 : Nat) = 0 + 9 from rfl, hval_shift l 9 0 9]
    exact hval_congr fun c _ hc => by
      have := hlm (c + 9) (by omega) (by omega)
      rwa [show (c + 9) % 9 = c by omega] at this
  have hU : hval l 0 9 < (2 ^ 64) ^ 9 := hval_lt fun c _ hc => hl64 c (by omega)
  have hAlt : wordsVal s.mem base a 9 < (2 ^ 64) ^ 9 := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  have hmlt : m < (2 ^ 64) ^ 9 := by rw [← hmv, ← Nat.pow_mul]; exact wordsVal_lt _ _ _ 9
  rw [← hA, ← hBv, ← hMv, ← hW, show pAccs (18 + 9) = [.r9, .r10, .r11] from rfl] at e₂
  obtain ⟨hacc1, hT2, eT⟩ := mulF_arith hmlt hAlt hB hU e₂
  have hr9 : (s₂.gpr .r9).toNat = regsVal s₂ [.r9, .r10, .r11] := by simp only [regsVal] at hacc1 ⊢; omega
  have hmo₂ : wordsVal s₂.mem base M.mo 9 = m := by
    rw [O₂.wordsVal (by omega) (by omega), hm₁, hmv]
  refine WP.mono (csubW_ok hs₂ (M := M) (o := o) (m := m) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [hn9]; exact hmo₂)
    (by rw [hr9, Nat.pow_mul, hn9]; exact hT2)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hr9, Nat.pow_mul, hn9] at e₃
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · have hcl : ∀ q ∈ [Reg.rax, .rcx, .rdx, .r8, .r9, .r10, .r11], q ∈ clob M.n := by
      rw [hn9]; decide
    rw [k₃.gpr r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind))),
      k₂.gpr r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind))),
      k₁.1 r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)))]
  · rw [k₃.rd, k₂.rd, k₁.2.2.1]
  · rw [k₃.wr, k₂.wr, k₁.2.2.2]
  · rw [O₃ x (by omega), O₂ x (by omega), hm₁]
  · rw [e₃]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₃, Nat.mod_mul_mod, Nat.mul_comm, eT]
    simp only [Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86_64
