module

public import VerifiedGarbage.Proof.Mont.X86_64.MulP
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Montgomery arithmetic on x86-64: eight and nine words by columns, for any modulus

`mulF o a b` (`Impl/Mont/X86_64.lean`), Montgomery multiplication by columns
for a modulus `m` of `w` words: column `c` adds its products and the
reduction's `u_k m_j` (`pTerms_ok`, `MulP.lean`), and for `c < w` computes
`u_c = t₀ m' mod 2⁶⁴`, stores it and adds `u_c m₀`, which clears the low word
(`fCol_ok`); the `2w` columns (`fCols_ok`, by induction on them) leave
`(a b + U m) / 2^(64w) < 2m` in the temporary area and `r9`, for the `u`s'
`U < 2^(64w)`. Then `csubW` (`mulF_ok`).
-/

@[expose] public section

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

variable {w : Nat}

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
  omega_using [h1, h2]

/-- Column `c` of `mulF` (`w` words): its terms; then for `c < w` the
reduction's `u_c`, stored at `[tmp + 8c]`, whose `u_c m₀` clears the low word,
and for `c ≥ w` the low word stored at `[tmp + 8 (c - w)]`; the rest of the
accumulator is the next column's. -/
theorem fCol_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {a b c : Nat}
    (hn : M.n = w) (hw : 0 < w) (hc : c < (2 * w)) (htmp : M.tmp + (8 * w) ≤ size) (hmo : M.mo + (8 * w) ≤ size)
    (hsep : M.mo + (8 * w) ≤ M.tmp ∨ M.tmp + (8 * w) ≤ M.mo)
    (hinv : ((word s.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (hin : ∀ t ∈ fTerms M a b c, PIn size t)
    (hb : regsVal s (pAccs (c + w)) + pSum s.mem base (fTerms M a b c) < 19 * 2 ^ 128) :
    WP isa (.block (fCol M a b c)) s fun s' =>
      (if c < w then 0 else (word s'.mem base (M.tmp + 8 * (c % w))).toNat) +
          2 ^ 64 * regsVal s' (pAccs (c + 1 + w)) =
        regsVal s (pAccs (c + w)) + pSum s.mem base (fTerms M a b c) +
          (if c < w then (word s'.mem base (M.tmp + 8 * (c % w))).toNat * (word s.mem base M.mo).toNat
            else 0) ∧
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' ∧
      Outside base (M.tmp + 8 * (c % w)) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hc9 := Nat.mod_lt c (show 0 < w by omega)
  have hok := pAccs_ok (c + w)
  have hsub := hok.2
  have hrdi : Reg.rdi ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs (c + w) := by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h
    all_goals first | exact absurd h (by decide) | exact absurd (hsub _ h) (by decide)
  have hkeep : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .r9, .r10, .r11] → r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs (c + w) :=
    fun r hr h => hr (by
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · have := hsub r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at this; grind)
  rw [fCol, hn, WP.block_append_iff]
  refine WP.mono (pTerms_ok (c + w) _ hs hin (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ hrdi
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  split
  · rename_i hc'
    have hcm : c % w = c := Nat.mod_eq_of_lt hc'
    rw [fRed, hn, show ([.mov .rax (.reg (pAcc (c + w) 0)), .movImm64 .rcx M.minv, .mul .rcx,
        .mov .rcx (.reg .rax), .store (sc (M.tmp + 8 * c)) .rcx, .mov .rax (.mem (sc M.mo)), .mul .rcx,
        .alu .add (pAcc (c + w) 0) (.reg .rax), .alu .adc (pAcc (c + w) 1) (.reg .rdx),
        .alu .adc (pAcc (c + w) 2) (.imm 0)] : List Instr) =
        [.mov .rax (.reg (pAcc (c + w) 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax),
          .store (sc (M.tmp + 8 * c)) .rcx] ++ [.mov .rax (.mem (sc M.mo)), .mul .rcx,
        .alu .add (pAcc (c + w) 0) (.reg .rax), .alu .adc (pAcc (c + w) 1) (.reg .rdx),
        .alu .adc (pAcc (c + w) 2) (.imm 0)] from rfl, WP.block_append_iff]
    refine WP.mono (fU_ok hs₁ (pAcc (c + w) 0) M.minv (t := M.tmp + 8 * c) (by omega))
      fun s₂ ⟨u₂, m₂, k₂⟩ => ?_
    have hs₂ := hs₁.of_keepRegs k₂ (by decide)
    have O₂ : Outside base (M.tmp + 8 * c) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    have hmo₂ : word s₂.mem base M.mo = word s.mem base M.mo := by
      rw [O₂.word (by omega) (by omega), hm₁]
    have hacc₂ : regsVal s₂ (pAccs (c + w)) = regsVal s₁ (pAccs (c + w)) :=
      regsVal_congr fun r hr => k₂.gpr r (by
        have := hsub r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
        grind)
    have hlow := regsVal_lt s₁ [pAcc (c + w) 1, pAcc (c + w) 2]
    have hu₂ : (s₂.gpr .rcx).toNat < 2 ^ 64 := (s₂.gpr .rcx).isLt
    refine WP.mono (pMulAcc_ok hs₂ hok.1 (dx := M.mo) (by omega) (by
      rw [show [pAcc (c + w) 0, pAcc (c + w) 1, pAcc (c + w) 2] = pAccs (c + w) from rfl, hacc₂, e₁, hmo₂]
      have := Nat.mul_le_mul (Nat.le_of_lt (word s.mem base M.mo).isLt) (Nat.le_of_lt hu₂)
      have : (2 ^ 64 - 1) * (2 ^ 64 - 1) < 2 ^ 128 := by decide
      omega_arith)) fun s₃ ⟨e₃, k₃, _⟩ => ?_
    rw [show [pAcc (c + w) 0, pAcc (c + w) 1, pAcc (c + w) 2] = pAccs (c + w) from rfl, hacc₂, hmo₂] at e₃
    have hm₃ : s₃.mem = s₂.mem := k₃.2.1
    -- The low word is now zero.
    have hz : (s₃.gpr (pAcc (c + w) 0)).toNat = 0 := by
      have e0 : regsVal s₁ (pAccs (c + w)) % 2 ^ 64 = (s₁.gpr (pAcc (c + w) 0)).toNat := by
        simp only [pAccs, regsVal]; omega
      have e3 : regsVal s₃ (pAccs (c + w)) % 2 ^ 64 = (s₃.gpr (pAcc (c + w) 0)).toNat := by
        simp only [pAccs, regsVal]; omega
      have hu : (s₂.gpr .rcx).toNat = (s₁.gpr (pAcc (c + w) 0)).toNat * M.minv.toNat % 2 ^ 64 := u₂
      rw [← e3, e₃, hu, Nat.add_mod, e0, Nat.mul_comm (word s.mem base M.mo).toNat]
      have := mont_low (s₁.gpr (pAcc (c + w) 0)).toNat M.minv.toNat (word s.mem base M.mo).toNat hinv
      rwa [Nat.add_mod, Nat.mod_eq_of_lt (s₁.gpr (pAcc (c + w) 0)).isLt] at this
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.zero_add, hcm, hm₃, m₂, word_writeW_self, show c + 1 + w = c + w + 1 by omega, pAccs_succ]
      have h3 : regsVal s₃ (pAccs (c + w)) =
          2 ^ 64 * regsVal s₃ [pAcc (c + w) 1, pAcc (c + w) 2, pAcc (c + w) 0] := by
        simp only [pAccs, regsVal, hz]; omega
      rw [← h3, e₃, e₁, Nat.mul_comm (word s.mem base M.mo).toNat]
    · refine ⟨fun r hr => ?_, k₃.2.2.1.trans (k₂.rd.trans k₁.2.2.1), k₃.2.2.2.trans (k₂.wr.trans k₁.2.2.2)⟩
      have h1 := hkeep r hr
      have h3 : r ∉ [Reg.rax, .rdx, pAcc (c + w) 0, pAcc (c + w) 1, pAcc (c + w) 2] := fun h => h1 (by
        simp only [pAccs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)
      have h2 : r ∉ [Reg.rax, .rcx, .rdx] := fun h => h1 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)
      rw [k₃.1 r h3, k₂.gpr r h2, k₁.1 r h1]
    · rw [hcm, hm₃]; exact fun x hx => by rw [O₂ x hx, hm₁]
  · rename_i hc'
    have hcm : c % w = c - w := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    refine WP.mono (pEnd_ok hs₁ (c + w) (t := M.tmp + 8 * (c - w)) (by omega)) fun s₂ ⟨m₂, e₂, k₂⟩ => ?_
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.add_zero, hcm, m₂, word_writeW_self, ← e₁, e₂,
        show c + 1 + w = c + w + 1 by omega]
      rfl
    · refine ⟨fun r hr => ?_, k₂.rd.trans k₁.2.2.1, k₂.wr.trans k₁.2.2.2⟩
      have h1 := hkeep r hr
      rw [k₂.gpr r (fun h => h1 (by simp only [List.mem_singleton] at h; simp [h, pAccs])), k₁.1 r h1]
    · rw [hcm, m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega)

/-! ## The columns' arithmetic -/

/-- `Σ f i · g j` over `i + j = c`, `i, j < w`. -/
def prodCol (w : Nat) (f g : Nat → Nat) (c : Nat) : Nat :=
  (((List.range w).filter fun i => i ≤ c ∧ c - i < w).map fun i => f i * g (c - i)).sum

/-- `Σ l k · g j` over `k + j = c`, `k < c`, `k, j < w`: the reduction's terms
but the column's own `u`. -/
def redCol (w : Nat) (l g : Nat → Nat) (c : Nat) : Nat :=
  (((List.range w).filter fun k => k < c ∧ c - k < w).map fun k => l k * g (c - k)).sum

/-- Column `c`'s sum: its products, its reduction's terms, and for `c < w`
its own `u_c m₀`. -/
def fColSum (w : Nat) (A B Mw l : Nat → Nat) (c : Nat) : Nat :=
  prodCol w A B c + redCol w l Mw c + if c < w then l c * Mw 0 else 0

/-- All `2w` columns: `A B + U m`. -/
theorem fColSum_total (hw : w = 8 ∨ w = 9) (A B Mw l : Nat → Nat) :
    hval (fColSum w A B Mw l) 0 (2 * w) = hval A 0 w * hval B 0 w + hval l 0 w * hval Mw 0 w := by
  rcases hw with rfl | rfl <;>
  simp only [hval, fColSum, prodCol, redCol, List.range, List.range.loop, List.filter_cons, List.filter_nil,
    decide_eq_true_eq, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, and_true, and_false,
    ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
  all_goals generalize 2 ^ 64 = X
  all_goals grind

/-- A column's terms' sum, from the words they read. -/
theorem pSum_fTerms {m : Mem} {base : Addr} {M : Mod} {a b c : Nat} {A B Mw l : Nat → Nat} (hn : M.n = w)
    (hA : ∀ i < w, (word m base (a + 8 * i)).toNat = A i)
    (hB : ∀ j < w, (word m base (b + 8 * j)).toNat = B j)
    (hM : ∀ j < w, (word m base (M.mo + 8 * j)).toNat = Mw j)
    (hl : ∀ k < w, k < c → c - k < w → (word m base (M.tmp + 8 * k)).toNat = l k) :
    pSum m base (fTerms M a b c) = prodCol w A B c + redCol w l Mw c := by
  simp only [pSum, fTerms, hn, List.map_append, List.sum_append, List.map_map, prodCol, redCol]
  refine congrArg₂ (· + ·) (congrArg List.sum (List.map_congr_left fun i hi => ?_))
    (congrArg List.sum (List.map_congr_left fun k hk => ?_))
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    simp only [Function.comp, pY, hA i hi.1, hB (c - i) hi.2.2]
  · simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
    simp only [Function.comp, pY, hl k hk.1 hk.2.1 hk.2.2, hM (c - k) hk.2.2]

theorem fColSum_congr {A B Mw l l' : Nat → Nat} {c : Nat} (h : ∀ k ≤ c, l' k = l k) :
    fColSum w A B Mw l' c = fColSum w A B Mw l c := by
  unfold fColSum redCol
  rw [List.map_congr_left fun k hk => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
    rw [h k (by omega_using [hk])]]
  split
  · rw [h c (Nat.le_refl _)]
  · rfl

/-- An index in the two passes over a `w`-word buffer. -/
theorem mod_two_pass {w c : Nat} (hc : c < 2 * w) :
    c % w = if c < w then c else c - w := by
  split
  · exact Nat.mod_eq_of_lt ‹_›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `n` columns of `mulF`: the words they wrote (`l`: the `u`s and
the result's low words) where not yet overwritten, and the accumulator,
`hval (fColSum w A B m l) 0 n = hval e 0 n + 2^(64 n) acc` for the low words
`e` (zero for the first `w`). -/
theorem fCols_ok {s₀ : State} {base : Addr} {size : Nat} (hs : Scr s₀ base size) {M : Mod} {a b : Nat}
    (hn : M.n = w) (hw : 0 < w ∧ w ≤ 9) (htmp : M.tmp + (8 * w) ≤ size) (hmo : M.mo + (8 * w) ≤ size) (ha : a + (8 * w) ≤ size)
    (hb : b + (8 * w) ≤ size) (hsep : M.mo + (8 * w) ≤ M.tmp ∨ M.tmp + (8 * w) ≤ M.mo)
    (haT : a + (8 * w) ≤ M.tmp ∨ M.tmp + (8 * w) ≤ a) (hbT : b + (8 * w) ≤ M.tmp ∨ M.tmp + (8 * w) ≤ b)
    (hinv : ((word s₀.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (h0 : regsVal s₀ (pAccs w) = 0) :
    ∀ n ≤ (2 * w), WP isa (.block ((List.range n).flatMap (fCol M a b))) s₀ fun s =>
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s₀ s ∧ Outside base M.tmp (8 * w) s₀.mem s.mem ∧
      regsVal s (pAccs (n + w)) < 2 ^ 128 ∧
      ∃ l : Nat → Nat, (∀ c < n, l c < 2 ^ 64) ∧
        (∀ c < n, n ≤ c + w → (word s.mem base (M.tmp + 8 * (c % w))).toNat = l c) ∧
        hval (fColSum w (fun i => (word s₀.mem base (a + 8 * i)).toNat)
          (fun j => (word s₀.mem base (b + 8 * j)).toNat) (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat) l)
          0 n = hval (fun c => if c < w then 0 else l c) 0 n + (2 ^ 64) ^ n * regsVal s (pAccs (n + w))
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _, by rw [Nat.zero_add, h0]; decide,
      fun _ => 0, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      by simp [hval, h0]⟩
  | n + 1, hn18 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (fCols_ok hs hn hw htmp hmo ha hb hsep haT hbT hinv h0 n (by omega_arith))
      fun s ⟨k, O, hacc, l, hl64, hlm, e⟩ => ?_
    have hnw := hs.nowrap
    have hsS : Scr s base size := hs.of_keepRegs k (by decide)
    have hA : ∀ i < w, (word s.mem base (a + 8 * i)).toNat = (word s₀.mem base (a + 8 * i)).toNat :=
      fun i hi => by rw [O.word (by omega_arith) (by omega_arith)]
    have hB : ∀ j < w, (word s.mem base (b + 8 * j)).toNat = (word s₀.mem base (b + 8 * j)).toNat :=
      fun j hj => by rw [O.word (by omega_arith) (by omega_arith)]
    have hM : ∀ j < w, (word s.mem base (M.mo + 8 * j)).toNat = (word s₀.mem base (M.mo + 8 * j)).toNat :=
      fun j hj => by rw [O.word (by omega_arith) (by omega_arith)]
    have hL : ∀ k < w, k < n → n - k < w → (word s.mem base (M.tmp + 8 * k)).toNat = l k :=
      fun k h9 hk hk' => by
      have := hlm k hk (by omega_arith)
      rwa [Nat.mod_eq_of_lt (show k < w by omega_arith)] at this
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
      · exact ⟨by omega_arith, fun d hd => by simp only [Option.some.injEq] at hd; omega_arith⟩
      · exact ⟨by omega_arith, fun d hd => by simp only [Option.some.injEq] at hd; omega_arith⟩
    have hinv' : ((word s.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0 := by
      rw [O.word (by omega_arith) (by omega_arith)]; exact hinv
    have hn9 := Nat.mod_lt n (show 0 < w by omega_arith)
    refine WP.mono (fCol_ok hsS hn hw.1 (by omega_arith) htmp hmo hsep hinv' hin (by omega_arith))
        fun s' ⟨e', k', O'⟩ => ?_
    have hm0 := hM 0 hw.1
    simp only [Nat.mul_zero, Nat.add_zero] at hm0
    rw [hm0] at e'
    have hword := (word s'.mem base (M.tmp + 8 * (n % w))).isLt
    have hm64 := (word s₀.mem base M.mo).isLt
    refine ⟨k.trans k', O.trans (O'.mono (by omega_arith) (by omega_arith)), ?_,
      fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % w))).toNat else l c, ?_, ?_, ?_⟩
    · have hp : (word s'.mem base (M.tmp + 8 * (n % w))).toNat * (word s₀.mem base M.mo).toNat ≤
          (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
      rw [show n + 1 + w = n + 1 + w from rfl]
      split at e' <;> omega_arith
    · intro c hc
      by_cases h : c = n
      · simp only [h, ite_true]; exact hword
      · simp only [h, ite_false]; exact hl64 c (by omega_arith)
    · intro c hc hc9
      by_cases h : c = n
      · subst h; simp
      · simp only [h, ite_false]
        have hc9' := Nat.mod_lt c (show 0 < w by omega_arith)
        have hne : c % w ≠ n % w := by
          rw [mod_two_pass (by omega_arith), mod_two_pass (by omega_arith)]
          by_cases hcW : c < w <;> by_cases hnW : n < w <;>
            simp only [hcW, hnW, ite_true, ite_false] <;> omega_arith
        rw [O'.word (by omega_arith) (by omega_arith)]
        exact hlm c (by omega_arith) (by omega_arith)
    · rw [hval_succ_last, hval_succ_last, Nat.zero_add]
      rw [hval_congr (g := fColSum w (fun i => (word s₀.mem base (a + 8 * i)).toNat)
          (fun j => (word s₀.mem base (b + 8 * j)).toNat) (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat) l)
          (fun c _ hc => fColSum_congr fun k hk => ite_eq_right_iff.mpr fun h => absurd h (by omega_arith)),
        hval_congr (f := fun c => if c < w then 0 else
            (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % w))).toNat else l c) c)
          (g := fun c => if c < w then 0 else l c)
          (fun c _ hc => by simp only [show c ≠ n by omega_arith, ite_false]),
        e]
      have hcol : fColSum w (fun i => (word s₀.mem base (a + 8 * i)).toNat)
          (fun j => (word s₀.mem base (b + 8 * j)).toNat) (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat)
          (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % w))).toNat else l c) n =
          pSum s.mem base (fTerms M a b n) +
            if n < w then (word s'.mem base (M.tmp + 8 * (n % w))).toNat * (word s₀.mem base M.mo).toNat
            else 0 := by
        rw [hsum]
        unfold fColSum
        rw [show redCol w (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % w))).toNat else l c)
            (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat) n =
            redCol w l (fun j => (word s₀.mem base (M.mo + 8 * j)).toNat) n by
          unfold redCol
          refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
          simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hk
          simp only [show k ≠ n by omega_arith, ite_false]]
        split <;> simp only [ite_true, Nat.mul_zero, Nat.add_zero, Nat.add_assoc]
      rw [hcol, pow64_succ', Nat.mul_comm (2 ^ 64) ((2 ^ 64) ^ n), Nat.mul_assoc]
      generalize (2 ^ 64) ^ n = Q
      rw [Nat.add_assoc, ← Nat.mul_add, ← Nat.add_assoc, ← e', Nat.mul_add]
      simp only [↓reduceIte, Nat.add_assoc]

theorem hval_zero : ∀ k n, hval (fun _ => 0) k n = 0
  | _, 0 => rfl
  | k, n + 1 => by rw [hval, hval_zero (k + 1) n]

/-- The arithmetic of `mulF`: from the columns' value `A B + U m =
X^w W + X^(2w) acc` (`X = 2⁶⁴`), `acc ≤ 1` and `W + X^w acc < 2m`. -/
theorem mulF_arith {X A B U W m acc : Nat} (hm : m < X ^ w) (hA : A < X ^ w) (hB : B < m) (hU : U < X ^ w)
    (e : A * B + U * m = X ^ w * W + X ^ w * X ^ w * acc) :
    acc ≤ 1 ∧ W + X ^ w * acc < 2 * m ∧ X ^ w * (W + X ^ w * acc) = A * B + U * m := by
  have eT : X ^ w * (W + X ^ w * acc) = A * B + U * m := by rw [Nat.mul_add, ← Nat.mul_assoc]; omega_using [e]
  have hAB : A * B < X ^ w * m := Nat.mul_lt_mul'' hA hB
  have hUm' : U * m < X ^ w * m := Nat.mul_lt_mul_of_pos_right hU (by omega_using [hB])
  have hT : W + X ^ w * acc < 2 * m := by
    have : X ^ w * (W + X ^ w * acc) < X ^ w * (2 * m) := by rw [eT, Nat.mul_left_comm]; omega_using [hAB, hUm']
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨?_, hT, eT⟩
  rcases Nat.lt_or_ge acc 2 with h | h
  · omega_using [h]
  · have : X ^ w * 2 ≤ X ^ w * acc := Nat.mul_le_mul_left _ h
    omega_using [hm, hT, this]

/-- `[o] = [a] [b] R⁻¹ mod m` for a modulus `m` of eight or nine words, `R = 2^(64w)`. -/
theorem mulF_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hn9 : M.n = w) (hw : w = 8 ∨ w = 9) {o a b : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mulF M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hw0 : 0 < w := by omega
  have hw9 : w ≤ 9 := by omega
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
  have h0 : regsVal s₁ (pAccs w) = 0 :=
    regsVal_zero fun r hr => z₁ r ((pAccs_ok w).2 r hr)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hinv₁ : ((word s₁.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hm₁]
    rw [← hmv, show wordsVal s.mem base M.mo w = (word s.mem base M.mo).toNat +
      2 ^ 64 * wordsVal s.mem base (M.mo + 8) (w - 1) by
        cases hw <;> rename_i hw <;> subst hw <;> rfl, Nat.add_mul, Nat.mul_assoc, Nat.add_right_comm,
      Nat.add_mul_mod_self_left] at hinv
    exact hinv
  rw [WP.block_append_iff]
  refine WP.mono (fCols_ok hs₁ hn9 ⟨hw0, hw9⟩ (by omega_using [htmp]) (by omega_using [hmo]) (by omega_using [ha])
      (by omega_using [hb]) (by omega_using [hsep]) (by omega_using [haT])
    (by omega_using [hbT]) hinv₁ h0 (2 * w) (Nat.le_refl _)) fun s₂ ⟨k₂, O₂, _, l, hl64, hlm, e₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- The value of the columns.
  rw [fColSum_total hw, show 2 * w = w + w by omega, hval_add _ 0 w w, Nat.zero_add,
    hval_congr (k := 0) (n := w) (g := fun _ => 0) (fun c _ hc => ite_eq_left_iff.mpr fun h => absurd (by omega_using [hc]) h), hval_zero,
    hval_congr (k := w) (n := w) (g := l) (fun c hc _ => ite_eq_right_iff.mpr fun h => absurd h (by omega_using [hc])), Nat.zero_add,
    show (2 ^ 64) ^ (w + w) = (2 ^ 64) ^ w * (2 ^ 64) ^ w by rw [Nat.pow_add]] at e₂
  have hA : wordsVal s.mem base a w = hval (fun i => (word s₁.mem base (a + 8 * i)).toNat) 0 w := by
    rw [← wordsVal_hval s₁.mem base a 0 w, hm₁, Nat.mul_zero, Nat.add_zero]
  have hBv : wordsVal s.mem base b w = hval (fun j => (word s₁.mem base (b + 8 * j)).toNat) 0 w := by
    rw [← wordsVal_hval s₁.mem base b 0 w, hm₁, Nat.mul_zero, Nat.add_zero]
  have hMv : m = hval (fun j => (word s₁.mem base (M.mo + 8 * j)).toNat) 0 w := by
    rw [← wordsVal_hval s₁.mem base M.mo 0 w, hm₁, Nat.mul_zero, Nat.add_zero, hmv]
  have hW : wordsVal s₂.mem base M.tmp w = hval l w w := by
    rw [show M.tmp = M.tmp + 8 * 0 from rfl, wordsVal_hval s₂.mem base M.tmp 0 w,
      show hval l w w = hval (fun j => l (j + w)) 0 w by
        simpa only [Nat.zero_add] using hval_shift l w 0 w]
    exact hval_congr fun c _ hc => by
      have := hlm (c + w) (by omega_using [hc]) (by omega_using [])
      rwa [show (c + w) % w = c by rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]] at this
  have hU : hval l 0 w < (2 ^ 64) ^ w := hval_lt fun c _ hc => hl64 c (by omega_using [hc])
  have hAlt : wordsVal s.mem base a w < (2 ^ 64) ^ w := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ w
  have hmlt : m < (2 ^ 64) ^ w := by rw [← hmv, ← Nat.pow_mul]; exact wordsVal_lt _ _ _ w
  rw [← hA, ← hBv, ← hMv, ← hW, show pAccs (w + w + w) = [.r9, .r10, .r11] by rcases hw with rfl | rfl <;> rfl] at e₂
  obtain ⟨hacc1, hT2, eT⟩ := mulF_arith hmlt hAlt hB hU e₂
  have hr9 : (s₂.gpr .r9).toNat = regsVal s₂ [.r9, .r10, .r11] := by simp only [regsVal] at hacc1 ⊢; omega_using [hacc1]
  have hmo₂ : wordsVal s₂.mem base M.mo w = m := by
    rw [O₂.wordsVal (by omega_using [hsep]) (by omega_using [hnw, hmo]), hm₁, hmv]
  refine WP.mono (csubW_ok hs₂ (M := M) (o := o) (m := m) (by omega_using [hn9, hw0]) (by omega_using [hn9, hmo]) (by omega_using [hn9, htmp])
    (by omega_using [hn9, ho]) (by omega_using [hn9, hoT]) (by omega_using [hn9, hoM]) (by rw [hn9]; exact hmo₂)
    (by rw [hr9, Nat.pow_mul, hn9]; exact hT2)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hr9, Nat.pow_mul, hn9] at e₃
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · have hcl : ∀ q ∈ [Reg.rax, .rcx, .rdx, .r8, .r9, .r10, .r11], q ∈ clob M.n := by
      rw [hn9]; rcases hw with rfl | rfl <;> decide
    rw [k₃.gpr r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind))),
      k₂.gpr r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind))),
      k₁.1 r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)))]
  · rw [k₃.rd, k₂.rd, k₁.2.2.1]
  · rw [k₃.wr, k₂.wr, k₁.2.2.2]
  · rw [O₃ x (by omega_using [hx]), O₂ x (by omega_using [hn9, hx']), hm₁]
  · rw [e₃]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₃, Nat.mod_mul_mod, Nat.mul_comm, eT]
    simp only [Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86_64
