module

public import VerifiedGarbage.Proof.Mont.X86_64.OpsReg
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86_64.MulP
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import Batteries.Logic

/-! ### `Mont.X86_64.MulF`, which the modules that import this one used -/

section

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
  obtain hs₁ := hs.of_keeps k₁ (by decide)
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
  obtain h1 := List.length_filter_le (fun i => decide (i ≤ c ∧ c - i < M.n)) (List.range M.n)
  obtain h2 := List.length_filter_le (fun k => decide (k < c ∧ c - k < M.n)) (List.range M.n)
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
  obtain hc9 := Nat.mod_lt c (show 0 < w by omega_arith)
  obtain hok := pAccs_ok (c + w)
  have hsub := hok.2
  obtain hrdi : Reg.rdi ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs (c + w) := by
    intro h
    simp only [List.mem_cons] at h
    rcases h with h | h | h | h
    all_goals first | exact absurd h (by decide) | exact absurd (hsub _ h) (by decide)
  obtain hkeep : ∀ r, r ∉ [Reg.rax, .rcx, .rdx, .r9, .r10, .r11] → r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs (c + w) :=
    fun r hr h => hr (by
      simp only [List.mem_cons] at h ⊢
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · have := hsub r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at this; grind)
  rw [fCol, hn, WP.block_append_iff]
  refine WP.mono (pTerms_ok (c + w) _ hs hin (by omega_arith)) fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ hrdi
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  split
  · rename_i hc'
    obtain hcm : c % w = c := Nat.mod_eq_of_lt hc'
    rw [fRed, hn, show ([.mov .rax (.reg (pAcc (c + w) 0)), .movImm64 .rcx M.minv, .mul .rcx,
        .mov .rcx (.reg .rax), .store (sc (M.tmp + 8 * c)) .rcx, .mov .rax (.mem (sc M.mo)), .mul .rcx,
        .alu .add (pAcc (c + w) 0) (.reg .rax), .alu .adc (pAcc (c + w) 1) (.reg .rdx),
        .alu .adc (pAcc (c + w) 2) (.imm 0)] : List Instr) =
        [.mov .rax (.reg (pAcc (c + w) 0)), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax),
          .store (sc (M.tmp + 8 * c)) .rcx] ++ [.mov .rax (.mem (sc M.mo)), .mul .rcx,
        .alu .add (pAcc (c + w) 0) (.reg .rax), .alu .adc (pAcc (c + w) 1) (.reg .rdx),
        .alu .adc (pAcc (c + w) 2) (.imm 0)] from rfl, WP.block_append_iff]
    refine WP.mono (fU_ok hs₁ (pAcc (c + w) 0) M.minv (t := M.tmp + 8 * c) (by omega_arith))
      fun s₂ ⟨u₂, m₂, k₂⟩ => ?_
    obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
    obtain O₂ : Outside base (M.tmp + 8 * c) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    obtain hmo₂ : word s₂.mem base M.mo = word s.mem base M.mo := by
      rw [O₂.word (by omega_arith) (by omega_arith), hm₁]
    obtain hacc₂ : regsVal s₂ (pAccs (c + w)) = regsVal s₁ (pAccs (c + w)) :=
      regsVal_congr fun r hr => k₂.gpr r (by
        have := hsub r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
        grind)
    obtain hlow := regsVal_lt s₁ [pAcc (c + w) 1, pAcc (c + w) 2]
    obtain hu₂ : (s₂.gpr .rcx).toNat < 2 ^ 64 := (s₂.gpr .rcx).isLt
    refine WP.mono (pMulAcc_ok hs₂ hok.1 (dx := M.mo) (by omega_arith) (by
      rw [show [pAcc (c + w) 0, pAcc (c + w) 1, pAcc (c + w) 2] = pAccs (c + w) from rfl, hacc₂, e₁, hmo₂]
      have := Nat.mul_le_mul (Nat.le_of_lt (word s.mem base M.mo).isLt) (Nat.le_of_lt hu₂)
      have : (2 ^ 64 - 1) * (2 ^ 64 - 1) < 2 ^ 128 := by decide
      omega_arith)) fun s₃ ⟨e₃, k₃, _⟩ => ?_
    rw [show [pAcc (c + w) 0, pAcc (c + w) 1, pAcc (c + w) 2] = pAccs (c + w) from rfl, hacc₂, hmo₂] at e₃
    have hm₃ : s₃.mem = s₂.mem := k₃.2.1
    -- The low word is now zero.
    obtain hz : (s₃.gpr (pAcc (c + w) 0)).toNat = 0 := by
      obtain e0 : regsVal s₁ (pAccs (c + w)) % 2 ^ 64 = (s₁.gpr (pAcc (c + w) 0)).toNat := by
        simp only [pAccs, regsVal]; omega_arith
      obtain e3 : regsVal s₃ (pAccs (c + w)) % 2 ^ 64 = (s₃.gpr (pAcc (c + w) 0)).toNat := by
        simp only [pAccs, regsVal]; omega_arith
      have hu : (s₂.gpr .rcx).toNat = (s₁.gpr (pAcc (c + w) 0)).toNat * M.minv.toNat % 2 ^ 64 := u₂
      rw [← e3, e₃, hu, Nat.add_mod, e0, Nat.mul_comm (word s.mem base M.mo).toNat]
      have := mont_low (s₁.gpr (pAcc (c + w) 0)).toNat M.minv.toNat (word s.mem base M.mo).toNat hinv
      rwa [Nat.add_mod, Nat.mod_eq_of_lt (s₁.gpr (pAcc (c + w) 0)).isLt] at this
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.zero_add, hcm, hm₃, m₂, word_writeW_self, show c + 1 + w = c + w + 1 by omega_arith, pAccs_succ]
      obtain h3 : regsVal s₃ (pAccs (c + w)) =
          2 ^ 64 * regsVal s₃ [pAcc (c + w) 1, pAcc (c + w) 2, pAcc (c + w) 0] := by
        simp only [pAccs, regsVal, hz]; omega_arith
      rw [← h3, e₃, e₁, Nat.mul_comm (word s.mem base M.mo).toNat]
    · refine ⟨fun r hr => ?_, k₃.2.2.1.trans (k₂.rd.trans k₁.2.2.1), k₃.2.2.2.trans (k₂.wr.trans k₁.2.2.2)⟩
      obtain h1 := hkeep r hr
      obtain h3 : r ∉ [Reg.rax, .rdx, pAcc (c + w) 0, pAcc (c + w) 1, pAcc (c + w) 2] := fun h => h1 (by
        simp only [pAccs, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)
      obtain h2 : r ∉ [Reg.rax, .rcx, .rdx] := fun h => h1 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)
      rw [k₃.1 r h3, k₂.gpr r h2, k₁.1 r h1]
    · rw [hcm, hm₃]; exact fun x hx => by rw [O₂ x hx, hm₁]
  · rename_i hc'
    obtain hcm : c % w = c - w := by
      rw [Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    refine WP.mono (pEnd_ok hs₁ (c + w) (t := M.tmp + 8 * (c - w)) (by omega_arith)) fun s₂ ⟨m₂, e₂, k₂⟩ => ?_
    refine ⟨?_, ?_, ?_⟩
    · rw [Nat.add_zero, hcm, m₂, word_writeW_self, ← e₁, e₂,
        show c + 1 + w = c + w + 1 by omega_arith]
      rfl
    · refine ⟨fun r hr => ?_, k₂.rd.trans k₁.2.2.1, k₂.wr.trans k₁.2.2.2⟩
      obtain h1 := hkeep r hr
      rw [k₂.gpr r (fun h => h1 (by simp only [List.mem_singleton] at h; simp [h, pAccs])), k₁.1 r h1]
    · rw [hcm, m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega_arith)

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

theorem hval_zero : ∀ k n, hval (fun _ => 0) k n = 0
  | _, 0 => rfl
  | k, n + 1 => by rw [hval, hval_zero (k + 1) n]

theorem hval_add_fun (f g : Nat → Nat) : ∀ k n, hval (fun c => f c + g c) k n = hval f k n + hval g k n
  | _, 0 => rfl
  | k, n + 1 => by
    rw [hval, hval, hval, hval_add_fun f g (k + 1) n, Nat.mul_add]
    simp only [Nat.add_assoc, Nat.add_left_comm]

theorem hval_mul_left (a : Nat) (f : Nat → Nat) : ∀ k n, hval (fun c => a * f c) k n = a * hval f k n
  | _, 0 => rfl
  | k, n + 1 => by
    rw [hval, hval, hval_mul_left a f (k + 1) n, Nat.mul_add, Nat.mul_left_comm]

theorem hval_sum (L : List Nat) (F : Nat → Nat → Nat) (k n : Nat) :
    hval (fun c => (L.map fun i => F i c).sum) k n = (L.map fun i => hval (F i) k n).sum := by
  induction L with
  | nil => exact hval_zero k n
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hval_add_fun (F i) (fun c => (L.map fun i => F i c).sum), ih]

theorem sum_map_filter {α} (L : List α) (p : α → Bool) (f : α → Nat) :
    ((L.filter p).map f).sum = (L.map fun x => if p x then f x else 0).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => by_cases h : p x <;> simp [h, ih]

theorem hval_eq_sum (f : Nat → Nat) : ∀ n, hval f 0 n = ((List.range n).map fun i => (2 ^ 64) ^ i * f i).sum
  | 0 => rfl
  | n + 1 => by
    rw [hval_succ_last, hval_eq_sum f n, List.range_succ, List.map_append, List.sum_append, Nat.zero_add]
    simp

/-- Row `i` of a product's columns: `X^i f i · g`. -/
theorem hval_row (w i : Nat) (hi : i < w) (a : Nat) (g : Nat → Nat) :
    hval (fun c => if i ≤ c ∧ c - i < w then a * g (c - i) else 0) 0 (2 * w) =
      (2 ^ 64) ^ i * (a * hval g 0 w) := by
  rw [show 2 * w = i + (w + (w - i)) by omega_using [hi], hval_add, hval_add,
    hval_congr (g := fun _ => 0) (fun c _ hc => ite_eq_right_iff.mpr fun h => absurd h (by omega_using [hc])), hval_zero,
    hval_congr (k := 0 + i + w) (g := fun _ => 0) (fun c hc _ => ite_eq_right_iff.mpr fun h => absurd h (by omega_using [hc])), hval_zero,
    Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
    hval_congr (k := i) (g := fun c => a * g (c - i)) (fun c hc hc' => ite_eq_left_iff.mpr fun h => absurd (by omega_using [hc, hc']) h),
    show i = 0 + i from (Nat.zero_add i).symm, hval_shift, hval_mul_left]
  simp only [Nat.add_sub_cancel, Nat.zero_add]

theorem sum_map_mul_right {α} (L : List α) (f : α → Nat) (b : Nat) :
    (L.map f).sum * b = (L.map fun x => f x * b).sum := by
  induction L with
  | nil => exact Nat.zero_mul b
  | cons x L ih => simp only [List.map_cons, List.sum_cons, Nat.add_mul, ih]

theorem sum_range_ite_eq (x : Nat → Nat) (c : Nat) : ∀ w,
    ((List.range w).map fun k => if k = c then x k else 0).sum = if c < w then x c else 0
  | 0 => rfl
  | w + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_ite_eq x c w]
    by_cases h : c < w
    · simp [h, show c < w + 1 by omega_using [h], show w ≠ c by omega_using [h]]
    · by_cases h' : w = c
      · subst h'; simp
      · simp [h, h', show ¬ c < w + 1 by omega_using [h, h']]

theorem sum_map_add_map {α} (L : List α) (f g : α → Nat) :
    (L.map f).sum + (L.map g).sum = (L.map fun x => f x + g x).sum := by
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons, List.sum_cons, ← ih]; omega_using []

theorem hval_prodCol (w : Nat) (f g : Nat → Nat) :
    hval (prodCol w f g) 0 (2 * w) = hval f 0 w * hval g 0 w := by
  have : prodCol w f g = fun c => ((List.range w).map fun i =>
      if i ≤ c ∧ c - i < w then f i * g (c - i) else 0).sum := by
    funext c; rw [prodCol, sum_map_filter]; simp only [decide_eq_true_eq]
  rw [this, hval_sum, hval_eq_sum f, sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
  rw [hval_row w i (List.mem_range.mp hi), Nat.mul_assoc]

/-- All `2w` columns: `A B + U m`. -/
theorem fColSum_total (hw : w = 8 ∨ w = 9) (A B Mw l : Nat → Nat) :
    hval (fColSum w A B Mw l) 0 (2 * w) = hval A 0 w * hval B 0 w + hval l 0 w * hval Mw 0 w := by
  obtain hw0 : 0 < w := by omega_using [hw]
  have : fColSum w A B Mw l = fun c => prodCol w A B c + prodCol w l Mw c := by
    funext c
    rw [fColSum, Nat.add_assoc]
    congr 1
    unfold redCol prodCol
    rw [sum_map_filter, sum_map_filter, show l c * Mw 0 = l c * Mw (c - c) by rw [Nat.sub_self],
      ← sum_range_ite_eq (fun k => l k * Mw (c - k)) c w, sum_map_add_map]
    refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
    simp only [decide_eq_true_eq]
    by_cases h : k = c
    · subst h; simp [hw0]
    · by_cases h' : k < c ∧ c - k < w
      · simp [h', h, show k ≤ c by omega_using [h']]
      · simp only [h', h, ite_false, Nat.add_zero]
        exact (ite_eq_right_iff.mpr fun h'' => absurd ⟨by omega_using [h, h''], h''.2⟩ h').symm
  rw [this, hval_add_fun, hval_prodCol, hval_prodCol]

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
  · rw [Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

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
    obtain hsS : Scr s base size := hs.of_keepRegs k (by decide)
    obtain hA : ∀ i < w, (word s.mem base (a + 8 * i)).toNat = (word s₀.mem base (a + 8 * i)).toNat :=
      fun i hi => by rw [O.word (by omega_arith) (by omega_arith)]
    obtain hB : ∀ j < w, (word s.mem base (b + 8 * j)).toNat = (word s₀.mem base (b + 8 * j)).toNat :=
      fun j hj => by rw [O.word (by omega_arith) (by omega_arith)]
    obtain hM : ∀ j < w, (word s.mem base (M.mo + 8 * j)).toNat = (word s₀.mem base (M.mo + 8 * j)).toNat :=
      fun j hj => by rw [O.word (by omega_arith) (by omega_arith)]
    obtain hL : ∀ k < w, k < n → n - k < w → (word s.mem base (M.tmp + 8 * k)).toNat = l k :=
      fun k h9 hk hk' => by
      have := hlm k hk (by omega_arith)
      rwa [Nat.mod_eq_of_lt (show k < w by omega_arith)] at this
    obtain hsum := pSum_fTerms (M := M) (c := n) hn hA hB hM hL
    obtain hpl := pSum_le s.mem base (fTerms M a b n) (fTerms_some M a b n)
    obtain hlen := fTerms_length M a b n
    rw [hn] at hlen
    obtain hlen' := Nat.mul_le_mul_right (2 ^ 128) hlen
    obtain hin : ∀ t ∈ fTerms M a b n, PIn size t := by
      intro t ht
      simp only [fTerms, hn, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with ⟨i, ⟨hi, -, hj⟩, rfl⟩ | ⟨i, ⟨hi, -, hj⟩, rfl⟩
      · exact ⟨by omega_arith, fun d hd => by simp only [Option.some.injEq] at hd; omega_arith⟩
      · exact ⟨by omega_arith, fun d hd => by simp only [Option.some.injEq] at hd; omega_arith⟩
    obtain hinv' : ((word s.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0 := by
      rw [O.word (by omega_arith) (by omega_arith)]; exact hinv
    obtain hn9 := Nat.mod_lt n (show 0 < w by omega_arith)
    refine WP.mono (fCol_ok hsS hn hw.1 (by omega_arith) htmp hmo hsep hinv' hin (by omega_arith))
        fun s' ⟨e', k', O'⟩ => ?_
    obtain hm0 := hM 0 hw.1
    simp only [Nat.mul_zero, Nat.add_zero] at hm0
    rw [hm0] at e'
    obtain hword := (word s'.mem base (M.tmp + 8 * (n % w))).isLt
    obtain hm64 := (word s₀.mem base M.mo).isLt
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
        obtain hc9' := Nat.mod_lt c (show 0 < w by omega_arith)
        obtain hne : c % w ≠ n % w := by
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
      obtain hcol : fColSum w (fun i => (word s₀.mem base (a + 8 * i)).toNat)
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

/-- The arithmetic of `mulF`: from the columns' value `A B + U m =
X^w W + X^(2w) acc` (`X = 2⁶⁴`), `acc ≤ 1` and `W + X^w acc < 2m`. -/
theorem mulF_arith {X A B U W m acc : Nat} (hm : m < X ^ w) (hA : A < X ^ w) (hB : B < m) (hU : U < X ^ w)
    (e : A * B + U * m = X ^ w * W + X ^ w * X ^ w * acc) :
    acc ≤ 1 ∧ W + X ^ w * acc < 2 * m ∧ X ^ w * (W + X ^ w * acc) = A * B + U * m := by
  obtain eT : X ^ w * (W + X ^ w * acc) = A * B + U * m := by rw [Nat.mul_add, ← Nat.mul_assoc]; omega_using [e]
  obtain hAB : A * B < X ^ w * m := Nat.mul_lt_mul'' hA hB
  obtain hUm' : U * m < X ^ w * m := Nat.mul_lt_mul_of_pos_right hU (by omega_using [hB])
  obtain hT : W + X ^ w * acc < 2 * m := by
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
  obtain hw0 : 0 < w := by omega_arith
  obtain hw9 : w ≤ 9 := by omega_arith
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
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain h0 : regsVal s₁ (pAccs w) = 0 :=
    regsVal_zero fun r hr => z₁ r ((pAccs_ok w).2 r hr)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain hinv₁ : ((word s₁.mem base M.mo).toNat * M.minv.toNat + 1) % 2 ^ 64 = 0 := by
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
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- The value of the columns.
  rw [fColSum_total hw, show 2 * w = w + w by omega_arith, hval_add _ 0 w w, Nat.zero_add,
    hval_congr (k := 0) (n := w) (g := fun _ => 0) (fun c _ hc => ite_eq_left_iff.mpr fun h => absurd (by omega_using [hc]) h), hval_zero,
    hval_congr (k := w) (n := w) (g := l) (fun c hc _ => ite_eq_right_iff.mpr fun h => absurd h (by omega_using [hc])), Nat.zero_add,
    show (2 ^ 64) ^ (w + w) = (2 ^ 64) ^ w * (2 ^ 64) ^ w by rw [Nat.pow_add]] at e₂
  obtain hA : wordsVal s.mem base a w = hval (fun i => (word s₁.mem base (a + 8 * i)).toNat) 0 w := by
    rw [← wordsVal_hval s₁.mem base a 0 w, hm₁, Nat.mul_zero, Nat.add_zero]
  obtain hBv : wordsVal s.mem base b w = hval (fun j => (word s₁.mem base (b + 8 * j)).toNat) 0 w := by
    rw [← wordsVal_hval s₁.mem base b 0 w, hm₁, Nat.mul_zero, Nat.add_zero]
  obtain hMv : m = hval (fun j => (word s₁.mem base (M.mo + 8 * j)).toNat) 0 w := by
    rw [← wordsVal_hval s₁.mem base M.mo 0 w, hm₁, Nat.mul_zero, Nat.add_zero, hmv]
  obtain hW : wordsVal s₂.mem base M.tmp w = hval l w w := by
    rw [show M.tmp = M.tmp + 8 * 0 from rfl, wordsVal_hval s₂.mem base M.tmp 0 w,
      show hval l w w = hval (fun j => l (j + w)) 0 w by
        simpa only [Nat.zero_add] using hval_shift l w 0 w]
    exact hval_congr fun c _ hc => by
      have := hlm (c + w) (by omega_using [hc]) (by omega_using [])
      rwa [show (c + w) % w = c by rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]] at this
  obtain hU : hval l 0 w < (2 ^ 64) ^ w := hval_lt fun c _ hc => hl64 c (by omega_using [hc])
  obtain hAlt : wordsVal s.mem base a w < (2 ^ 64) ^ w := by rw [← Nat.pow_mul]; exact wordsVal_lt _ _ _ w
  obtain hmlt : m < (2 ^ 64) ^ w := by rw [← hmv, ← Nat.pow_mul]; exact wordsVal_lt _ _ _ w
  rw [← hA, ← hBv, ← hMv, ← hW, show pAccs (w + w + w) = [.r9, .r10, .r11] by rcases hw with rfl | rfl <;> rfl] at e₂
  obtain ⟨hacc1, hT2, eT⟩ := mulF_arith hmlt hAlt hB hU e₂
  obtain hr9 : (s₂.gpr .r9).toNat = regsVal s₂ [.r9, .r10, .r11] := by simp only [regsVal] at hacc1 ⊢; omega_using [hacc1]
  obtain hmo₂ : wordsVal s₂.mem base M.mo w = m := by
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

end

end

/-!
# P-256 field subtraction on x86-64

The modulus limbs are all ones, `2³² - 1`, zero and `2⁶⁴ - 2³² + 1`.
Construct their borrow masks in registers, then add them directly to the
four-limb difference. The inputs may alias the output. No temporary memory
is written; the existing field-operation frame is preserved.
-/

@[expose] public section

namespace VG.Proof.Mont.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry)

/-- Form the masked P-256 modulus from the subtraction borrow. -/
theorem p256SubMask_ok (s : State) (c : Bool) (hx : s.gpr .rax = if c then -1 else 0) :
    WP isa (.block p256SubMask) s fun s' =>
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rcx).toNat +
        2 ^ 192 * (s'.gpr .rdx).toNat =
          (if c then 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff else 0) ∧
      Keeps [.rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [p256SubMask, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, readSrc32, State.setReg32, Option.bind_some, Option.map_some, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, reduceCtorEq, ↓reduceIte, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [hx]
    cases c <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      hr.1, hr.2, ite_false]

/-- The four-word carry chain adds the masked modulus. -/
theorem p256SubAdd_ok (s : State) :
    WP isa (.block p256SubAdd) s fun s' => ∃ c, s'.cf = some c ∧
      regsVal s' (low 4) + 2 ^ 256 * c.toNat = regsVal s (low 4) +
        ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rcx).toNat + 2 ^ 192 * (s.gpr .rdx).toNat) ∧
      Keeps (low 4) s s' := by
  apply WP.of_runBlock
  simp only [p256SubAdd, low, acc, List.take, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.bind_some, Option.map_some, regsVal, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, reduceCtorEq, ↓reduceIte,
    BitVec.ofNat_eq_ofNat, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e1 := add_carry (s.gpr .r8) (s.gpr .rax)
    have e2 := adc_carry (s.gpr .r9) (s.gpr .rcx)
      (decide (2 ^ 64 ≤ (s.gpr .r8).toNat + (s.gpr .rax).toNat))
    generalize decide (2 ^ 64 ≤ (s.gpr .r8).toNat + (s.gpr .rax).toNat) = c₁ at e1 e2 ⊢
    have e3 := adc_carry (s.gpr .r10) (BitVec.signExtend 64 (0#32))
      (decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .rcx).toNat + c₁.toNat))
    generalize decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .rcx).toNat + c₁.toNat) = c₂ at e2 e3 ⊢
    have e4 := adc_carry (s.gpr .r11) (s.gpr .rdx)
      (decide (2 ^ 64 ≤ (s.gpr .r10).toNat + (BitVec.signExtend 64 (0#32)).toNat + c₂.toNat))
    generalize decide (2 ^ 64 ≤ (s.gpr .r10).toNat + (BitVec.signExtend 64 (0#32)).toNat + c₂.toNat) = c₃ at e3 e4 ⊢
    have hz : (BitVec.signExtend 64 (0#32)).toNat = 0 := rfl
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- Subtraction specialized to the four limbs of P-256's field modulus. -/
theorem sub256_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hn4 : M.n = 4) (hm : m = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff)
    {o a b : Nat} (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub256 o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  simp only [hn4] at ho ha hb hA hB ⊢
  have hf : Fresh (low 4) := (fresh_top_low (n := 4) (by decide)).tail
  have hl : (low 4).length = 4 := rfl
  have hsub : ∀ r ∈ low 4, r ∈ clob M.n := by rw [hn4]; decide
  rw [sub256, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok (low 4) hs (a := a) (by simpa only [hl] using ha) hf)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainSub_ok hs₁ (t := .r8) (ts := [.r9, .r10, .r11]) (b := b) hb hf)
    fun s₂ ⟨c, c₂, e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₂ c₂) fun s₃ ⟨x₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p256SubMask_ok s₃ c x₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p256SubAdd_ok s₄) fun s₅ ⟨c', _, e₅, k₅⟩ => ?_
  have hs₅ := ((hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)).of_keeps k₅ (by decide)
  refine WP.mono (stores_ok (low 4) hs₅ (o := o) (by simpa only [hl] using ho) hf.1)
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₁ e₆ O₆
  change regsVal s₂ (low 4) + wordsVal s₁.mem base b 4 =
    regsVal s₁ (low 4) + 2 ^ 256 * c.toNat at e₂
  have hR₄ : regsVal s₄ (low 4) = regsVal s₂ (low 4) := by
    apply regsVal_congr
    intro r hr
    rw [k₄.1 r (by revert r; decide), k₃.1 r (by revert r; decide)]
  rw [hR₄, e₄, ← hm] at e₅
  rw [e₁, k₁.2.1] at e₂
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · have hr' : r ∉ low 4 := fun h => hr (hsub r h)
    have h4 : r ∉ [.rcx, .rdx] := by
      intro h; apply hr; rw [hn4]
      exact (by decide : ∀ r : Reg, r ∈ [.rcx, .rdx] → r ∈ clob 4) r h
    have h3 : r ∉ [.rax] := by
      intro h; apply hr; rw [hn4]
      exact (by decide : ∀ r : Reg, r ∈ [.rax] → r ∈ clob 4) r h
    rw [k₆.gpr r (by simp), k₅.1 r hr', k₄.1 r h4, k₃.1 r h3, k₂.1 r hr', k₁.1 r hr']
  · rw [k₆.rd, k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₆.wr, k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₆ x (by simpa only [hn4] using hx), k₅.2.1, k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  · rw [e₆]
    have hR₂ := regsVal_lt s₂ (low 4)
    have hR₅ := regsVal_lt s₅ (low 4)
    rw [hl] at hR₂ hR₅
    have hmX : m < 2 ^ 256 := by rw [hm]; decide
    cases c <;> cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero, Bool.false_eq_true, ite_false, ite_true] at e₂ e₅
    · rw [show wordsVal s.mem base a 4 + m - wordsVal s.mem base b 4 =
        (wordsVal s.mem base a 4 - wordsVal s.mem base b 4) + m by omega_arith, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    · omega_arith
    · omega_arith
    · rw [Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith

/-- The friendly reduction's words determine P-256's field modulus. -/
theorem p256_of_red {M : Mod} {m : Nat} (hred : M.red = .friendly p256Ws) (h : M.ok m = true) :
    M.n = 4 ∧ m = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff := by
  have h' := Mod.ok_red h
  rw [hred] at h'
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨⟨hn, hm⟩, hw⟩, -⟩ := h'
  have h1 : (m + 1) % 2 ^ 64 = 0 := by omega_arith
  have hw' : mwVal p256Ws = 0xffffffff0000000100000000000000000000000100000000 := by rfl
  have h2 := Nat.div_add_mod (m + 1) (2 ^ 64)
  rw [← hw, hw', h1, Nat.add_zero] at h2
  refine ⟨by rw [← hn]; rfl, ?_⟩
  omega_arith
end VG.Proof.Mont.X86_64
