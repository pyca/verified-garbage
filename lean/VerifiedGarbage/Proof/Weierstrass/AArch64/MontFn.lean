module

import VerifiedGarbage.Proof.Weierstrass.AArch64.MontSaves
public import VerifiedGarbage.Proof.Mont.AArch64.Csub
public import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Weierstrass.AArch64.MontRound`, which only this module used -/

section

/-!
# Montgomery products as functions on AArch64: rounds from registers

The functions' product (`Impl/Weierstrass/AArch64/Mont.lean`) multiplies by
words in registers only: `[b]`'s in `bRegsF`, and a general modulus's in
`mRegs`. Its rounds (`roundG`, `roundsG_ok`) are the inline product's
(`Proof/Mont/AArch64/Rounds.lean`) with those words in place of `bWords` and
`mWords`, for any registers the rounds do not write (`RoundSafe`), and for
P-384's `p` a reduction without its words (`redSparse_ok`); the reduction of
the result subtracts the modulus's words in registers (`csubM_ok`, as
`csubR_ok`); and the modulus's distinct words are built in their registers
(`constLoads_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-! ## Words in registers -/

/-- Registers the rounds read but do not write (`x1`–`x3`, `x23` and the
accumulator). -/
def RoundSafe (n : Nat) (rs : List Reg) : Prop := ∀ r ∈ rs, r ∉ Reg.x1 :: .x2 :: .x3 :: .x23 :: acc n

theorem RoundSafe.acc {n : Nat} {rs : List Reg} (h : RoundSafe n rs) {r : Reg} (hr : r ∈ rs) :
    r ∉ acc n := fun h' => h r hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ h'))))

theorem RoundSafe.ne {n : Nat} {rs : List Reg} (h : RoundSafe n rs) {r : Reg} (hr : r ∈ rs) :
    r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 :=
  ⟨fun e => h r hr (by simp [e]), fun e => h r hr (by simp [e]), fun e => h r hr (by simp [e])⟩

theorem rwVal_regWords (s : State) (base : Addr) (rs : List Reg) :
    rwVal s base (regWords rs) = regsVal s rs := rwVal_regs s base rs

theorem regWords_length (rs : List Reg) : (regWords rs).length = rs.length := List.length_map ..

/-- A row of products by words in registers that neither the accumulator nor
`x1`–`x3` is. -/
theorem rowOk_regs {size n : Nat} (hn : n < 10) (i : Nat) {rs : List Reg} (h : RoundSafe n rs) :
    RowOk size .x1 (wins n i) (regWords rs) where
  nodup := (fresh_wins hn i).1
  regs t ht := by have := wins_regs hn i t ht; exact ⟨this.1, this.2.2.1, this.2.2.2.1,
    this.2.2.2.2.2.2.2.1, this.2.1⟩
  ok w hw := by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
    exact ⟨(h.ne hr).2.1, (h.ne hr).2.2⟩
  reads w hw q hq := by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
    simp only [RWord.reads, Src.reads, Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact ⟨fun hm => h.acc hr (wins_sub_acc hn i _ hm), (h.ne hr).2.1, (h.ne hr).2.2⟩
  x2 := by decide
  x3 := by decide

/-- Registers the rounds do not write keep their values. -/
theorem regsVal_keep {n : Nat} {rs : List Reg} (h : RoundSafe n rs) {s s' : State}
    {ks : List Reg} (hk : Keeps ks s s') (hks : ∀ r ∈ ks, r ∈ Reg.x1 :: .x2 :: .x3 :: .x23 :: acc n) :
    regsVal s' rs = regsVal s rs :=
  regsVal_congr fun r hr => hk.gpr r fun h' => h r hr (hks r h')

/-! ## A round -/

/-- Round `i` of the product, for `[a]` through `ra`, the multiplicand's words
in `bs`, and P-384's sparse reduction (`sp`) or a friendly modulus's. -/
def roundG (M : Mod) (ra : Reg) (bs : List Reg) (sp : Bool) (i : Nat) : List Instr :=
  [.ldr .x .x1 ra (8 * i)] ++ row .x0 .x1 (prodWins M i) (regWords bs) ++
    if sp then redSparse M.n i else
    match M.red with
    | .general => []
    | .friendly ws => row .x0 (win M.n i 0) (wins M.n i).tail (ws.map (fWord (firstGen ws))) ++
      [.movz .x (win M.n i 0) 0 0]

/-! ## P-384's sparse reduction -/

/-- P-384's `p`, `2^384 - 2^128 - 2^96 + 2^32 - 1`. -/
abbrev p384 : Nat := 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

/-- `2^384 + 2^32`, `sparseWords`' value. -/
abbrev sparseVal : Nat := 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806632285274112

/-- `2^512`. -/
theorem pow512 : 2 ^ (64 * (6 + 2)) = 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by decide +kernel

/-- The sum after the sparse reduction's subtraction, which does not borrow:
`T + u (2^384 + 2^32) - u (2^128 + 2^96 + 1) = T + u p`. -/
theorem sparse_val {V u R b x2 x3 x23 : Nat} (hu : u < 2 ^ 64) (hR : R < 2 ^ (64 * (6 + 2))) (hb : b ≤ 1)
    (hx2 : x2 = u * 2 ^ 32 % 2 ^ 64) (hx3 : x3 + 2 ^ 64 * x23 = u / 2 ^ 32 + u)
    (he : R + (u + 2 ^ 64 * x2 + 2 ^ 128 * (x3 + 2 ^ 64 * x23)) = V + u * sparseVal + 2 ^ (64 * (6 + 2)) * b) :
    R = V + u * p384 := by
  rw [pow512] at hR he
  unfold sparseVal at he
  unfold p384
  obtain hs : u * 2 ^ 32 = u * 2 ^ 32 % 2 ^ 64 + 2 ^ 64 * (u / 2 ^ 32) := by omega_arith
  omega_arith

/-- The sum before the subtraction fits in eight words. -/
theorem sparse_bound {V u : Nat} (hV : V < 2 * p384 + (2 ^ 64 - 1) * p384) (hu : u < 2 ^ 64) :
    V + u * sparseVal < 2 ^ (64 * (6 + 2)) := by
  rw [pow512]; unfold sparseVal; unfold p384 at hV; omega_using [hV, hu]

theorem sparse_low {V t0 u : Nat} (ht : V % 2 ^ 64 = t0) (h : (t0 + u * p384) % 2 ^ 64 = 0) :
    (V + u * p384) % 2 ^ 64 = 0 := by
  obtain ht0 : t0 % 2 ^ 64 = t0 := by rw [← ht, Nat.mod_mod]
  obtain h2 := Nat.add_mod t0 (u * p384) (2 ^ 64)
  rw [h, ht0] at h2
  rw [Nat.add_mod V, ht]; exact h2.symm

theorem round_bound {T x y p : Nat} (hT : T < 2 * p) (hx : x ≤ (2 ^ 64 - 1) * p) (hy : y ≤ (2 ^ 64 - 1) * p) :
    T + x + y < 2 ^ 64 * (2 * p) := by omega_using [hT, hx, hy]

theorem sparseOk_eq {n m : Nat} (h : sparseOk n m = true) : n = 6 ∧ m = p384 := by
  simp only [sparseOk, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2⟩

/-- `x3 = ⌊x1 / 2^k⌋`. -/
theorem lsr3_ok (s : State) {k : Nat} (hk : k < 64) :
    WP isa (.block [.lsr .x .x3 .x1 k]) s fun s' =>
      (s'.gpr .x3).toNat = (s.gpr .x1).toNat / 2 ^ k ∧ Keeps [.x3] s s' ∧ s'.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show k < Size.x.bits from hk, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr]

/-- The words of `u (2^128 + 2^96 + 1)` but `u`: `u 2^32 mod 2^64` in `x2`, and
`⌊u / 2^32⌋ + u` in `x3` and its carry in `x23`, for `u` in `x1`. -/
theorem nWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.lsl .x .x2 .x1 32, .lsr .x .x3 .x1 32, .adds .x .x3 .x3 .x1, .adcs .x .x23 .x7 .x7]) s
      fun s' => (s'.gpr .x2).toNat = (s.gpr .x1).toNat * 2 ^ 32 % 2 ^ 64 ∧
        (s'.gpr .x3).toNat + 2 ^ 64 * (s'.gpr .x23).toNat = (s.gpr .x1).toNat / 2 ^ 32 + (s.gpr .x1).toNat ∧
        Keeps [.x2, .x3, .x23] s s' := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (piece_ok hs.ptr (x := .x1) (p := .shl 32) (by decide) (show 32 < 64 by decide))
    fun s₁ ⟨e₁, k₁, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (lsr3_ok s₁ (k := 32) (by decide)) fun s₂ ⟨e₂, k₂, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addc_ok s₂ .x3 .x3 .x1 true (c := false) rfl) fun s₃ ⟨e₃, c₃, k₃⟩ => ?_
  refine WP.mono (addc_ok s₃ .x23 .x7 .x7 false (c := s₃.c) rfl) fun s₄ ⟨e₄, _, k₄⟩ => ?_
  obtain x1₁ : s₁.gpr .x1 = s.gpr .x1 := k₁.gpr _ (by decide)
  obtain x1₂ : s₂.gpr .x1 = s.gpr .x1 := by rw [k₂.gpr _ (by decide), x1₁]
  obtain z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), hz]
  obtain v₃ := VG.Proof.Ed25519.Word64.addCarry_value (s₂.gpr .x3) (s₂.gpr .x1) false
  rw [← e₃, ← c₃, x1₂, e₂, x1₁] at v₃
  obtain v₄ := VG.Proof.Ed25519.Word64.addCarry_value (s₃.gpr .x7) (s₃.gpr .x7) s₃.c
  rw [← e₄, z₃] at v₄
  obtain c0 : (VG.Proof.Ed25519.Word64.carryOut 0 0 s₃.c).toNat = 0 := by cases s₃.c <;> rfl
  rw [c0] at v₄
  simp only [Bool.toNat_false] at v₃
  refine ⟨?_, ?_, ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans
    ((k₃.mono (by sub_regs)).trans (k₄.mono (by sub_regs)))⟩
  · rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide)]
    simpa only [Piece.reg, Piece.val] using e₁
  · have hx3 : s₄.gpr .x3 = s₃.gpr .x3 := k₄.gpr _ (by decide)
    obtain hc : (s₄.gpr .x23).toNat = s₃.c.toNat := by
      have := (s₄.gpr .x23).isLt
      have := Bool.toNat_le s₃.c
      have h0 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0] at v₄
      omega_using [v₄]
    rw [hx3, hc]
    omega_using [v₃]

/-- One word of the difference: `d = t - r - b` with the borrow `b = !c` in,
and its borrow out. -/
theorem diffM1_ok (s : State) (t d r : Reg) (first : Bool) {c : Bool}
    (hc : (if first then true else s.c) = c) :
    WP isa (.block [if first then .subs .x d t r else .sbcs .x d t r]) s
      fun s' => (s'.gpr d).toNat + (s.gpr r).toNat + (!c).toNat =
          (s.gpr t).toNat + 2 ^ 64 * (!s'.c).toNat ∧ Keeps [d] s s' :=
  WP.mono (subc_ok s d t r first hc) fun s' ⟨d', c', k'⟩ => ⟨by rw [d', c']; exact sub_borrow _ _ c, k'⟩

/-- `ts -= rs`, word by word in place, with the borrow `!c` in (`c` the carry
flag, set for the first word), and its borrow out. -/
theorem subsIn_ok : ∀ (first : Bool) (ts rs : List Reg) {s : State}, (first = false ∨ ts ≠ []) →
    ts.length = rs.length → ts.Nodup → (∀ r ∈ rs, r ∉ ts) →
    WP isa (.block (subsIn first ts rs)) s fun s' =>
      regsVal s' ts + regsVal s rs + (!(if first then true else s.c)).toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * (!s'.c).toNat ∧ Keeps ts s s'
  | first, [], [], s, h1, _, _, _ => by
    rcases h1 with rfl | h1
    · exact WP.block_nil ⟨by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · exact absurd rfl h1
  | _, [], _ :: _, _, _, hl, _, _ => absurd hl (by simp)
  | _, _ :: _, [], _, _, hl, _, _ => absurd hl (by simp)
  | first, t :: ts, r :: rs, s, _, hl, hnd, hrt => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    obtain ht := (List.nodup_cons.mp hnd)
    rw [subsIn, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (diffM1_ok s t t r first rfl) fun s₁ ⟨e₁, k₁⟩ => ?_
    refine WP.mono (subsIn_ok false ts rs (.inl rfl) hl ht.2 fun q hq hq' =>
      hrt q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ hq')) fun s₂ ⟨e₂, k₂⟩ => ?_
    obtain hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => ht.1 (h ▸ hq))
    obtain hM : regsVal s₁ rs = regsVal s rs := regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => hrt q (List.mem_cons_of_mem _ hq) (h ▸ List.mem_cons_self ..))
    obtain ht₂ : s₂.gpr t = s₁.gpr t := k₂.gpr t ht.1
    have hr : s.gpr r = s.gpr r := rfl
    simp only [Bool.false_eq_true, ite_false] at e₂
    rw [hR, hM] at e₂
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, List.length_cons, pow64_succ, ht₂]
    rw [Nat.mul_assoc]
    omega_using [e₁, e₂]

/-- `x1 = a_i` through `ra`, and `T += a_i B` for `B` in `bs`. -/
theorem prodRowG_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 10) {ra : Reg} {pa : Addr} {sa : Nat} (hpa : Ptr s ra pa sa)
    {bs : List Reg} (hbs : RoundSafe M.n bs) (hbl : bs.length = M.n)
    {i m : Nat} (ha : 8 * i + 8 ≤ sa) (hz : s.gpr .x7 = 0)
    (hm : m < 2 ^ (64 * M.n)) (hok : M.ok m = true) (hB : regsVal s bs < m)
    (hT : regsVal s (wins M.n i) < 2 * m) :
    WP isa (.block (([.ldr .x .x1 ra (8 * i)] : List Instr) ++ row .x0 .x1 (prodWins M i) (regWords bs))) s
      fun s' => regsVal s' (wins M.n i) = regsVal s (wins M.n i) +
          (word s.mem pa (8 * i)).toNat * regsVal s bs ∧
        Keeps (.x1 :: .x2 :: .x3 :: wins M.n i) s s' := by
  obtain hw := wins_regs hn i
  rw [WP.block_append_iff]
  refine WP.mono (ldR_ok hpa ha (by omega_using []) .x1) fun s₁ ⟨c₁, k₁, _⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (by decide), hz]
  obtain hT₁ : ∀ ts : List Reg, (∀ q ∈ ts, q ∈ wins M.n i) → regsVal s₁ ts = regsVal s ts :=
    fun ts hts => regsVal_congr fun q hq => k₁.gpr q (by simp [(hw q (hts q hq)).2.1])
  obtain hRB : rwVal s₁ base (regWords bs) = regsVal s bs := by
    rw [rwVal_regWords]
    exact regsVal_keep hbs k₁ (by sub_regs)
  obtain hA := (word s.mem pa (8 * i)).isLt
  obtain hAB : (word s.mem pa (8 * i)).toNat * regsVal s bs ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega_using []) (by omega_using [hB])
  obtain hlen : (wins M.n i).length = M.n + 2 := wins_length M.n i
  obtain htake : ∀ q ∈ (wins M.n i).take (M.n + 1), q ∈ wins M.n i := fun q hq => List.mem_of_mem_take hq
  obtain hdrop : ∀ q ∈ (wins M.n i).drop (M.n + 1), q ∈ wins M.n i := fun q hq => List.mem_of_mem_drop hq
  obtain hnd := (fresh_wins hn i).1
  obtain hdisj : ∀ q ∈ (wins M.n i).drop (M.n + 1), q ∉ (wins M.n i).take (M.n + 1) := fun q hq ht => by
    obtain hnd' : ((wins M.n i).take (M.n + 1) ++ (wins M.n i).drop (M.n + 1)).Nodup := by
      rw [List.take_append_drop]; exact hnd
    exact (List.nodup_append.mp hnd').2.2 q ht q hq rfl
  obtain hn0 : Reg.x0 ∉ wins M.n i := fun h => (hw _ h).1 rfl
  obtain hRO := rowOk_regs (size := size) hn i hbs
  by_cases ht : M.tight = true
  · rw [prodWins, ite_eq_left_iff.mpr (fun h => absurd ht h)]
    obtain hti := Mod.ok_tight hok ht
    obtain hRT : regsVal s ((wins M.n i).take (M.n + 1)) < 2 * m := by
      have := regsVal_wins_split s M.n i; omega_using [hT, this]
    obtain hP1 : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    refine WP.mono (row_ok hs₁.ptr hz₁ (hRO.sub (List.take_sublist _ _)) (by decide) (by decide)
        (fun h => hn0 (List.mem_of_mem_take h))
        (by rw [regWords_length, List.length_take, hlen]; omega_using [hbl]) (by
          rw [hT₁ _ htake, c₁, hRB, List.length_take, hlen, Nat.min_eq_left (by omega_using [])]
          omega_using [hAB, hti, hRT])) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono fun q hq => by
          simp only [List.mem_cons] at hq ⊢
          rcases hq with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (htake q h))))⟩
    obtain hd : ∀ q ∈ (wins M.n i).drop (M.n + 1), s₂.gpr q = s₁.gpr q := fun q hq => k₂.gpr q (by
      have := hw q (hdrop q hq)
      simp only [List.mem_cons, not_or]
      exact ⟨this.2.2.1, this.2.2.2.1, hdisj q hq⟩)
    rw [regsVal_wins_split s₂, regsVal_wins_split s, e₂, regsVal_congr hd, hT₁ _ hdrop, hT₁ _ htake,
      c₁, hRB]
    omega_using []
  · rw [prodWins, ite_eq_right_iff.mpr (fun h => absurd h ht)]
    obtain hP : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
      rw [show 64 * (M.n + 2) = 64 * M.n + 64 + 64 by omega_using [], Nat.pow_add, Nat.pow_add]
    obtain hmX : m ≤ 2 ^ (64 * M.n) := Nat.le_of_lt hm
    refine WP.mono (row_ok hs₁.ptr hz₁ hRO (by decide) (by decide) hn0
        (by rw [regWords_length, hlen]; omega_using [hbl]) (by
        rw [hT₁ _ (fun _ h => h), c₁, hRB, hlen, hP]
        have : (2 ^ 64 - 1) * m ≤ (2 ^ 64 - 1) * 2 ^ (64 * M.n) := Nat.mul_le_mul_left _ hmX
        have : 2 ^ (64 * M.n) * 2 ^ 64 ≤ 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
        omega_arith)) fun s₂ ⟨e₂, k₂⟩ => ?_
    exact ⟨by rw [e₂, hT₁ _ (fun _ h => h), c₁, hRB],
      (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩

/-- Round `i`, with `x7 = 0`, the multiplicand `B` in `bs` and the reduction's
constant in `x6`: `2⁶⁴ T' = T + a_i B + u m`, and `T' < 2m` if `T < 2m`. -/
theorem roundG_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 10) {ra : Reg} {pa : Addr} {sa : Nat} (hpa : Ptr s ra pa sa)
    {bs : List Reg} (hbs : RoundSafe M.n bs) (hbl : bs.length = M.n) {sp : Bool} {i m : Nat}
    (hsp : sp = true → M.n = 6 ∧ m = p384 ∧ M.red = .general)
    (hfr : sp = false → ∃ ws, M.red = .friendly ws)
    (ha : 8 * i + 8 ≤ sa) (hz : s.gpr .x7 = 0)
    (hm' : m < 2 ^ (64 * M.n))
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true)
    (h6 : ConstOk M s) (hB : regsVal s bs < m) (hT : regsVal s (wins M.n i) < 2 * m) :
    WP isa (.block (roundG M ra bs sp i)) s fun s' =>
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem pa (8 * i)).toNat * regsVal s bs + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.x1 :: .x2 :: .x3 :: .x23 :: wins M.n i) s s' := by
  obtain hred := Mod.ok_red hok
  obtain hw := wins_regs hn i
  obtain n0 : Reg.x0 ∉ wins M.n i := fun h => (hw _ h).1 rfl
  obtain n6 : Reg.x6 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.1 rfl
  obtain n7 : Reg.x7 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.2.1 rfl
  obtain hcons := wins_cons M.n i
  obtain ht0 : win M.n i 0 ∈ wins M.n i := by rw [hcons]; exact List.mem_cons_self ..
  obtain hlen : (wins M.n i).length = M.n + 2 := wins_length M.n i
  obtain hAB : (word s.mem pa (8 * i)).toNat * regsVal s bs ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by have := (word s.mem pa (8 * i)).isLt; omega_using []) (by omega_using [hB])
  obtain hrot : ∀ t : State, (t.gpr (win M.n i 0)).toNat = 0 →
      2 ^ 64 * regsVal t (wins M.n (i + 1)) = regsVal t (wins M.n i) := by
    intro t h0
    rw [wins_succ, regsVal_append, hcons, regsVal]
    simp only [regsVal, h0, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  obtain hkw : ∀ q ∈ Reg.x1 :: Reg.x2 :: Reg.x3 :: wins M.n i, q ∈ Reg.x1 :: .x2 :: .x3 :: .x23 :: wins M.n i :=
    fun q hq => by
      simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  cases hspv : sp with
  | true =>
    obtain ⟨hn6, rfl, hrg⟩ := hsp hspv
    obtain hcode : roundG M ra bs true i = ([.ldr .x .x1 ra (8 * i)] ++ row .x0 .x1 (prodWins M i) (regWords bs)) ++
        redSparse M.n i := by simp only [roundG, ite_true]
    obtain h6' : s.gpr .x6 = M.minv := by unfold ConstOk at h6; rw [hrg] at h6; exact h6
    rw [hcode, WP.block_append_iff]
    refine WP.mono (prodRowG_ok hs hn hpa hbs hbl ha hz hm' hok hB hT) fun s₂ ⟨e₂, k₂⟩ => ?_
    obtain hs₂ := hs.of_keeps k₂ (by simp [n0])
    obtain hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    obtain h6₂ : s₂.gpr .x6 = M.minv := by rw [k₂.gpr _ (by simp [n6]), h6']
    rw [redSparse, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (mulU_ok s₂ (win M.n i 0)) fun s₃ ⟨u₃, k₃⟩ => ?_
    obtain hs₃ := hs₂.of_keeps k₃ (by decide)
    obtain hz₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr .x7 (by decide), hz₂]
    obtain hT₃ : regsVal s₃ (wins M.n i) = regsVal s₂ (wins M.n i) := regsVal_congr fun q hq =>
      k₃.gpr q (by simp [(hw q hq).2.1])
    obtain hu := (s₃.gpr .x1).isLt
    rw [WP.block_append_iff]
    obtain hRO : RowOk size .x1 (wins M.n i) sparseWords :=
      { nodup := (fresh_wins hn i).1
        regs := fun t ht => by have := hw t ht; exact ⟨this.1, this.2.2.1, this.2.2.2.1,
          this.2.2.2.2.2.2.2.1, this.2.1⟩
        ok := fun w hw' => by
          simp only [sparseWords, List.mem_cons, List.not_mem_nil, or_false] at hw'
          rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [RWord.Ok]
        reads := fun w hw' r hr => by
          simp only [sparseWords, List.mem_cons, List.not_mem_nil, or_false] at hw'
          rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [RWord.reads] at hr
        x2 := by decide
        x3 := by decide }
    obtain hlen8 : M.n + 2 = 6 + 2 := by rw [hn6]
    obtain hRS : rwVal s₃ base sparseWords = sparseVal := by
      simp only [sparseWords, rwVal, RWord.val, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    obtain hV₂ : regsVal s₂ (wins M.n i) < 2 * p384 + (2 ^ 64 - 1) * p384 := by
      rw [e₂]; exact Nat.add_lt_add_of_lt_of_le hT hAB
    refine WP.mono (row_ok hs₃.ptr hz₃ hRO (by decide) (by decide) n0
        (by rw [hlen, hn6]; decide) (by rw [hT₃, hRS, hlen, hlen8]; exact sparse_bound hV₂ hu))
      fun s₄ ⟨e₄, k₄⟩ => ?_
    rw [hT₃, hRS] at e₄
    obtain hs₄ := hs₃.of_keeps k₄ (by simp [n0])
    obtain hz₄ : s₄.gpr .x7 = 0 := by rw [k₄.gpr _ (by simp [n7]), hz₃]
    obtain x1₄ : s₄.gpr .x1 = s₃.gpr .x1 := k₄.gpr _ (by
      simp only [List.mem_cons, not_or]; exact ⟨by decide, by decide, fun h => (hw _ h).2.1 rfl⟩)
    rw [WP.block_append_iff]
    refine WP.mono (nWords_ok hs₄ hz₄) fun s₅ ⟨n₂, n₃, k₅⟩ => ?_
    obtain n23 : Reg.x23 ∉ wins M.n i := fun h => by
      have := wins_sub_acc hn i _ h; rw [hn6] at this; exact absurd this (by decide)
    obtain hT₅ : regsVal s₅ (wins M.n i) = regsVal s₄ (wins M.n i) := regsVal_congr fun q hq =>
      k₅.gpr q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (rfl | rfl | rfl)
        · exact (hw _ hq).2.2.1 rfl
        · exact (hw _ hq).2.2.2.1 rfl
        · exact n23 hq)
    obtain x1₅ : s₅.gpr .x1 = s₃.gpr .x1 := by rw [k₅.gpr _ (by decide), x1₄]
    obtain z₅ : s₅.gpr .x7 = 0 := by rw [k₅.gpr _ (by decide), hz₄]
    obtain hrs : ∀ r ∈ ([.x1, .x2, .x3, .x23] ++ List.replicate (M.n - 2) .x7 : List Reg),
        r ∉ wins M.n i := by
      intro r hr hr'
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_replicate] at hr
      rcases hr with (rfl | rfl | rfl | rfl) | ⟨-, rfl⟩
      · exact (hw _ hr').2.1 rfl
      · exact (hw _ hr').2.2.1 rfl
      · exact (hw _ hr').2.2.2.1 rfl
      · exact n23 hr'
      · exact n7 hr'
    refine WP.mono (subsIn_ok true (wins M.n i) ([.x1, .x2, .x3, .x23] ++ List.replicate (M.n - 2) .x7)
        (.inr (by rw [hcons]; exact List.cons_ne_nil _ _)) (by rw [hlen]; simp; omega_using [hlen8]) (fresh_wins hn i).1 hrs)
      fun s₆ ⟨e₆, k₆⟩ => ?_
    obtain hK : Keeps (.x1 :: .x2 :: .x3 :: .x23 :: wins M.n i) s s₆ :=
      (((k₂.mono hkw).trans (k₃.mono (by sub_regs))).trans ((k₄.mono (by sub_regs)).trans
        (k₅.mono (by sub_regs)))).trans (k₆.mono (by sub_regs))
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    obtain hN : regsVal s₅ ([.x1, .x2, .x3, .x23] ++ List.replicate (M.n - 2) .x7) =
        (s₃.gpr .x1).toNat + 2 ^ 64 * (s₅.gpr .x2).toNat +
          2 ^ 128 * ((s₅.gpr .x3).toNat + 2 ^ 64 * (s₅.gpr .x23).toNat) := by
      rw [hn6]
      simp only [show 6 - 2 = 4 from rfl, List.replicate, List.cons_append, List.nil_append, regsVal,
        z₅, h0, x1₅, Nat.mul_zero, Nat.add_zero]
      omega_using []
    rw [hT₅, hN, e₄, hlen, hlen8] at e₆
    simp only [ite_true, Bool.not_true, Bool.toNat_false, Nat.add_zero] at e₆
    obtain hRl := regsVal_lt s₆ (wins M.n i)
    rw [hlen, hlen8] at hRl
    -- The sum: `T + u p`, without a borrow.
    obtain hval : regsVal s₆ (wins M.n i) = regsVal s₂ (wins M.n i) + (s₃.gpr .x1).toNat * p384 :=
      sparse_val (V := regsVal s₂ (wins M.n i)) (u := (s₃.gpr .x1).toNat) (R := regsVal s₆ (wins M.n i))
        (b := (!s₆.c).toNat) (x2 := (s₅.gpr .x2).toNat) (x3 := (s₅.gpr .x3).toNat) (x23 := (s₅.gpr .x23).toNat)
        hu hRl (Bool.toNat_le _) (by rw [n₂, x1₄]) (by rw [n₃, x1₄]) e₆
    obtain h₆ : (regsVal s₆ (wins M.n i)) % 2 ^ 64 = (s₆.gpr (win M.n i 0)).toNat := by
      rw [hcons, regsVal]; omega_using []
    obtain hlow : (s₆.gpr (win M.n i 0)).toNat = 0 := by
      obtain ht0₂ : (regsVal s₂ (wins M.n i)) % 2 ^ 64 = (s₂.gpr (win M.n i 0)).toNat := by
        rw [hcons, regsVal]; omega_using []
      obtain h := mont_low (s₂.gpr (win M.n i 0)).toNat M.minv.toNat p384 hinv
      rw [h6₂] at u₃
      rw [← u₃] at h
      rw [← h₆, hval]
      exact sparse_low ht0₂ h
    obtain hum : (s₃.gpr .x1).toNat * p384 ≤ (2 ^ 64 - 1) * p384 := Nat.mul_le_mul (by omega_using []) (Nat.le_refl _)
    refine ⟨⟨(s₃.gpr .x1).toNat, by rw [hrot s₆ hlow, hval, e₂]⟩, ?_, ?_⟩
    · have : 2 ^ 64 * regsVal s₆ (wins M.n (i + 1)) < 2 ^ 64 * (2 * p384) := by
        rw [hrot s₆ hlow, hval, e₂]; exact round_bound hT hAB hum
      exact Nat.lt_of_mul_lt_mul_left this
    · exact hK
  | false =>
    obtain ⟨ws, hr⟩ := hfr hspv
    obtain hcode : roundG M ra bs false i = ([.ldr .x .x1 ra (8 * i)] ++ row .x0 .x1 (prodWins M i) (regWords bs)) ++
        (row .x0 (win M.n i 0) (wins M.n i).tail (ws.map (fWord (firstGen ws))) ++
          ([.movz .x (win M.n i 0) 0 0] : List Instr)) := by
      simp only [roundG, hr, Bool.false_eq_true, ite_false]
    have hok := hred
    rw [hr] at hok
    simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hwl, hm1⟩, hmv⟩, hwok⟩ := hok
    obtain h6' : ∀ v, firstGen ws = some v → s.gpr .x6 = BitVec.ofNat 64 v := by
      unfold ConstOk at h6; rw [hr] at h6; exact h6
    obtain hm2 : 2 ^ 64 * mwVal ws = m + 1 := by
      rw [hmv]
      have := Nat.div_add_mod (m + 1) (2 ^ 64)
      have : (m + 1) % 2 ^ 64 = 0 := by omega_using [hm1]
      omega_arith
    rw [hcode, WP.block_append_iff]
    refine WP.mono (prodRowG_ok hs hn hpa hbs hbl ha hz hm' hok hB hT) fun s₂ ⟨e₂, k₂⟩ => ?_
    obtain hs₂ := hs.of_keeps k₂ (by simp [n0])
    obtain hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    obtain h6₂ : ∀ v, firstGen ws = some v → s₂.gpr .x6 = BitVec.ofNat 64 v := fun v hv => by
      rw [k₂.gpr _ (by simp [n6]), h6' v hv]
    obtain hRF : rwVal s₂ base (ws.map (fWord (firstGen ws))) = mwVal ws := rwVal_fWords h6₂ ws hwok
    obtain hsplit : ∀ t : State, regsVal t (wins M.n i) =
        (t.gpr (win M.n i 0)).toNat + 2 ^ 64 * regsVal t (wins M.n i).tail := by
      intro t; rw [hcons]; rfl
    obtain htl : (wins M.n i).tail.length = M.n + 1 := by rw [wins_tail]; simp
    obtain hPt : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [show 64 * (M.n + 1) = 64 * M.n + 64 by omega_using [], Nat.pow_add]
    obtain hS := hsplit s₂
    obtain ht0v := (s₂.gpr (win M.n i 0)).isLt
    obtain htm : (s₂.gpr (win M.n i 0)).toNat * m ≤ (2 ^ 64 - 1) * m :=
      Nat.mul_le_mul (by omega_using []) (Nat.le_refl _)
    obtain hkey : 2 ^ 64 * (regsVal s₂ (wins M.n i).tail + (s₂.gpr (win M.n i 0)).toNat * mwVal ws) =
        regsVal s₂ (wins M.n i) + (s₂.gpr (win M.n i 0)).toNat * m := by
      rw [Nat.mul_add, Nat.mul_left_comm, hm2, Nat.mul_add, Nat.mul_one, hS]; omega_using []
    obtain hmP : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega_using [hm']) (by omega_using [])
    rw [WP.block_append_iff]
    refine WP.mono (row_ok hs₂.ptr hz₂ (rowOkF hn i hwok (firstGen ws)) (by decide) (by decide)
        (fun h => n0 (List.mem_of_mem_tail h)) (by
        rw [List.length_map, hwl, htl]; omega_using []) (by
        rw [hRF, htl, hPt]
        have : 2 ^ 64 * (regsVal s₂ (wins M.n i).tail + (s₂.gpr (win M.n i 0)).toNat * mwVal ws) <
            2 ^ 64 * (2 ^ (64 * M.n) * 2 ^ 64) := by
          rw [hkey, e₂]; omega_using [hT, hAB, htm, hmP]
        exact Nat.lt_of_mul_lt_mul_left this)) fun s₃ ⟨e₃, k₃⟩ => ?_
    rw [hRF] at e₃
    refine WP.mono (movz0_ok s₃ (win M.n i 0)) fun s₄ ⟨z₄, k₄⟩ => ?_
    have htl₄ : regsVal s₄ (wins M.n i).tail = regsVal s₃ (wins M.n i).tail := regsVal_congr
      fun q hq => k₄.gpr q (by
        obtain hnd := (fresh_wins hn i).1
        rw [hcons] at hnd
        simp only [List.mem_singleton]
        intro h; subst h
        exact (List.nodup_cons.mp hnd).1 (by rw [← wins_tail]; exact hq))
    obtain hval : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) = regsVal s₂ (wins M.n i) +
        (s₂.gpr (win M.n i 0)).toNat * m := by
      rw [wins_succ, regsVal_append, ← wins_tail, htl, htl₄, e₃]
      simp only [regsVal, z₄, Nat.mul_zero, Nat.add_zero]
      exact hkey
    refine ⟨⟨(s₂.gpr (win M.n i 0)).toNat, by rw [hval, e₂]⟩, ?_, ?_⟩
    · have : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) < 2 ^ 64 * (2 * m) := by
        rw [hval, e₂]; omega_using [hT, hAB, htm]
      exact Nat.lt_of_mul_lt_mul_left this
    · refine ((k₂.mono hkw).trans (k₃.mono ?_)).trans (k₄.mono ?_)
      · intro q hq
        simp only [List.mem_cons] at hq ⊢
        rcases hq with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (List.mem_of_mem_tail h))))
      · intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        simp only [List.mem_cons]
        exact Or.inr (Or.inr (Or.inr (Or.inr ht0)))

/-! ## The rounds -/

/-- `k` rounds, from a cleared accumulator. -/
theorem roundsG_ok {M : Mod} (hn : M.n < 10) {ra : Reg} {pa : Addr} {sa : Nat}
    (hra : ra ∉ Reg.x1 :: .x2 :: .x3 :: .x23 :: acc M.n) {bs : List Reg} (hbs : RoundSafe M.n bs)
    (hbl : bs.length = M.n) {sp : Bool} {m size : Nat}
    (hsp : sp = true → M.n = 6 ∧ m = p384 ∧ M.red = .general)
    (hfr : sp = false → ∃ ws, M.red = .friendly ws)
    (ha : 8 * M.n ≤ sa) (hm' : m < 2 ^ (64 * M.n))
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hok : M.ok m = true) :
    ∀ k ≤ M.n, ∀ {s : State} {base : Addr}, Scr s base size → Ptr s ra pa sa → s.gpr .x7 = 0 →
      ConstOk M s → regsVal s bs < m → regsVal s (wins M.n 0) = 0 →
      WP isa (.block ((List.range k).flatMap (roundG M ra bs sp))) s fun s' =>
        (∃ U, 2 ^ (64 * k) * regsVal s' (wins M.n k) =
          wordsVal s.mem pa 0 k * regsVal s bs + U * m) ∧
        regsVal s' (wins M.n k) < 2 * m ∧
        Keeps (.x1 :: .x2 :: .x3 :: .x23 :: acc M.n) s s'
  | 0, _, s, _, _, _, _, _, hB, h0 => WP.block_nil ⟨⟨0, by simp [h0, wordsVal]⟩, by rw [h0]; omega_using [hB],
      ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | k + 1, hk, s, base, hs, hpa, hz, h6, hB, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (roundsG_ok hn hra hbs hbl hsp hfr ha hm' hinv hok k (by omega_using [hk]) hs hpa hz h6 hB h0)
      fun s₁ ⟨⟨U, eU⟩, hT, k₁⟩ => ?_
    have hmem : s₁.mem = s.mem := k₁.mem
    obtain hacc := acc_regs_lt _ hn
    obtain nk : ∀ r ∈ [Reg.x0, .x6, .x7], r ∉ Reg.x1 :: Reg.x2 :: Reg.x3 :: Reg.x23 :: acc M.n := by
      intro r hr h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases h with h | h | h | h | h
      · rcases hr with rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl <;> exact absurd h (by decide)
      · have := hacc r h
        rcases hr with rfl | rfl | rfl <;> simp at this
    obtain hs₁ := hs.of_keeps k₁ (nk .x0 (by simp))
    obtain hpa₁ := hpa.of_keeps k₁ hra
    obtain hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (nk .x7 (by simp)), hz]
    obtain hB₁ : regsVal s₁ bs = regsVal s bs := regsVal_keep hbs k₁ (fun _ h => h)
    obtain h6₁ : ConstOk M s₁ := h6.keep (k₁.gpr .x6 (nk .x6 (by simp)))
    refine WP.mono (roundG_ok hs₁ hn hpa₁ hbs hbl hsp hfr (i := k) (by omega_using [ha, hk]) hz₁ hm' hinv hok h6₁
      (by rw [hB₁]; exact hB) hT) fun s₂ ⟨⟨u, eu⟩, hT₂, k₂⟩ => ?_
    rw [hmem, hB₁] at eu
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_⟩, hT₂, k₁.trans (k₂.mono fun q hq => ?_)⟩
    · calc 2 ^ (64 * (k + 1)) * regsVal s₂ (wins M.n (k + 1))
          = 2 ^ (64 * k) * (2 ^ 64 * regsVal s₂ (wins M.n (k + 1))) := by
            rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ (64 * k) * regsVal s₁ (wins M.n k) +
            2 ^ (64 * k) * (word s.mem pa (8 * k)).toNat * regsVal s bs +
            2 ^ (64 * k) * u * m := by rw [eu]; simp only [Nat.mul_add, Nat.mul_assoc]
        _ = (wordsVal s.mem pa 0 k + 2 ^ (64 * k) * (word s.mem pa (0 + 8 * k)).toNat) *
            regsVal s bs + (U + 2 ^ (64 * k) * u) * m := by
            rw [eU, Nat.add_mul, Nat.add_mul, Nat.zero_add]; omega_using []
        _ = _ := by rw [wordsVal_succ_top]
    · simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h | h
      any_goals simp only [h, true_or, or_true]
      exact Or.inr (Or.inr (Or.inr (Or.inr (wins_sub_acc hn k q h))))

/-! ## The reduction against registers -/

/-- The difference of `ts` and the words in `ms`, with the borrow `!c` in (`c`
the carry flag, set for the first word), into `ds`, and its borrow out. -/
theorem diffsM_ok : ∀ (first : Bool) (ts ds ms : List Reg) {s : State}, (first = false ∨ ts ≠ []) →
    ts.length = ds.length → ms.length = ts.length → Fresh ts → DRegs ds → (∀ r ∈ ms, r ∉ ds) →
    WP isa (.block (diffsM first ts ds ms)) s fun s' =>
      regsVal s' ds + regsVal s ms + (!(if first then true else s.c)).toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * (!s'.c).toNat ∧ Keeps ds s s'
  | first, [], [], [], s, h1, _, _, _, _, _ => by
    rcases h1 with rfl | h1
    · exact WP.block_nil ⟨by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · exact absurd rfl h1
  | _, [], _ :: _, _, _, _, hl, _, _, _, _ => absurd hl (by simp)
  | _, _ :: _, [], _, _, _, hl, _, _, _, _ => absurd hl (by simp)
  | _, [], [], _ :: _, _, _, _, hm, _, _, _ => absurd hm (by simp)
  | _, _ :: _, _ :: _, [], _, _, _, hm, _, _, _ => absurd hm (by simp)
  | first, t :: ts, d :: ds, r :: ms, s, _, hl, hm, hf, hd, hmd => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hm
    obtain hdP := hd.2 d (List.mem_cons_self ..)
    rw [diffsM, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (diffM1_ok s t d r first rfl) fun s₁ ⟨e₁, k₁⟩ => ?_
    refine WP.mono (diffsM_ok false ts ds ms (.inl rfl) hl hm hf.tail hd.tail fun q hq hq' =>
      hmd q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ hq')) fun s₂ ⟨e₂, k₂⟩ => ?_
    obtain hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      obtain hq' := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => dPool_fresh hdP hq' h.symm)
    obtain hM : regsVal s₁ ms = regsVal s ms := regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => hmd q (List.mem_cons_of_mem _ hq) (h ▸ List.mem_cons_self ..))
    obtain hd₂ : s₂.gpr d = s₁.gpr d := k₂.gpr d (List.nodup_cons.mp hd.1).1
    simp only [Bool.false_eq_true, ite_false] at e₂
    rw [hR, hM] at e₂
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, List.length_cons, pow64_succ, hd₂]
    rw [Nat.mul_assoc]
    omega_using [e₁, e₂]

/-- `csubM`: `ts + 2^(64 n) top < 2m` reduced modulo `m`, for `m` in the
registers `ms`, with `x7 = 0`. -/
theorem csubM_ok {s : State} {n : Nat} {ts ms : List Reg} {top : Reg} (hlen : ts.length = n)
    (hml : ms.length = n) (hn : 0 < n) (h7 : n < 10) (hf : Fresh (top :: ts))
    (hmd : ∀ r ∈ ms, r ∉ dRegs n) (hz : s.gpr .x7 = 0) {m : Nat} (hm : regsVal s ms = m)
    (hmX : m < 2 ^ (64 * n))
    (hV : regsVal s ts + 2 ^ (64 * n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csubM n ts top ms)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * n) * (s.gpr top).toNat) % m ∧
      Keeps (.x2 :: ts ++ dRegs n) s s' := by
  have hft := hf.tail
  have htop := hf.head
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htop
  obtain ⟨hD, hDl⟩ := dRegs_ok n h7
  obtain hDl' := hDl (by omega_using [h7])
  rw [csubM, List.append_assoc, WP.block_append_iff]
  refine WP.mono (diffsM_ok true ts (dRegs n) ms (.inr fun h => by subst h; simp at hlen; omega_using [hn, hlen]) (by rw [hlen, hDl']) (by rw [hml, hlen]) hft hD hmd)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (fun h => (dPool_ne _ (hD.2 _ h)).2.1 rfl), hz]
  rw [WP.block_append_iff]
  refine WP.mono (flagR_ok s₁ top hz₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  obtain htopP : ∀ d ∈ dRegs n, d ≠ top := fun d hd => dPool_fresh (hD.2 d hd) (by
    simp [htop.2.1, htop.2.2.1, htop.2.2.2.1, htop.2.2.2.2.1, htop.2.2.2.2.2.1, htop.2.2.2.2.2.2.1,
      htop.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.2.2])
  obtain htop₁ : s₁.gpr top = s.gpr top := k₁.gpr top fun h => htopP _ h rfl
  rw [htop₁] at x₂
  obtain hDs : ∀ q ∈ dRegs n, q ∉ [Reg.x2] := fun q hq hq' =>
    (dPool_ne q (hD.2 q hq)).1 (List.mem_singleton.mp hq')
  refine WP.mono (selectsR_ok ts (dRegs n) (decide ((s.gpr top).toNat < (!s₁.c).toNat))
    (s := s₂) (by rw [hlen, hDl']) hft hD x₂) fun s₃ ⟨e₃, k₃, _⟩ => ?_
  obtain hR₂ : regsVal s₂ ts = regsVal s ts := by
    rw [regsVal_congr fun q hq => k₂.gpr q (by
      have := hft.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact this.2.2.1)]
    exact regsVal_congr fun q hq => k₁.gpr q (by
      obtain hq' := hft.2 q hq
      exact fun h => dPool_fresh (hD.2 _ h) hq' rfl)
  obtain hD₂ : regsVal s₂ (dRegs n) = regsVal s₁ (dRegs n) :=
    regsVal_congr fun q hq => k₂.gpr q (hDs q hq)
  rw [hlen, hm] at e₁
  simp only [ite_true, Bool.not_true, Bool.toNat_false, Nat.add_zero] at e₁
  refine ⟨?_, (k₁.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr)).trans
      ((k₂.mono (by sub_regs)).trans (k₃.mono fun r hr =>
        List.mem_cons_of_mem _ (List.mem_append_left _ hr)))⟩
  rw [e₃, hR₂, hD₂]
  simp only [decide_eq_true_eq]
  obtain hDlt := regsVal_lt s₁ (dRegs n)
  rw [hDl'] at hDlt
  exact csub_arith (b := !s₁.c) hmX hDlt hV (by omega_using [e₁])

/-! ## Constants into registers -/

/-- Each pair's constant into its register, for distinct registers. -/
theorem constLoads_ok : ∀ (L : List (Reg × BitVec 64)) {s : State}, (L.map Prod.fst).Nodup →
    WP isa (.block (L.flatMap fun p => const64 p.1 p.2)) s fun s' =>
      (∀ p ∈ L, s'.gpr p.1 = p.2) ∧ Keeps (L.map Prod.fst) s s'
  | [], s, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | p :: L, s, hnd => by
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (const64_ok s p.1 p.2) fun s₁ ⟨e₁, k₁⟩ => ?_
    obtain hnd' := List.nodup_cons.mp hnd
    refine WP.mono (constLoads_ok L hnd'.2) fun s₂ ⟨e₂, k₂⟩ => ⟨fun q hq => ?_,
      (k₁.mono (by intro r hr; simp only [List.mem_singleton] at hr; simp [hr])).trans
        (k₂.mono fun r hr => List.mem_cons_of_mem _ hr)⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [k₂.gpr _ hnd'.1, e₁]
    · exact e₂ q hq

/-- Registers holding the words of `x`, from word `j` on, hold `x`. -/
theorem regsVal_of_shifts (s : State) (f : Nat → Reg) : ∀ (j n x : Nat), x < 2 ^ (64 * n) →
    (∀ k < n, s.gpr (f (j + k)) = BitVec.ofNat 64 (x >>> (64 * k))) →
    regsVal s ((List.range' j n).map f) = x
  | _, 0, x, hx, _ => by simp only [Nat.mul_zero, Nat.pow_zero] at hx; simp only [List.range'_zero,
      List.map_nil, regsVal]; omega_using [hx]
  | j, n + 1, x, hx, h => by
    obtain h0 := h 0 (by omega_using [])
    simp only [Nat.mul_zero, Nat.add_zero, Nat.shiftRight_zero] at h0
    obtain hr := regsVal_of_shifts s f (j + 1) n (x >>> 64) (by
        rw [Nat.shiftRight_eq_div_pow]
        rw [pow64_succ] at hx
        exact Nat.div_lt_of_lt_mul hx) fun k hk => by
      rw [show j + 1 + k = j + (k + 1) by omega_using [], h (k + 1) (by omega_using [hk]), ← Nat.shiftRight_add,
        show 64 + 64 * k = 64 * (k + 1) by omega_using []]
    rw [List.range'_succ, List.map_cons, regsVal, hr, h0, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_add_div x _

end VG.Proof.Weierstrass.AArch64.Mont

end

end


/-!
# Montgomery products modulo a curve's `p` or `n`, as functions, on AArch64

`mulFn n m` (`Impl/Weierstrass/AArch64/Mont.lean`), from a state `Pre n m`
(`ws` in `x0` and the offsets in `w1`–`w3`, the working space the only
region, the numbers below the function's own working space), zero-extends the
offsets (`zext_ok`), saves the callee-saved registers it writes in vector
lanes (`saves_ok`) and computes its pointers (`ptrsF_ok`); its body
(`bodyF_ok`) loads `[b]` and the modulus into registers, runs the rounds
(`roundsG_ok`), reduces the result against the modulus in registers
(`csubM_ok`) and stores it; then it restores the registers (`mulFnS_ok`). The
function keeps the callee-saved registers, `x30`, `sp` and the low halves of
`v8`–`v15` (`abiPreserved`), changes the memory only at `[o]` (`Kept`), and
leaves `x0 = ws`, `x19` and `x20`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- An offset argument: the low 32 bits of its register. -/
abbrev arg (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- The function's own working space. -/
abbrev own (n : Nat) : Nat := Impl.Weierstrass.Mont.ownAt n

/-- The registers the body writes. -/
def bodyW (n : Nat) : List Reg := [.x1, .x2, .x3, .x6, .x7, .x23] ++ bRegsF n ++ mPool n ++ acc n ++ dRegs n

/-- The pointer additions. -/
def ptrsCode (n : Nat) : List Instr := [.add .x (roF n) .x0 .x1, .add .x (raF n) .x0 .x2, .add .x .x3 .x0 .x3]

/-- What follows the pointers: `[b]` into registers, the reduction's constant,
`x7` and the accumulator cleared, the rounds, the modulus into registers, the
reduction and the store. -/
def bodyCode (n m : Nat) : List Instr :=
  loadsR .x3 (bRegsF n) 0 ++ (mulConst (mod n m) ++
    ((zero7 :: zeros (acc n)) ++ ((List.range n).flatMap (roundF n m) ++
      (mLoadCode n m ++ (csubM n (lowF n) (win n n n) (mRegs n m) ++
        storesR (roF n) (lowF n) 0)))))

/-- Whether a reduction is a friendly modulus's. -/
def isFriendly : Red → Bool
  | .friendly _ => true
  | .general => false

theorem friendly_of {r : Red} (h : isFriendly r = true) : ∃ ws, r = .friendly ws := by
  cases r with
  | friendly ws => exact ⟨ws, rfl⟩
  | general => exact absurd h (by decide)

/-- What the function needs of the modulus `m` of `n` words: six or nine
words, `m` below `2^(64 n)`, `minv m` its inverse's negation, what the
multiplication needs of it, P-384's sparse `p` (reduced as a general one's
constant says) or a friendly modulus, `x6` free for `[b]` only where the
reduction needs no constant, each word of `m` in the register `mReg` once
`mLoadCode` builds them (in distinct registers), and code that writes no
vector register but the lanes'. -/
structure ModOkS (n m : Nat) : Prop where
  hn : n = 6 ∨ n = 9
  m_lt : m < 2 ^ (64 * n)
  inv : (m * minv m + 1) % 2 ^ 64 = 0
  red : (mod n m).ok m = true
  kind : (sparseOk n m = true ∧ (mod n m).red = .general) ∨
    (sparseOk n m = false ∧ ∃ ws, (mod n m).red = .friendly ws)
  x6 : Reg.x6 ∈ bRegsF n → mulConst (mod n m) = []
  loads : ∀ j < n, (mReg n m j, mWord m j) ∈ mLoads n m
  lnd : ((mLoads n m).map Prod.fst).Nodup
  novec : ∀ i ∈ ptrsCode n ++ bodyCode n m, vdstOf i = none

/-- The precondition, on the registers. -/
structure Pre (n W : Nat) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [⟨s.gpr .x0, W⟩]
  fit : (s.gpr .x0).toNat + W ≤ 2 ^ 64
  w : moAt n + 8 * n ≤ W
  w8 : W ≤ 8192
  o : arg s .x1 + 8 * n ≤ own n
  a : arg s .x2 + 8 * n ≤ own n
  b : arg s .x3 + 8 * n ≤ own n

/-- The memory changes only at `[o]` and at the modulus. -/
def Kept (n : Nat) (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + 8 * n ≤ ofs base x) →
    (ofs base x < moAt n ∨ moAt n + 8 * n ≤ ofs base x) → m' x = m x

theorem own_eq {n : Nat} (h : n ≤ 9) : own n + 64 * n = 4096 := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]; omega_arith

theorem minv_lt (m : Nat) : minv m < 2 ^ 64 := Nat.mod_lt _ (by decide)

/-! ## Facts of the registers, for each number of words -/

/-- What the code needs of its registers. -/
structure Regs (n : Nat) : Prop where
  n10 : n < 10
  bsafe : RoundSafe n (bRegsF n)
  macc : ∀ r ∈ mPool n, r ∉ acc n
  ra : raF n ∉ Reg.x1 :: .x2 :: .x3 :: .x23 :: acc n
  ro : roF n ∉ Reg.x1 :: .x2 :: .x3 :: .x23 :: acc n
  blen : (bRegsF n).length = n
  bnd : (bRegsF n).Nodup
  b3 : Reg.x3 ∉ bRegsF n
  bra : raF n ∉ bRegsF n
  bro : roF n ∉ bRegsF n
  b7 : Reg.x7 ∉ bRegsF n
  md : ∀ r ∈ mPool n, r ∉ dRegs n
  m2 : ∀ r ∈ mPool n, r ≠ .x2 ∧ r ≠ .x7 ∧ r ≠ roF n
  rod : roF n ∉ dRegs n
  r67 : raF n ≠ .x6 ∧ raF n ≠ .x7 ∧ roF n ≠ .x6 ∧ roF n ≠ .x7
  rom : roF n ∉ mPool n
  ra3 : raF n ≠ .x3 ∧ roF n ≠ .x3 ∧ raF n ≠ roF n ∧ raF n ≠ .x0 ∧ roF n ≠ .x0 ∧ raF n ≠ .x1 ∧
    raF n ≠ .x2 ∧ roF n ≠ .x1 ∧ roF n ≠ .x2
  slen : (saved n).length ≤ 10
  snd : (saved n).Nodup
  spres : ∀ r ∈ saved n, r ∈ preserved
  pres : ∀ r ∈ preserved, r ∉ saved n → r ∉ bodyW n ∧ r ≠ roF n ∧ r ≠ raF n
  keep0 : ∀ r ∈ [Reg.x0, .x19, .x20], r ∉ bodyW n ∧ r ∉ saved n ∧ r ≠ roF n ∧ r ≠ raF n
  nro : roF n ∉ bodyW n

theorem regs_ok : ∀ n, (n = 6 ∨ n = 9) → Regs n := by
  intro n hn
  rcases hn with rfl | rfl <;> constructor <;> first | decide | (unfold RoundSafe; decide)

/-! ## Words through pointers -/

theorem off_off (p : Addr) (e d : Nat) : off (off p e) d = off p (e + d) :=
  VG.Offset.add_ofNat_add_ofNat p e d

theorem wordsVal_off (m : Mem) (p : Addr) (e : Nat) : ∀ d k, wordsVal m (off p e) d k = wordsVal m p (e + d) k
  | _, 0 => rfl
  | d, k + 1 => by
    simp only [wordsVal, word, off_off, wordsVal_off m p e (d + 8) k, Nat.add_assoc]

theorem ofs_off_sub (p x : Addr) (e : Nat) (he : e < 2 ^ 64) :
    ofs (off p e) x = (2 ^ 64 - e + ofs p x) % 2 ^ 64 := by
  simp only [ofs, off]
  rw [VG.Offset.sub_add_eq, VG.Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt he]

/-- The changes at `[off p e]`, `len` bytes, are at `[e, e + len)` of `p`. -/
theorem Outside.of_off {p : Addr} {e len : Nat} {m m' : Mem} (h : Outside (off p e) 0 len m m')
    (he : e + len < 2 ^ 64) : Outside p e len m m' := fun x hx => h x (Or.inr (by
  rw [ofs_off_sub p x e (by omega_arith)]
  have := (x - p).isLt
  simp only [ofs] at hx ⊢
  rcases hx with hx | hx
  · rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  · rw [show 2 ^ 64 - e + (x - p).toNat = ((x - p).toNat - e) + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]; omega_arith))

/-! ## The entry -/

/-- The value of a zero-extended offset. -/
theorem zext_val (v : BitVec 64) :
    ((v.setWidth 32 + BitVec.ofNat 32 0).setWidth 64 : BitVec 64) = BitVec.ofNat 64 (v.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- The offsets zero-extended. -/
theorem zext_ok (s : State) :
    WP isa (.block [.addImm .w .x1 .x1 0, .addImm .w .x2 .x2 0, .addImm .w .x3 .x3 0]) s fun s' =>
      s'.gpr .x1 = BitVec.ofNat 64 (arg s .x1) ∧ s'.gpr .x2 = BitVec.ofNat 64 (arg s .x2) ∧
      s'.gpr .x3 = BitVec.ofNat 64 (arg s .x3) ∧ Keeps [.x1, .x2, .x3] s s' ∧ s'.v = s.v := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show (0 : Nat) < 4096 by decide,
    ite_true, Option.some.injEq, exists_eq_left', State.read]
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, zext_val]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, zext_val]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, zext_val]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

end VG.Proof.Weierstrass.AArch64.Mont

namespace VG.Proof.Weierstrass.AArch64.Mont

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Weierstrass.AArch64.Mont
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- The pointers: `ro = x0 + x1`, `ra = x0 + x2`, and `x3 = x0 + x3`. -/
theorem ptrsF_ok (s : State) {ra ro : Reg} (ha : ra ∉ [Reg.x0, .x1, .x2, .x3])
    (ho : ro ∉ [Reg.x0, .x1, .x2, .x3]) (hd : ra ≠ ro) :
    WP isa (.block [.add .x ro .x0 .x1, .add .x ra .x0 .x2, .add .x .x3 .x0 .x3]) s fun s' =>
      s'.gpr ro = s.gpr .x0 + s.gpr .x1 ∧ s'.gpr ra = s.gpr .x0 + s.gpr .x2 ∧
      s'.gpr .x3 = s.gpr .x0 + s.gpr .x3 ∧ Keeps [ra, .x3, ro] s s' ∧ s'.v = s.v := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha ho
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    State.read, BitVec.setWidth_eq]
  obtain e2 : ro ≠ ra := Ne.symm hd
  have := Ne.symm ha.1; have := Ne.symm ha.2.1; have := Ne.symm ha.2.2.1; have := Ne.symm ha.2.2.2
  have := Ne.symm ho.1; have := Ne.symm ho.2.1; have := Ne.symm ho.2.2.1; have := Ne.symm ho.2.2.2
  refine ⟨?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  all_goals simp only [RegUpd.gpr_write]
  all_goals simp_all

/-! ## The body -/

theorem regsVal_of_loads {s : State} {mem : Mem} {p : Addr} : ∀ (ts : List Reg) (a : Nat),
    (∀ j (r : Reg), ts[j]? = some r → s.gpr r = word mem p (a + 8 * j)) →
    regsVal s ts = wordsVal mem p a ts.length
  | [], _, _ => rfl
  | t :: ts, a, h => by
    obtain h0 := h 0 t rfl
    rw [Nat.mul_zero, Nat.add_zero] at h0
    obtain hr := regsVal_of_loads ts (a + 8) fun j r hr => by
      rw [h (j + 1) r (by rw [List.getElem?_cons_succ]; exact hr), show a + 8 * (j + 1) = a + 8 + 8 * j by omega_arith]
    rw [List.length_cons, regsVal, wordsVal, h0, hr]

theorem mLoads_fst {n m : Nat} {p : Reg × BitVec 64} (hp : p ∈ mLoads n m) : p.1 ∈ mPool n :=
  (List.of_mem_zip hp).1

theorem mRegs_sub {n m : Nat} (hM : ModOkS n m) : ∀ r ∈ mRegs n m, r ∈ mPool n := by
  intro r hr
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  exact mLoads_fst (hM.loads j (List.mem_range.mp hj))

theorem mRegs_length (n m : Nat) : (mRegs n m).length = n := by simp [mRegs]

/-- P-384's `p` from `x7 = 0`, in the registers `mLoads` names. -/
theorem sparseLoad_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block sparseLoadCode) s fun t =>
      t.gpr .x23 = 0x00000000ffffffff ∧ t.gpr .x24 = 0xffffffff00000000 ∧
      t.gpr .x25 = 0xfffffffffffffffe ∧ t.gpr .x26 = 0xffffffffffffffff ∧
      Keeps [.x23, .x24, .x25, .x26] s t := by
  apply WP.of_runBlock
  simp only [sparseLoadCode, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    show (1 : Nat) < 4096 from by decide, show 32 < Size.x.bits from by decide, ite_true,
    RegUpd.gpr_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left', hz, reduceCtorEq, ite_false]
  refine ⟨by decide, by decide, by decide, by decide, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- The modulus's words into their registers, `x7` being zero. -/
theorem mLoad_ok {n m : Nat} (hM : ModOkS n m) (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block (mLoadCode n m)) s fun s' => regsVal s' (mRegs n m) = m ∧ Keeps (mPool n) s s' := by
  rw [mLoadCode]
  by_cases hs : sparseOk n m = true
  · simp only [hs, ite_true]
    obtain hn : n = 6 := by simp only [sparseOk, Bool.and_eq_true, beq_iff_eq] at hs; exact hs.1
    obtain hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 := by
      simp only [sparseOk, Bool.and_eq_true, beq_iff_eq] at hs; exact hs.2
    subst hn hm
    refine WP.mono (sparseLoad_ok s hz) fun t ⟨h23, h24, h25, h26, k⟩ => ⟨?_, by
      rw [show mPool 6 = [.x23, .x24, .x25, .x26] by decide]; exact k⟩
    rw [show mRegs 6 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319 =
      [.x23, .x24, .x25, .x26, .x26, .x26] by decide +kernel]
    simp only [regsVal, h23, h24, h25, h26]
    decide
  simp only [Bool.not_eq_true] at hs
  simp only [hs, Bool.false_eq_true, ite_false]
  refine WP.mono (constLoads_ok (mLoads n m) hM.lnd) fun s' ⟨e, k⟩ => ⟨?_, k.mono fun r hr => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr; exact mLoads_fst hp⟩
  rw [mRegs, List.range_eq_range']
  exact regsVal_of_shifts s' (mReg n m) 0 n m hM.m_lt fun k hk => by
    rw [Nat.zero_add]; exact e _ (hM.loads k hk)

/-- The reduction's constant into `x6`. -/
theorem mulConst_ok (M : Mod) (s : State) :
    WP isa (.block (mulConst M)) s fun s' => ConstOk M s' ∧ Keeps [.x6] s s' := by
  cases hr : M.red with
  | general =>
    rw [show mulConst M = const64 .x6 M.minv by simp only [mulConst, hr]]
    refine WP.mono (const64_ok s .x6 M.minv) fun s₂ ⟨e, k⟩ => ⟨?_, k⟩
    unfold ConstOk; rw [hr]; exact e
  | friendly ws =>
    cases hg : firstGen ws with
    | none =>
      rw [show mulConst M = [] by simp only [mulConst, hr, hg]]
      refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      unfold ConstOk; rw [hr]; intro v hv; rw [hg] at hv; exact absurd hv (by simp)
    | some v =>
      rw [show mulConst M = const64 .x6 (BitVec.ofNat 64 v) by simp only [mulConst, hr, hg]]
      refine WP.mono (const64_ok s .x6 (BitVec.ofNat 64 v)) fun s₂ ⟨e, k⟩ => ⟨?_, k⟩
      unfold ConstOk; rw [hr]; intro v' hv'
      rw [hg, Option.some.injEq] at hv'
      rw [e, hv']

theorem constOk_of_nil {M : Mod} (h : mulConst M = []) (s : State) : ConstOk M s := by
  cases hr : M.red with
  | general => simp only [mulConst, hr, const64] at h; exact absurd h (by simp)
  | friendly ws =>
    cases hg : firstGen ws with
    | none => simp only [ConstOk, hr]; intro v hv; rw [hg] at hv; exact absurd hv (by simp)
    | some v => simp only [mulConst, hr, hg, const64] at h; exact absurd h (by simp)

theorem mem_bodyW_fixed {n : Nat} : ∀ r ∈ [Reg.x1, .x2, .x3, .x6, .x7, .x23], r ∈ bodyW n := by
  intro r hr; simp only [bodyW, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl hr)))

theorem mem_bodyW_b {n : Nat} {r : Reg} (h : r ∈ bRegsF n) : r ∈ bodyW n := by
  simp only [bodyW, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem mem_bodyW_m {n : Nat} {r : Reg} (h : r ∈ mPool n) : r ∈ bodyW n := by
  simp only [bodyW, List.mem_append]; exact Or.inl (Or.inl (Or.inr h))

theorem mem_bodyW_acc {n : Nat} {r : Reg} (h : r ∈ acc n) : r ∈ bodyW n := by
  simp only [bodyW, List.mem_append]; exact Or.inl (Or.inr h)

theorem mem_bodyW_d {n : Nat} {r : Reg} (h : r ∈ dRegs n) : r ∈ bodyW n := by
  simp only [bodyW, List.mem_append]; exact Or.inr h

theorem mem_bodyW_round {n : Nat} {r : Reg} (h : r ∈ Reg.x1 :: .x2 :: .x3 :: .x23 :: acc n) :
    r ∈ bodyW n := by
  simp only [List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | h
  · exact mem_bodyW_fixed _ (by simp)
  · exact mem_bodyW_fixed _ (by simp)
  · exact mem_bodyW_fixed _ (by simp)
  · exact mem_bodyW_fixed _ (by simp)
  · exact mem_bodyW_acc h

/-- The body: `[po] = [pa] [pb] R⁻¹ mod m`, changing only the registers
`bodyW` and the memory at `[po]`. -/
theorem bodyF_ok {n m : Nat} (hM : ModOkS n m) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {pa pb po : Addr} (hpa : Ptr s (raF n) pa (8 * n)) (hpb : Ptr s .x3 pb (8 * n))
    (hpo : PtrW s (roF n) po (8 * n)) (hB : wordsVal s.mem pb 0 n < m) :
    WP isa (.block (bodyCode n m)) s fun s' =>
      (∀ r, r ∉ bodyW n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Outside po 0 (8 * n) s.mem s'.mem ∧ wordsVal s'.mem po 0 n < m ∧
      wordsVal s'.mem po 0 n * 2 ^ (64 * n) % m = wordsVal s.mem pa 0 n * wordsVal s.mem pb 0 n % m := by
  obtain R := regs_ok n hM.hn
  have hn := R.n10
  obtain hacc := acc_regs_lt _ hn
  have hmX := hM.m_lt
  -- How each step's changes keep a register outside `bodyW`.
  obtain kw : ∀ {rs : List Reg} {t t' : State}, Keeps rs t t' → (∀ q ∈ rs, q ∈ bodyW n) →
      ∀ r, r ∉ bodyW n → t'.gpr r = t.gpr r := fun k h r hr => k.gpr r fun h' => hr (h _ h')
  obtain x0W : Reg.x0 ∉ bodyW n := (R.keep0 .x0 (by simp)).1
  rw [bodyCode, WP.block_append_iff]
  -- `[b]` into its registers.
  refine WP.mono (loadsEach_ok (bRegsF n) hpb (a := 0) (by rw [R.blen]; omega_arith) rfl R.bnd R.b3)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hB₁ : regsVal s₁ (bRegsF n) = wordsVal s.mem pb 0 n := by
    rw [regsVal_of_loads _ 0 e₁, R.blen]
  obtain w₁ := kw k₁ fun q hq => mem_bodyW_b hq
  -- The reduction's constant.
  rw [WP.block_append_iff]
  obtain hC : WP isa (.block (mulConst (mod n m))) s₁ fun s₃ => ConstOk (mod n m) s₃ ∧
      Keeps (if mulConst (mod n m) = [] then [] else [.x6]) s₁ s₃ := by
    by_cases hc : mulConst (mod n m) = []
    · rw [hc]
      simp only [↓reduceIte]
      exact WP.block_nil ⟨constOk_of_nil hc s₁, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · exact WP.mono (mulConst_ok _ s₁) fun s₃ ⟨c, k⟩ => ⟨c, by simp only [hc, ↓reduceIte]; exact k⟩
  refine WP.mono hC fun s₃ ⟨c₃, k₃⟩ => ?_
  obtain w₃ := kw k₃ fun q hq => by
    split at hq
    · exact absurd hq List.not_mem_nil
    · exact mem_bodyW_fixed q (by simp at hq; simp [hq])
  obtain g₃ : ∀ r, r ≠ .x6 → s₃.gpr r = s₁.gpr r := fun r hr => k₃.gpr r (by
    split
    · exact List.not_mem_nil
    · simp only [List.mem_singleton]; exact hr)
  obtain hB₃ : regsVal s₃ (bRegsF n) = wordsVal s.mem pb 0 n := by
    rw [← hB₁]
    refine regsVal_congr fun r hr => k₃.gpr r ?_
    split
    · exact List.not_mem_nil
    · rename_i hc
      simp only [List.mem_singleton]
      rintro rfl
      exact hc (hM.x6 hr)
  -- `x7` and the accumulator cleared.
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (zero7_ok s₃) fun s₄ ⟨z₄, k₄⟩ => ?_
  obtain w₄ := kw k₄ fun q hq => mem_bodyW_fixed q (by simp at hq; simp [hq])
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok s₄ (acc n)) fun s₅ ⟨z₅, k₅⟩ => ?_
  obtain w₅ := kw k₅ fun q hq => mem_bodyW_acc hq
  obtain c₅ : ConstOk (mod n m) s₅ := c₃.keep (by
    rw [k₅.gpr _ (fun h => by have := hacc _ h; simp at this), k₄.gpr _ (by decide)])
  obtain z₇ : s₅.gpr .x7 = 0 := by rw [k₅.gpr _ (fun h => by have := hacc _ h; simp at this), z₄]
  obtain hB₅ : regsVal s₅ (bRegsF n) = wordsVal s.mem pb 0 n := by
    rw [← hB₃, regsVal_congr fun r hr => k₅.gpr r (R.bsafe.acc hr),
      regsVal_congr fun r hr => k₄.gpr r (by simp only [List.mem_singleton]; rintro rfl; exact R.b7 hr)]
  obtain h0 : regsVal s₅ (wins n 0) = 0 := regsVal_zero fun r hr => z₅ r (wins_sub_acc hn 0 r hr)
  -- The pointers so far.
  obtain kp : ∀ r, r ∉ bodyW n → s₅.gpr r = s.gpr r := fun r hr => by
    rw [w₅ r hr, w₄ r hr, w₃ r hr, w₁ r hr]
  have nro : roF n ∉ bodyW n := R.nro
  obtain ra₅ : s₅.gpr (raF n) = s.gpr (raF n) := by
    have hra := R.ra
    simp only [List.mem_cons, not_or] at hra
    rw [k₅.gpr _ hra.2.2.2.2, k₄.gpr _ (by simp [R.r67.2.1]), g₃ _ R.r67.1, k₁.gpr _ R.bra]
  obtain hmem₅ : s₅.mem = s.mem := by rw [k₅.mem, k₄.mem, k₃.mem, k₁.mem]
  obtain hrd₅ : s₅.rd = s.rd := by rw [k₅.rd, k₄.rd, k₃.rd, k₁.rd]
  obtain hwr₅ : s₅.wr = s.wr := by rw [k₅.wr, k₄.wr, k₃.wr, k₁.wr]
  obtain hs₅ : Scr s₅ base size := ⟨(kp _ x0W).trans hs.x0, hwr₅ ▸ hs.wr, hs.nowrap, hs.enc⟩
  obtain hpa₅ : Ptr s₅ (raF n) pa (8 * n) :=
    ⟨ra₅.trans hpa.reg, by rw [hrd₅, hwr₅]; exact hpa.ld, hpa.enc⟩
  -- The rounds.
  rw [WP.block_append_iff]
  obtain hinv : (m * (mod n m).minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [show (mod n m).minv = BitVec.ofNat 64 (minv m) from rfl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (minv_lt m)]; exact hM.inv
  obtain hsp : sparseOk n m = true → (mod n m).n = 6 ∧ m = p384 ∧ (mod n m).red = .general := fun h => by
    obtain ⟨h6, hp⟩ := sparseOk_eq h
    rcases hM.kind with ⟨_, hg⟩ | ⟨hf, _⟩
    · exact ⟨h6, hp, hg⟩
    · rw [h] at hf; exact absurd hf (by decide)
  obtain hfr : sparseOk n m = false → ∃ ws, (mod n m).red = .friendly ws := fun h => by
    rcases hM.kind with ⟨ht, _⟩ | ⟨_, hw⟩
    · rw [h] at ht; exact absurd ht (by decide)
    · exact hw
  obtain hR := roundsG_ok (M := mod n m) (size := size) (sp := sparseOk n m) hn R.ra R.bsafe R.blen hsp hfr
    (pa := pa) (sa := 8 * n) (Nat.le_refl _) hmX hinv hM.red n (Nat.le_refl _) hs₅ hpa₅ z₇ c₅
    (by rw [hB₅]; exact hB) h0
  rw [show (List.range n).flatMap (roundF n m) =
      (List.range n).flatMap (roundG (mod n m) (raF n) (bRegsF n) (sparseOk n m)) from rfl]
  refine WP.mono hR fun s₆ ⟨⟨U, eU⟩, hT, k₆⟩ => ?_
  replace hT : regsVal s₆ (wins n n) < 2 * m := hT
  replace eU : 2 ^ (64 * n) * regsVal s₆ (wins n n) =
      wordsVal s₅.mem pa 0 n * regsVal s₅ (bRegsF n) + U * m := eU
  obtain w₆ := kw k₆ fun q hq => mem_bodyW_round hq
  rw [hmem₅, hB₅] at eU
  -- The modulus into its registers.
  rw [WP.block_append_iff]
  obtain hz₆ : s₆.gpr .x7 = 0 := by
    rw [k₆.gpr _ (fun h => by
      simp only [List.mem_cons] at h
      rcases h with h | h | h | h | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · have := hacc _ h; simp at this), z₇]
  refine WP.mono (mLoad_ok hM s₆ hz₆) fun s₇ ⟨e₇, k₇⟩ => ?_
  obtain g₇ : ∀ r, r ∉ mPool n → s₇.gpr r = s₆.gpr r := fun r hr => k₇.gpr r hr
  obtain hz₇ : s₇.gpr .x7 = 0 := by
    rw [g₇ _ (fun h => (R.m2 _ h).2.1 rfl), hz₆]
  -- The result reduced.
  obtain hsplit := wins_split n n
  obtain hlowlen : (lowF n).length = n := by simp [lowF]
  obtain hlow_acc : ∀ r ∈ lowF n, r ∈ acc n := fun r hr =>
    wins_sub_acc hn n r (by rw [hsplit]; exact List.mem_append_left _ hr)
  obtain hT₇ : ∀ r ∈ wins n n, s₇.gpr r = s₆.gpr r := fun r hr =>
    g₇ r fun h => R.macc _ h (wins_sub_acc hn n r hr)
  obtain hV : regsVal s₇ (lowF n) + 2 ^ (64 * n) * (s₇.gpr (win n n n)).toNat = regsVal s₆ (wins n n) := by
    obtain hw' := regsVal_congr (rs := wins n n) hT₇
    rw [← hw', hsplit, regsVal_append, show ((List.range n).map (win n n)).length = n by simp]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hT' := hT
    rw [← hw', hsplit, regsVal_append, show ((List.range n).map (win n n)).length = n by simp] at hT'
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hT'
    have : (s₇.gpr (win n n (n + 1))).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * n) * 2 ^ 64 ≤ 2 ^ (64 * n) * ((s₇.gpr (win n n n)).toNat +
          2 ^ 64 * (s₇.gpr (win n n (n + 1))).toNat) :=
        Nat.mul_le_mul_left _ (by omega_arith)
      have : m < 2 ^ (64 * n) := hmX
      have : 2 ^ (64 * n) * 2 ^ 64 ≥ 2 * 2 ^ (64 * n) := by
        rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (by decide)
      omega_arith
    rw [this, Nat.mul_zero, Nat.add_zero]
    rfl
  rw [WP.block_append_iff]
  refine WP.mono (csubM_ok hlowlen (mRegs_length n m) (by rcases hM.hn with rfl | rfl <;> decide) hn
    (fresh_low n hn) (fun r hr => R.md r (mRegs_sub hM r hr)) hz₇ e₇ hmX (by rw [hV]; exact hT))
    fun s₈ ⟨e₈, k₈⟩ => ?_
  obtain w₈ := kw k₈ fun q hq => by
    simp only [List.mem_cons, List.mem_append] at hq
    rcases hq with (rfl | h) | h
    · exact mem_bodyW_fixed _ (by simp)
    · exact mem_bodyW_acc (hlow_acc _ h)
    · exact mem_bodyW_d h
  -- The store.
  obtain kr : ∀ r, r ∉ bodyW n → s₈.gpr r = s.gpr r :=
    fun r hr => by rw [w₈ r hr, g₇ r (fun h => hr (mem_bodyW_m h)), w₆ r hr, kp r hr]
  obtain hmem₈ : s₈.mem = s.mem := by rw [k₈.mem, k₇.mem, k₆.mem, hmem₅]
  obtain hpo₈ : PtrW s₈ (roF n) po (8 * n) :=
    ⟨(kr _ nro).trans hpo.reg, by rw [k₈.wr, k₇.wr, k₆.wr, hwr₅]; exact hpo.st,
      hpo.enc, hpo.nowrap⟩
  refine WP.mono (storesR_ok _ hpo₈ (o := 0) (by rw [hlowlen]; omega_arith) rfl (fresh_low' n hn).1)
    fun s₉ ⟨e₉, k₉, O₉⟩ => ?_
  rw [hlowlen] at e₉ O₉
  refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₉.gpr r (by simp), kr r hr]
  · rw [k₉.rd, k₈.rd, k₇.rd, k₆.rd, hrd₅]
  · rw [k₉.wr, k₈.wr, k₇.wr, k₆.wr, hwr₅]
  · rw [k₉.sp, k₈.sp, k₇.sp, k₆.sp, k₅.sp, k₄.sp, k₃.sp, k₁.sp]
  · intro x hx; rw [O₉ x hx, hmem₈]
  · rw [e₉, e₈, hV]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₉, e₈, hV, Nat.mod_mul_mod, Nat.mul_comm, eU]
    simp only [Nat.add_mul_mod_self_right]

/-! ## The function -/

theorem moAt_facts {n : Nat} (h : n ≤ 9) (h4 : 4 ≤ n) :
    own n ≤ moAt n ∧ moAt n + 16 * n = 4096 ∧ moAt n % 8 = 0 := by
  simp only [own, moAt, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]; omega_arith

theorem mulFnS_wp (n m : Nat) {s : State} {Q : State → Prop} : WP isa (mulFnS n m) s Q ↔
    WP isa (.block (zextCode ++ (saveCode n ++ (ptrsCode n ++ (bodyCode n m ++ restoreCode n))))) s Q := by
  rw [mulFnS, WP.seq_iff, ← WP.block_append_iff]
  simp only [entryRest, exitCode, bodyCode, ptrsCode, List.append_assoc, List.cons_append, List.nil_append]

/-- The function around a body that computes `[po] = F [pa] [pb] R⁻¹ mod m`
from operands with `pre [pa] [pb]` (the product or the square), changing only
the registers `bodyW n` and the memory at `[po]`: the entry (`zext_ok`,
`saves_ok`, `ptrsF_ok`), the body, the restores. -/
theorem mulFnOf_ok {n m W : Nat} (hn : n = 6 ∨ n = 9) {body : List Instr} (pre : Nat → Nat → Prop)
    (F : Nat → Nat → Nat) (hnv : ∀ i ∈ body, vdstOf i = none)
    (hbody : ∀ {s : State} {base : Addr} {size : Nat}, Scr s base size → ∀ {pa pb po : Addr},
      Ptr s (raF n) pa (8 * n) → Ptr s .x3 pb (8 * n) → PtrW s (roF n) po (8 * n) →
      pre (wordsVal s.mem pa 0 n) (wordsVal s.mem pb 0 n) →
      WP isa (.block body) s fun s' =>
        (∀ r, r ∉ bodyW n → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        Outside po 0 (8 * n) s.mem s'.mem ∧ wordsVal s'.mem po 0 n < m ∧
        wordsVal s'.mem po 0 n * 2 ^ (64 * n) % m = F (wordsVal s.mem pa 0 n) (wordsVal s.mem pb 0 n) % m)
    {s : State} (hp : Pre n W s)
    (hb : pre (wordsVal s.mem (s.gpr .x0) (arg s .x2) n) (wordsVal s.mem (s.gpr .x0) (arg s .x3) n)) :
    WP isa (.block (zextCode ++ (saveCode n ++ (ptrsCode n ++ (body ++ restoreCode n))))) s fun s' =>
      abiPreserved s s' ∧ Kept n (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) n < m ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) n * 2 ^ (64 * n) % m =
        F (wordsVal s.mem (s.gpr .x0) (arg s .x2) n) (wordsVal s.mem (s.gpr .x0) (arg s .x3) n) % m) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d := by
  obtain R := regs_ok n hn
  obtain hn9 : n ≤ 9 := by rcases hn with rfl | rfl <;> decide
  obtain hown := own_eq hn9
  have hfit := hp.fit
  have hw := hp.w
  have hw8 := hp.w8
  have ho := hp.o
  have ha := hp.a
  have hb' := hp.b
  obtain k0 := R.keep0 .x0 (by simp)
  obtain hn4 : 4 ≤ n := by rcases hn with rfl | rfl <;> decide
  obtain ⟨hmo1, hmo2, hmo8⟩ := moAt_facts hn9 hn4
  rw [WP.block_append_iff]
  refine WP.mono (zext_ok s) fun s₁ ⟨g1, g2, g3, K₁, V₁⟩ => ?_
  rw [WP.block_append_iff, saveCode_eq]
  refine WP.mono (saves_ok (saved n) 0 (s := s₁) (by have := R.slen; omega_arith)) fun s₂ ⟨K₂, L₂, _, V₂⟩ => ?_
  rw [WP.block_append_iff, ptrsCode]
  obtain ⟨r3a, r3o, rao, ra0, ro0, ra1, ra2, ro1, ro2⟩ := R.ra3
  refine WP.mono (ptrsF_ok s₂ (ra := raF n) (ro := roF n) (by simp [ra0, ra1, ra2, r3a]) (by simp [ro0, ro1, ro2, r3o])
    rao) fun s₃ ⟨go, ga, gb, K₃, V₃⟩ => ?_
  obtain x0₂ : s₂.gpr .x0 = s.gpr .x0 := by rw [K₂.gpr, K₁.gpr _ (by decide)]
  obtain x0₃ : s₃.gpr .x0 = s.gpr .x0 := by
    rw [K₃.gpr _ (by simp [Ne.symm ra0, Ne.symm ro0]), x0₂]
  obtain hs₃ : Scr s₃ (s.gpr .x0) W := ⟨x0₃, by rw [K₃.wr, K₂.wr, K₁.wr, hp.wr]; simp, hfit, by omega_arith⟩
  obtain off0 : ∀ x : Reg, s₂.gpr x = s₁.gpr x := fun x => by rw [K₂.gpr]
  obtain hP : ∀ (d e : Nat), d + 8 ≤ 8 * n → e + 8 * n ≤ own n →
      InRegions (s₃.rd ++ s₃.wr) (off (s.gpr .x0) e + BitVec.ofNat 64 d) 8 := by
    intro d e hd he
    show InRegions _ (off (off (s.gpr .x0) e) d) 8
    rw [off_off]
    have := hs₃.ld (d := e + d) (by have := hd; have := he; omega_arith)
    rwa [hs₃.x0] at this
  obtain hpa : Ptr s₃ (raF n) (off (s.gpr .x0) (arg s .x2)) (8 * n) :=
    ⟨by rw [ga, x0₂, off0, g2], fun d hd => hP d _ hd ha, by omega_arith⟩
  obtain hpb : Ptr s₃ .x3 (off (s.gpr .x0) (arg s .x3)) (8 * n) :=
    ⟨by rw [gb, x0₂, off0, g3], fun d hd => hP d _ hd hb', by omega_arith⟩
  obtain hpo : PtrW s₃ (roF n) (off (s.gpr .x0) (arg s .x1)) (8 * n) := by
    refine ⟨by rw [go, x0₂, off0, g1], fun d hd => ?_, by omega_arith, ?_⟩
    · show InRegions _ (off (off (s.gpr .x0) (arg s .x1)) d) 8
      rw [off_off]
      have := hs₃.st (d := arg s .x1 + d) (by omega_arith)
      rwa [hs₃.x0] at this
    · have := hp.fit; simp only [off, Nat.add_comm]
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := arg s .x1) (by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  obtain hmem₃ : s₃.mem = s.mem := by rw [K₃.mem, K₂.mem, K₁.mem]
  obtain hB : pre (wordsVal s₃.mem (off (s.gpr .x0) (arg s .x2)) 0 n)
      (wordsVal s₃.mem (off (s.gpr .x0) (arg s .x3)) 0 n) := by
    rw [wordsVal_off, wordsVal_off, Nat.add_zero, Nat.add_zero, hmem₃]; exact hb
  rw [WP.block_append_iff]
  refine WP.mono (WP.block_novec hnv (hbody hs₃ hpa hpb hpo hB)) fun s₄ ⟨⟨G₄, rd₄, wr₄, sp₄, O₄, V, C⟩, Vv⟩ => ?_
  rw [restoreCode_eq]
  refine WP.mono (restores_ok (saved n) 0 (by have := R.slen; omega_arith) R.snd) fun s₅ ⟨K₅, V₅, R₅⟩ => ?_
  have mem₅ : s₅.mem = s₄.mem := K₅.mem
  -- The registers kept by everything but the saves and restores.
  obtain keep : ∀ r, r ∉ saved n → r ∉ bodyW n → r ∉ [Reg.x1, .x2, .x3] → r ≠ roF n → r ≠ raF n →
      s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 => by
    rw [K₅.gpr r h1, G₄ r h2, K₃.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h5, fun e => h3 (by simp [e]), h4⟩), off0, K₁.gpr r h3]
  obtain ev : ∀ d, wordsVal s₃.mem (off (s.gpr .x0) d) 0 n = wordsVal s.mem (s.gpr .x0) d n := fun d => by
    rw [wordsVal_off, Nat.add_zero, hmem₃]
  refine ⟨⟨fun r hr => ?_, by rw [K₅.sp, sp₄, K₃.sp, K₂.sp, K₁.sp], fun d hd => ?_⟩, fun x hx _ => ?_, ⟨?_, ?_⟩,
    keep .x0 k0.2.1 k0.1 (by decide) (Ne.symm ro0) (Ne.symm ra0), by rw [K₅.rd, rd₄, K₃.rd, K₂.rd, K₁.rd],
    by rw [K₅.wr, wr₄, K₃.wr, K₂.wr, K₁.wr], fun d hd => by rw [V₅, Vv, V₃, V₂ d hd, V₁]⟩
  · by_cases hs : r ∈ saved n
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hs
      obtain l := L₂ i hi
      rw [Nat.zero_add] at l
      rw [R₅ i hi, Nat.zero_add, Vv, V₃, l, K₁.gpr]
      obtain hp' := R.spres _ (List.getElem_mem hi)
      intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> rw [h] at hp' <;> exact absurd hp' (by decide)
    · obtain ⟨c1, c2, c3⟩ := R.pres r hr hs
      exact keep r hs c1 (by
        intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> exact absurd hr (by decide)) c2 c3
  · have hd' : ∀ i < 10, d ≠ (slot i).1 := by
      have : ∀ d ∈ preservedV, ∀ i < 10, d ≠ (slot i).1 := by decide
      exact this d hd
    rw [V₅, Vv, V₃, V₂ d hd', V₁]
  · rw [mem₅]
    have := Outside.of_off O₄ (by have := (s.gpr .x0).isLt; omega_arith)
    rw [this x hx, hmem₃]
  · have e := wordsVal_off s₄.mem (s.gpr .x0) (arg s .x1) 0 n
    rw [Nat.add_zero] at e
    rw [mem₅, ← e]; exact V
  · have e := wordsVal_off s₄.mem (s.gpr .x0) (arg s .x1) 0 n
    rw [Nat.add_zero] at e
    rw [mem₅, ← e, C, ev, ev]

/-- `vg_<curve>_mul_mod_<p|n>`: `[o] = [a] [b] R⁻¹ mod m`. -/
theorem mulFnS_ok {n m W : Nat} (hM : ModOkS n m) {s : State} (hp : Pre n W s)
    (hb : wordsVal s.mem (s.gpr .x0) (arg s .x3) n < m) :
    WP isa (mulFnS n m) s fun s' => abiPreserved s s' ∧ Kept n (s.gpr .x0) (arg s .x1) s.mem s'.mem ∧
      (wordsVal s'.mem (s.gpr .x0) (arg s .x1) n < m ∧
      wordsVal s'.mem (s.gpr .x0) (arg s .x1) n * 2 ^ (64 * n) % m =
        wordsVal s.mem (s.gpr .x0) (arg s .x2) n * wordsVal s.mem (s.gpr .x0) (arg s .x3) n % m) ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      ∀ d, (∀ i < 10, d ≠ (slot i).1) → s'.v d = s.v d := by
  rw [mulFnS_wp]
  exact mulFnOf_ok hM.hn (fun _ B => B < m) (· * ·) (fun i hi => hM.novec i (List.mem_append_right _ hi))
    (fun hs _ _ _ hpa hpb hpo hB => bodyF_ok hM hs hpa hpb hpo hB) hp hb

end VG.Proof.Weierstrass.AArch64.Mont
