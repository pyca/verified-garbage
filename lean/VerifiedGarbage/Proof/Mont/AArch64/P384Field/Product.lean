module

public import VerifiedGarbage.Proof.Mont.AArch64.P384Field.Chains
import VerifiedGarbage.Proof.Mont.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# P-384's field arithmetic on AArch64: the product and the square

`prod_ok`: `prod` leaves in `tl` and `th` the twelve words of the product of
the numbers its pointers name. `sqr_ok`: `sqr` leaves there those of a number's
square.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Mont.AArch64.P384Field

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64.P384Field
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- The registers a product or a square writes. -/
abbrev prodW : List Reg := [.x1, .x2] ++ bs ++ tl ++ th

/-- The rows' sums fit. -/
theorem row_fit {V x B n : Nat} (hV : V < 2 ^ (64 * n)) (hx : x < 2 ^ 64) (hB : B < 2 ^ (64 * n)) :
    V + x * B < 2 ^ (64 * (n + 1)) := by
  rw [pow64_succ]
  have : x * B ≤ (2 ^ 64 - 1) * B := Nat.mul_le_mul_right _ (by omega_using [hx])
  omega_using [this, hV, hB]

/-- A row of the product: `ls` the words of `T` below it. -/
theorem mulRow_ok {s : State} {ra : Reg} {pa : Addr} {sa d : Nat} (hp : Ptr s ra pa sa) (hd : d + 8 ≤ sa)
    (h8 : d % 8 = 0) (hz : s.gpr .x7 = 0) {q l : Reg} {qs : List Reg} (ls : List Reg)
    (h : RowOk .x1 q qs l [.x8, .x9, .x10, .x16, .x24] .x25)
    (hl : ∀ r ∈ ls, r ∉ Reg.x1 :: .x2 :: l :: q :: qs) (hb : ∀ r ∈ bs, r ≠ .x1) (hq : .x1 ∉ q :: qs) :
    WP isa (.block (mulRow ra d q qs l)) s fun t =>
      regsVal t (ls ++ (q :: qs ++ [l])) = regsVal s (ls ++ q :: qs) +
        2 ^ (64 * ls.length) * ((word s.mem pa d).toNat * regsVal s bs) ∧
      Keeps (.x1 :: .x2 :: l :: q :: qs) s t := by
  rw [mulRow, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ldR_ok hp hd h8 .x1) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have hlen : qs.length = 5 := by simpa using h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm
  have eb : regsVal s₁ bs = regsVal s bs := regsVal_keep k₁ fun r hr e => hb r hr (List.mem_singleton.mp e)
  have eq : regsVal s₁ (q :: qs) = regsVal s (q :: qs) :=
    regsVal_keep k₁ fun r hr e => hq (List.mem_singleton.mp e ▸ hr)
  refine WP.mono (row_ok h (by rw [k₁.gpr _ (by decide), hz]) ?_) fun t ⟨e₂, k₂⟩ => ?_
  · have := row_fit (n := 6) (by simpa [hlen] using regsVal_lt s₁ (q :: qs)) (s₁.gpr .x1).isLt
      (regsVal_lt s₁ bs)
    rw [hlen]; exact this
  · have k := (k₁.mono (rs' := .x1 :: .x2 :: l :: q :: qs) (by simp)).trans (k₂.mono (by simp +contextual))
    refine ⟨?_, k⟩
    have e₃ : regsVal s₁ ([.x8, .x9, .x10, .x16, .x24] ++ [.x25]) = regsVal s bs := eb
    rw [e₃, e₁, eq] at e₂
    rw [regsVal_append, e₂, regsVal_append s, regsVal_keep k hl, Nat.mul_add]
    omega_using []

/-- `T = [ra + a] [rb + b]`. -/
theorem prod_ok {s : State} {ra rb : Reg} {pa pb : Addr} {sa sb a b : Nat} (hpa : Ptr s ra pa sa)
    (hpb : Ptr s rb pb sb) (ha : a + 48 ≤ sa) (hb : b + 48 ≤ sb) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hra : ra ∉ prodW) (hrb : rb ∉ bs) (hz : s.gpr .x7 = 0) :
    WP isa (.block (prod ra rb a b)) s fun t =>
      regsVal t (tl ++ th) = wordsVal s.mem pa a 6 * wordsVal s.mem pb b 6 ∧ Keeps prodW s t := by
  simp only [prod, List.append_assoc, List.cons_append]
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok bs hpb (by simpa using hb) hb8 (by decide) hrb) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have K₁ : Keeps prodW s s₁ := k₁.mono (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ldR_ok (hpa.of_keeps K₁ hra) (d := a) (by omega_using [ha]) ha8 .x1) fun s₂ ⟨e₂, k₂, _⟩ => ?_
  have K₂ : Keeps prodW s s₂ := K₁.trans (k₂.mono (by decide))
  rw [WP.block_append_iff]
  have z : ∀ {u}, Keeps prodW s u → u.gpr .x7 = 0 := fun k => by rw [k.gpr _ (by decide), hz]
  refine WP.mono (row0_ok (by decide) (z K₂)) fun s₃ ⟨e₃, k₃⟩ => ?_
  have K₃ : Keeps prodW s s₃ := K₂.trans (k₃.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (mulRow_ok (hpa.of_keeps K₃ hra) (d := a + 8) (by omega_using [ha]) (by omega_using [ha8]) (z K₃)
    [.x17] (by decide) (by decide) (by decide) (by decide)) fun s₄ ⟨e₄, k₄⟩ => ?_
  have K₄ : Keeps prodW s s₄ := K₃.trans (k₄.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (mulRow_ok (hpa.of_keeps K₄ hra) (d := a + 16) (by omega_using [ha]) (by omega_using [ha8]) (z K₄)
    [.x17, .x22] (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨e₅, k₅⟩ => ?_
  have K₅ : Keeps prodW s s₅ := K₄.trans (k₅.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (mulRow_ok (hpa.of_keeps K₅ hra) (d := a + 24) (by omega_using [ha]) (by omega_using [ha8]) (z K₅)
    [.x17, .x22, .x23] (by decide) (by decide) (by decide) (by decide)) fun s₆ ⟨e₆, k₆⟩ => ?_
  have K₆ : Keeps prodW s s₆ := K₅.trans (k₆.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (mulRow_ok (hpa.of_keeps K₆ hra) (d := a + 32) (by omega_using [ha]) (by omega_using [ha8]) (z K₆)
    [.x17, .x22, .x23, .x11] (by decide) (by decide) (by decide) (by decide)) fun s₇ ⟨e₇, k₇⟩ => ?_
  have K₇ : Keeps prodW s s₇ := K₆.trans (k₇.mono (by decide))
  refine WP.mono (mulRow_ok (hpa.of_keeps K₇ hra) (d := a + 40) (by omega_using [ha]) (by omega_using [ha8]) (z K₇)
    [.x17, .x22, .x23, .x11, .x12] (by decide) (by decide) (by decide) (by decide)) fun t ⟨e₈, k₈⟩ => ?_
  refine ⟨?_, K₇.trans (k₈.mono (by decide))⟩
  have B₂ : regsVal s₂ bs = wordsVal s.mem pb b 6 := by
    rw [regsVal_keep k₂ (by decide)]; exact e₁
  have B₃ : regsVal s₃ bs = wordsVal s.mem pb b 6 := (regsVal_keep k₃ (by decide)).trans B₂
  have B₄ : regsVal s₄ bs = wordsVal s.mem pb b 6 := (regsVal_keep k₄ (by decide)).trans B₃
  have B₅ : regsVal s₅ bs = wordsVal s.mem pb b 6 := (regsVal_keep k₅ (by decide)).trans B₄
  have B₆ : regsVal s₆ bs = wordsVal s.mem pb b 6 := (regsVal_keep k₆ (by decide)).trans B₅
  have B₇ : regsVal s₇ bs = wordsVal s.mem pb b 6 := (regsVal_keep k₇ (by decide)).trans B₆
  rw [B₇, K₇.mem] at e₈
  rw [B₆, K₆.mem] at e₇
  rw [B₅, K₅.mem] at e₆
  rw [B₄, K₄.mem] at e₅
  rw [B₃, K₃.mem] at e₄
  rw [e₂, K₁.mem, show regsVal s₂ ([.x8, .x9, .x10, .x16, .x24] ++ [.x25]) = wordsVal s.mem pb b 6 from B₂] at e₃
  refine e₈.trans ?_
  rw [show ([.x17, .x22, .x23, .x11, .x12] ++ Reg.x13 :: [.x14, .x15, .x21, .x4, .x5] : List Reg) =
    [.x17, .x22, .x23, .x11] ++ (.x12 :: [.x13, .x14, .x15, .x21, .x4] ++ [.x5]) from rfl, e₇,
    show ([.x17, .x22, .x23, .x11] ++ Reg.x12 :: [.x13, .x14, .x15, .x21, .x4] : List Reg) =
    [.x17, .x22, .x23] ++ (.x11 :: [.x12, .x13, .x14, .x15, .x21] ++ [.x4]) from rfl, e₆,
    show ([.x17, .x22, .x23] ++ Reg.x11 :: [.x12, .x13, .x14, .x15, .x21] : List Reg) =
    [.x17, .x22] ++ (.x23 :: [.x11, .x12, .x13, .x14, .x15] ++ [.x21]) from rfl, e₅,
    show ([.x17, .x22] ++ Reg.x23 :: [.x11, .x12, .x13, .x14, .x15] : List Reg) =
    [.x17] ++ (.x22 :: [.x23, .x11, .x12, .x13, .x14] ++ [.x15]) from rfl, e₄,
    show ([.x17] ++ Reg.x22 :: [.x23, .x11, .x12, .x13, .x14] : List Reg) =
    .x17 :: [.x22, .x23, .x11, .x12, .x13] ++ [.x14] from rfl, e₃]
  generalize wordsVal s.mem pb b 6 = B
  simp only [wordsVal, List.length_cons, List.length_nil, Nat.add_mul, Nat.mul_assoc, Nat.mul_zero, Nat.zero_add,
    Nat.add_zero, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]
  omega_using []

/-! ## The square -/

/-- A row of the products of different words, `ls` the words below it. -/
theorem crossRow_ok {s : State} (hz : s.gpr .x7 = 0) {x q l b : Reg} {qs cs : List Reg} (ls : List Reg)
    (h : RowOk x q qs l cs b) (hl : ∀ r ∈ ls, r ∉ Reg.x2 :: l :: q :: qs) :
    WP isa (.block (rowAdd x q qs l cs b)) s fun t =>
      regsVal t (ls ++ (q :: qs ++ [l])) = regsVal s (ls ++ q :: qs) +
        2 ^ (64 * ls.length) * ((s.gpr x).toNat * regsVal s (cs ++ [b])) ∧
      Keeps (.x2 :: l :: q :: qs) s t := by
  have hlen : cs.length = qs.length := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine WP.mono (row_ok h hz ?_) fun t ⟨e, k⟩ => ⟨?_, k⟩
  · exact row_fit (n := qs.length + 1) (regsVal_lt s (q :: qs)) (s.gpr x).isLt
      (by have := regsVal_lt s (cs ++ [b]); rwa [List.length_append, hlen] at this)
  · rw [regsVal_append, e, regsVal_append s ls, regsVal_keep k hl, Nat.mul_add]
    omega_using []

/-- The squares of the words of `xs`, two words to each. -/
def sqsVal (s : State) : List Reg → Nat
  | [] => 0
  | x :: xs => (s.gpr x).toNat * (s.gpr x).toNat + 2 ^ 128 * sqsVal s xs

theorem sqsVal_keep {W : List Reg} {s t : State} (k : Keeps W s t) : ∀ {xs : List Reg},
    (∀ r ∈ xs, r ∉ W) → sqsVal t xs = sqsVal s xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [sqsVal, k.gpr x (h x (List.mem_cons_self ..)),
      sqsVal_keep k fun r hr => h r (List.mem_cons_of_mem _ hr)]

/-- The registers of `diag`. -/
def DiagOk : List Reg → List Reg → Prop
  | d :: e :: ds, x :: xs => d ∉ e :: ds ∧ e ∉ ds ∧ d ∉ x :: xs ∧ e ∉ x :: xs ∧ d ≠ .x2 ∧ e ≠ .x2 ∧
    .x2 ∉ x :: xs ∧ .x2 ∉ ds ∧ DiagOk ds xs
  | [], [] => True
  | _, _ => False

instance : ∀ ds xs, Decidable (DiagOk ds xs)
  | d :: e :: ds, x :: xs => by
    have := instDecidableDiagOk ds xs
    unfold DiagOk; infer_instance
  | [], [] => .isTrue trivial
  | [], _ :: _ => .isFalse (by simp [DiagOk])
  | [_], [] => .isFalse (by simp [DiagOk])
  | [_], _ :: _ => .isFalse (by simp [DiagOk])
  | _ :: _ :: _, [] => .isFalse (by simp [DiagOk])

theorem diag_ok : ∀ (ds xs : List Reg) {s : State}, DiagOk ds xs →
    WP isa (.block (diag ds xs)) s fun t =>
      regsVal t ds + 2 ^ (64 * ds.length) * t.c.toNat = regsVal s ds + sqsVal s xs + s.c.toNat ∧
      Keeps (.x2 :: ds) s t
  | [], [], s, _ => WP.block_nil ⟨by simp [regsVal, sqsVal], (Keeps.refl s).mono (by simp)⟩
  | [], _ :: _, _, h => absurd h (by simp [DiagOk])
  | [_], [], _, h => absurd h (by simp [DiagOk])
  | [_], _ :: _, _, h => absurd h (by simp [DiagOk])
  | _ :: _ :: _, [], _, h => absurd h (by simp [DiagOk])
  | d :: e :: ds, x :: xs, s, h => by
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := h
    simp only [List.mem_cons, not_or] at o1 o3 o4 o7
    simp only [diag, List.cons_append, List.nil_append]
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (mulh_ok s false .x2 x x) fun s₁ ⟨e₁, k₁, c₁⟩ => ?_
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (addc_ok s₁ d d .x2 false rfl) fun s₂ ⟨e₂, c₂, k₂⟩ => ?_
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (mulh_ok s₂ true .x2 x x) fun s₃ ⟨e₃, k₃, c₃⟩ => ?_
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (addc_ok s₃ e e .x2 false rfl) fun s₄ ⟨e₄, c₄, k₄⟩ => ?_
    refine WP.mono (diag_ok ds xs o9) fun t ⟨e₅, k₅⟩ => ?_
    have K₂ : Keeps [.x2, d] s s₂ := (k₁.mono (by simp)).trans (k₂.mono (by simp))
    have K₄ : Keeps [.x2, d, e] s s₄ :=
      (K₂.mono (by simp)).trans ((k₃.mono (by simp)).trans (k₄.mono (by simp)))
    have v₂ := Word64.addCarry_value (s₁.gpr d) (s₁.gpr .x2) s₁.c
    have v₄ := Word64.addCarry_value (s₃.gpr e) (s₃.gpr .x2) s₃.c
    simp only [Bool.false_eq_true, ite_false, ite_true] at e₁ e₂ c₂ e₃ e₄ c₄
    rw [← e₂, ← c₂, e₁, c₁, k₁.gpr d (by simpa using o5)] at v₂
    rw [← e₄, ← c₄, e₃, c₃, k₃.gpr e (by simpa using o6), K₂.gpr e (by simp [o6, Ne.symm o1.1]),
      K₂.gpr x (by simp [Ne.symm o7.1, Ne.symm o3.1])] at v₄
    rw [regsVal_keep K₄ (by
        intro r hr h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact o8 hr
        · exact o1.2 hr
        · exact o2 hr),
      sqsVal_keep K₄ (by
        intro r hr h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl
        · exact o7.2 hr
        · exact o3.2 hr
        · exact o4.2 hr)] at e₅
    refine ⟨?_, (K₄.mono (by simp)).trans (k₅.mono (by simp +contextual))⟩
    have hd : t.gpr d = s₂.gpr d := by
      rw [k₅.gpr d (by simp [o5, o1.2]), k₄.gpr d (by simpa using o1.1), k₃.gpr d (by simpa using o5)]
    have he : t.gpr e = s₄.gpr e := k₅.gpr e (by simp [o6, o2])
    have hx := Nat.mod_add_div ((s.gpr x).toNat * (s.gpr x).toNat) (2 ^ 64)
    simp only [regsVal, sqsVal, List.length_cons, pow64_succ, hd, he, Nat.mul_assoc]
    generalize (s.gpr x).toNat * (s.gpr x).toNat = X at *
    omega_using [e₅, v₂, v₄, hx]

/-- The products of different words of six, and their squares, are the square. -/
theorem sq_arith {a0 a1 a2 a3 a4 a5 A X S : Nat}
    (hA : A = a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * (a3 + 2 ^ 64 * (a4 + 2 ^ 64 * a5)))))
    (hX : X = a0 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * (a3 + 2 ^ 64 * (a4 + 2 ^ 64 * a5)))) +
      2 ^ 128 * (a1 * (a2 + 2 ^ 64 * (a3 + 2 ^ 64 * (a4 + 2 ^ 64 * a5)))) +
      2 ^ 256 * (a2 * (a3 + 2 ^ 64 * (a4 + 2 ^ 64 * a5))) +
      2 ^ 384 * (a3 * (a4 + 2 ^ 64 * a5)) + 2 ^ 512 * (a4 * a5))
    (hS : S = a0 * a0 + 2 ^ 128 * (a1 * a1 + 2 ^ 128 * (a2 * a2 + 2 ^ 128 * (a3 * a3 + 2 ^ 128 * (a4 * a4 +
      2 ^ 128 * (a5 * a5)))))) : S + 2 ^ 64 * (2 * X) = A * A := by
  subst hA hX hS
  grind

/-- The words 1 to 10 of `T`. -/
abbrev crossRegs : List Reg := [.x22, .x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4, .x5]

theorem cross_arith {L V x y z w c : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (e : z + 2 ^ 64 * c = w + x * y % 2 ^ 64)
    (h : L + 2 ^ 512 * w = V) (hc : c ≤ 1) :
    L + 2 ^ 512 * (z + 2 ^ 64 * ((x * y / 2 ^ 64 + 0 + c) % 2 ^ 64)) = V + 2 ^ 512 * (x * y) := by
  have : x * y ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_using [hx]) (by omega_using [hy])
  generalize x * y = P at *
  omega_using [this, e, h, hc]

/-- The products of different words. -/
theorem cross_ok {s : State} (hz : s.gpr .x7 = 0) :
    WP isa (.block cross) s fun t =>
      regsVal t crossRegs = (s.gpr .x8).toNat * regsVal s [.x9, .x10, .x16, .x24, .x25] +
        2 ^ 128 * ((s.gpr .x9).toNat * regsVal s [.x10, .x16, .x24, .x25]) +
        2 ^ 256 * ((s.gpr .x10).toNat * regsVal s [.x16, .x24, .x25]) +
        2 ^ 384 * ((s.gpr .x16).toNat * regsVal s [.x24, .x25]) +
        2 ^ 512 * ((s.gpr .x24).toNat * (s.gpr .x25).toNat) ∧
      Keeps (.x2 :: crossRegs) s t := by
  simp only [cross, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (row0_ok (s := s) (by decide) hz) fun s₁ ⟨e₁, k₁⟩ => ?_
  have K₁ : Keeps (.x2 :: crossRegs) s s₁ := k₁.mono (by decide)
  have z : ∀ {u}, Keeps (.x2 :: crossRegs) s u → u.gpr .x7 = 0 := fun k => by rw [k.gpr _ (by decide), hz]
  rw [WP.block_append_iff]
  refine WP.mono (crossRow_ok (z K₁) [.x22, .x23] (by decide) (by decide)) fun s₂ ⟨e₂, k₂⟩ => ?_
  have K₂ : Keeps (.x2 :: crossRegs) s s₂ := K₁.trans (k₂.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (crossRow_ok (z K₂) [.x22, .x23, .x11, .x12] (by decide) (by decide)) fun s₃ ⟨e₃, k₃⟩ => ?_
  have K₃ : Keeps (.x2 :: crossRegs) s s₃ := K₂.trans (k₃.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (crossRow_ok (z K₃) [.x22, .x23, .x11, .x12, .x13, .x14] (by decide) (by decide))
    fun s₄ ⟨e₄, k₄⟩ => ?_
  have K₄ : Keeps (.x2 :: crossRegs) s s₄ := K₃.trans (k₄.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (muls_ok (x := .x24) (by decide) false true [.x4] [.x25] (.inr (by simp)) rfl (by decide))
    fun s₅ ⟨e₅, k₅⟩ => ?_
  have K₅ : Keeps (.x2 :: crossRegs) s s₅ := K₄.trans (k₅.mono (by decide))
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulh_ok s₅ true .x2 .x24 .x25) fun s₆ ⟨e₆, k₆, c₆⟩ => ?_
  have K₆ : Keeps (.x2 :: crossRegs) s s₆ := K₅.trans (k₆.mono (by decide))
  refine WP.mono (adc_ok s₆ .x5 .x2 .x7) fun t ⟨e₇, k₇, _⟩ => ?_
  refine ⟨?_, K₆.trans (k₇.mono (by decide))⟩
  rw [K₁.gpr .x9 (by decide), show regsVal s₁ ([.x10, .x16, .x24] ++ [.x25]) = regsVal s [.x10, .x16, .x24, .x25]
    from regsVal_keep K₁ (by decide)] at e₂
  rw [K₂.gpr .x10 (by decide), show regsVal s₂ ([.x16, .x24] ++ [.x25]) = regsVal s [.x16, .x24, .x25]
    from regsVal_keep K₂ (by decide)] at e₃
  rw [K₃.gpr .x16 (by decide), show regsVal s₃ ([.x24] ++ [.x25]) = regsVal s [.x24, .x25]
    from regsVal_keep K₃ (by decide)] at e₄
  simp only [part, K₄.gpr .x24 (by decide), K₄.gpr .x25 (by decide), Bool.false_eq_true, ite_false, ite_true,
    Nat.mul_zero, Nat.add_zero, Bool.toNat_false, regsVal_single, List.length_singleton, Nat.mul_one] at e₅
  simp only [ite_true, K₅.gpr .x24 (by decide), K₅.gpr .x25 (by decide)] at e₆
  rw [z K₆, c₆, e₆] at e₇
  have low : regsVal t [.x22, .x23, .x11, .x12, .x13, .x14, .x15, .x21] =
      regsVal s₄ [.x22, .x23, .x11, .x12, .x13, .x14, .x15, .x21] := by
    rw [regsVal_keep k₇ (by decide), regsVal_keep k₆ (by decide), regsVal_keep k₅ (by decide)]
  have x4 : t.gpr .x4 = s₅.gpr .x4 := by rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide)]
  rw [show ([.x22, .x23] ++ Reg.x11 :: [.x12, .x13, .x14] : List Reg) =
    .x22 :: [.x23, .x11, .x12, .x13] ++ [.x14] from rfl, e₁] at e₂
  rw [show ([.x22, .x23, .x11, .x12] ++ Reg.x13 :: [.x14, .x15] : List Reg) =
    [.x22, .x23] ++ (.x11 :: [.x12, .x13, .x14] ++ [.x15]) from rfl, e₂] at e₃
  rw [show ([.x22, .x23, .x11, .x12, .x13, .x14] ++ Reg.x15 :: [.x21] : List Reg) =
    [.x22, .x23, .x11, .x12] ++ (.x13 :: [.x14, .x15] ++ [.x21]) from rfl, e₃] at e₄
  have e₈ : regsVal s₄ ([.x22, .x23, .x11, .x12, .x13, .x14, .x15, .x21] ++ [.x4]) = _ := e₄
  rw [regsVal_append, regsVal_single] at e₈
  rw [show crossRegs = [.x22, .x23, .x11, .x12, .x13, .x14, .x15, .x21] ++ [.x4, .x5] from rfl, regsVal_append, low,
    show regsVal t [.x4, .x5] = (t.gpr .x4).toNat + 2 ^ 64 * (t.gpr .x5).toNat by simp [regsVal], x4, e₇]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, List.cons_append, List.nil_append,
    show (0 : BitVec 64).toNat = 0 from rfl] at e₈ ⊢
  generalize regsVal s₄ [.x22, .x23, .x11, .x12, .x13, .x14, .x15, .x21] = L at e₈ ⊢
  exact cross_arith (s.gpr .x24).isLt (s.gpr .x25).isLt e₅ e₈ (Bool.toNat_le _)

/-- The words of the square: those of the doubled products and the squares,
in their chain. -/
theorem sqr_end {A X S' x1 D x10 x11 l0 h0 l5 h5 y1 D' y10 c1 c8 c10 : Nat}
    (hX : x1 + 2 ^ 64 * D + 2 ^ 576 * x10 + 2 ^ 640 * x11 = 2 * X)
    (h1 : y1 + 2 ^ 64 * c1 = x1 + h0) (h2 : D' + 2 ^ 512 * c8 = D + S' + c1)
    (h3 : y10 + 2 ^ 64 * c10 = x10 + l5 + c8)
    (hA : l0 + 2 ^ 64 * h0 + 2 ^ 128 * (S' + 2 ^ 512 * (l5 + 2 ^ 64 * h5)) + 2 ^ 64 * (2 * X) = A * A)
    (hlt : A < 2 ^ 384) :
    l0 + 2 ^ 64 * y1 + 2 ^ 128 * D' + 2 ^ 640 * y10 + 2 ^ 704 * ((x11 + h5 + c10) % 2 ^ 64) = A * A := by
  have hs : l0 + 2 ^ 64 * y1 + 2 ^ 128 * D' + 2 ^ 640 * y10 + 2 ^ 704 * (x11 + h5 + c10) = A * A := by
    omega_using [hX, h1, h2, h3, hA]
  have hAA : A * A < 2 ^ 384 * 2 ^ 384 := Nat.mul_lt_mul'' hlt hlt
  rw [Nat.mod_eq_of_lt, hs]
  omega_using [hs, hAA]

/-- `T = [ra + a]²`. -/
theorem sqr_ok {s : State} {ra : Reg} {pa : Addr} {sa a : Nat} (hpa : Ptr s ra pa sa) (ha : a + 48 ≤ sa)
    (ha8 : a % 8 = 0) (hra : ra ∉ bs) (hz : s.gpr .x7 = 0) :
    WP isa (.block (sqr ra a)) s fun t =>
      regsVal t (tl ++ th) = wordsVal s.mem pa a 6 * wordsVal s.mem pa a 6 ∧ Keeps prodW s t := by
  simp only [sqr, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok bs hpa (by simpa using ha) ha8 (by decide) hra) fun s₁ ⟨e₁, k₁, _⟩ => ?_
  have z₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by decide), hz]
  rw [WP.block_append_iff]
  refine WP.mono (cross_ok z₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  have z₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by decide), z₁]
  rw [WP.block_append_iff]
  refine WP.mono (adds_ok true crossRegs crossRegs crossRegs (s := s₂) (.inr (by simp)) rfl rfl (by decide))
    fun s₃ ⟨e₃, k₃⟩ => ?_
  have z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (by decide), z₂]
  rw [WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (adc_ok s₃ .x6 .x7 .x7) fun s₄ ⟨e₄, k₄, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulh_ok s₄ false .x17 .x8 .x8) fun s₅ ⟨e₅, k₅, _⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulh_ok s₅ true .x2 .x8 .x8) fun s₆ ⟨e₆, k₆, _⟩ => ?_
  refine WP.mono (addc_ok s₆ .x22 .x22 .x2 true rfl) fun s₇ ⟨e₇, c₇, k₇⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (diag_ok _ _ (by decide)) fun s₈ ⟨e₈, k₈⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulh_ok s₈ false .x2 .x25 .x25) fun s₉ ⟨e₉, k₉, c₉⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addc_ok s₉ .x5 .x5 .x2 false rfl) fun s₁₀ ⟨e₁₀, c₁₀, k₁₀⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mulh_ok s₁₀ true .x2 .x25 .x25) fun s₁₁ ⟨e₁₁, k₁₁, c₁₁⟩ => ?_
  refine WP.mono (adc_ok s₁₁ .x6 .x6 .x2) fun t ⟨e₁₂, k₁₂, _⟩ => ?_
  have K₂ : Keeps prodW s s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have K₃ : Keeps prodW s s₃ := K₂.trans (k₃.mono (by decide))
  have K₄ : Keeps prodW s s₄ := K₃.trans (k₄.mono (by decide))
  have K₆ : Keeps prodW s s₆ := K₄.trans ((k₅.mono (by decide)).trans (k₆.mono (by decide)))
  have K₈ : Keeps prodW s s₈ := K₆.trans ((k₇.mono (by decide)).trans (k₈.mono (by decide)))
  have K₁₀ : Keeps prodW s s₁₀ := K₈.trans ((k₉.mono (by decide)).trans (k₁₀.mono (by decide)))
  have K : Keeps prodW s t := K₁₀.trans ((k₁₁.mono (by decide)).trans (k₁₂.mono (by decide)))
  refine ⟨?_, K⟩
  have J₂ : Keeps ([.x2, .x6, .x17] ++ crossRegs) s₁ s₂ := k₂.mono (by decide)
  have J₃ := J₂.trans (k₃.mono (by decide))
  have J₄ := J₃.trans (k₄.mono (by decide))
  have J₅ := J₄.trans (k₅.mono (by decide))
  have J₆ := J₅.trans (k₆.mono (by decide))
  have J₇ := J₆.trans (k₇.mono (by decide))
  have J₈ := J₇.trans (k₈.mono (by decide))
  have J₁₀ := J₈.trans ((k₉.mono (by decide)).trans (k₁₀.mono (by decide)))
  -- The values.
  have hlt := regsVal_lt s₁ bs
  rw [e₁] at hlt
  have hA := (e₁ : regsVal s₁ bs = wordsVal s.mem pa a 6).symm
  simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hA
  obtain ⟨X, hX⟩ : ∃ X, X = regsVal s₂ crossRegs := ⟨_, rfl⟩
  rw [← hX] at e₂ e₃
  simp only [regsVal, Nat.mul_zero, Nat.add_zero] at e₂
  have hsq := sq_arith hA e₂ rfl
  simp only [z₃, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, Nat.zero_add] at e₄
  simp only [J₄.gpr .x8 (by decide), Bool.false_eq_true, ite_false] at e₅
  simp only [J₅.gpr .x8 (by decide), ite_true] at e₆
  have v₇ := Word64.addCarry_value (s₆.gpr .x22) (s₆.gpr .x2) false
  simp only [ite_true] at e₇ c₇
  rw [← e₇, ← c₇, e₆, k₆.gpr .x22 (by decide), k₅.gpr .x22 (by decide), k₄.gpr .x22 (by decide)] at v₇
  have hD : regsVal s₇ [.x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4] =
      regsVal s₃ [.x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4] := by
    rw [regsVal_keep k₇ (by decide), regsVal_keep k₆ (by decide), regsVal_keep k₅ (by decide),
      regsVal_keep k₄ (by decide)]
  simp only [hD, sqsVal, J₇.gpr .x9 (by decide), J₇.gpr .x10 (by decide), J₇.gpr .x16 (by decide),
    J₇.gpr .x24 (by decide), Nat.mul_zero, Nat.add_zero] at e₈
  simp only [J₈.gpr .x25 (by decide), Bool.false_eq_true, ite_false] at e₉
  simp only [J₁₀.gpr .x25 (by decide), ite_true] at e₁₁
  have v₁₀ := Word64.addCarry_value (s₉.gpr .x5) (s₉.gpr .x2) s₉.c
  simp only [Bool.false_eq_true, ite_false] at e₁₀ c₁₀
  rw [← e₁₀, ← c₁₀, e₉, c₉, k₉.gpr .x5 (by decide), k₈.gpr .x5 (by decide), k₇.gpr .x5 (by decide),
    k₆.gpr .x5 (by decide), k₅.gpr .x5 (by decide), k₄.gpr .x5 (by decide)] at v₁₀
  have h6 : s₁₁.gpr .x6 = s₄.gpr .x6 := by
    rw [k₁₁.gpr _ (by decide), k₁₀.gpr _ (by decide), k₉.gpr _ (by decide), k₈.gpr _ (by decide),
      k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide)]
  rw [e₁₁, c₁₁, h6, e₄] at e₁₂
  have t17 : t.gpr .x17 = s₅.gpr .x17 := by
    rw [k₁₂.gpr _ (by decide), k₁₁.gpr _ (by decide), k₁₀.gpr _ (by decide), k₉.gpr _ (by decide),
      k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide)]
  have t22 : t.gpr .x22 = s₇.gpr .x22 := by
    rw [k₁₂.gpr _ (by decide), k₁₁.gpr _ (by decide), k₁₀.gpr _ (by decide), k₉.gpr _ (by decide),
      k₈.gpr _ (by decide)]
  have tD : regsVal t [.x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4] =
      regsVal s₈ [.x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4] := by
    rw [regsVal_keep k₁₂ (by decide), regsVal_keep k₁₁ (by decide), regsVal_keep k₁₀ (by decide),
      regsVal_keep k₉ (by decide)]
  have t5 : t.gpr .x5 = s₁₀.gpr .x5 := by rw [k₁₂.gpr _ (by decide), k₁₁.gpr _ (by decide)]
  have hT : regsVal t (tl ++ th) = (t.gpr .x17).toNat + 2 ^ 64 * (t.gpr .x22).toNat +
      2 ^ 128 * regsVal t [.x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4] + 2 ^ 640 * (t.gpr .x5).toNat +
      2 ^ 704 * (t.gpr .x6).toNat := by
    simp only [regsVal, List.cons_append, List.nil_append, Nat.mul_zero, Nat.add_zero, Nat.mul_add,
      ← Nat.mul_assoc, Nat.reduceMul, Nat.reducePow, Nat.add_assoc]
  have hC : regsVal s₃ crossRegs = (s₃.gpr .x22).toNat +
      2 ^ 64 * regsVal s₃ [.x23, .x11, .x12, .x13, .x14, .x15, .x21, .x4] + 2 ^ 576 * (s₃.gpr .x5).toNat := by
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, Nat.mul_add, ← Nat.mul_assoc, Nat.reduceMul, Nat.reducePow,
      Nat.add_assoc]
  have hc3 := Bool.toNat_le s₃.c
  rw [Nat.mod_eq_of_lt (a := s₃.c.toNat) (by omega_using [hc3])] at e₁₂
  simp only [ite_true, Bool.toNat_false, Nat.add_zero, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceMul] at e₃ e₈ v₇
  rw [hC] at e₃
  rw [hT, t17, t22, tD, t5, e₅, e₁₂]
  have h0 := Nat.mod_add_div ((s₁.gpr .x8).toNat * (s₁.gpr .x8).toNat) (2 ^ 64)
  have h5 := Nat.mod_add_div ((s₁.gpr .x25).toNat * (s₁.gpr .x25).toNat) (2 ^ 64)
  refine sqr_end (X := X) (by omega_using [e₃]) v₇ e₈ v₁₀ ?_ hlt
  rw [h0, h5]
  refine Eq.trans ?_ hsq
  simp only [Nat.mul_add, ← Nat.mul_assoc, Nat.reduceMul, Nat.reducePow, Nat.add_assoc]

end VG.Proof.Mont.AArch64.P384Field
