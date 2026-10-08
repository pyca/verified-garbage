import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Impl.Weierstrass.AArch64.Mont

/-!
# Montgomery products as functions on AArch64: rounds from registers

The functions' product (`Impl/Weierstrass/AArch64/Mont.lean`) multiplies by
words in registers only: `[b]`'s in `bRegsF`, and a general modulus's in
`mRegs`. Its rounds (`roundG`, `roundsG_ok`) are the inline product's
(`Proof/Mont/AArch64/Round.lean`) with those words in place of `bWords` and
`mWords`, for any registers the rounds do not write (`RoundSafe`), and for
P-384's `p` a reduction without its words (`redSparse_ok`); the reduction of
the result subtracts the modulus's words in registers (`csubM_ok`, as
`csubR_ok`); and the modulus's distinct words are built in their registers
(`constLoads_ok`).
-/

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

theorem roundF_eq (n m i : Nat) : roundF n m i = roundG (mod n m) (raF n) (bRegsF n) (sparseOk n m) i := rfl

/-! ## P-384's sparse reduction -/

/-- P-384's `p`, `2^384 - 2^128 - 2^96 + 2^32 - 1`. -/
abbrev p384 : Nat := 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319

/-- `2^384 + 2^32`, `sparseWords`' value. -/
abbrev sparseVal : Nat := 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806632285274112

/-- `p = 2^384 + 2^32 - (2^128 + 2^96 + 1)`. -/
theorem p384_eq : p384 + 2 ^ 128 + 2 ^ 64 * 2 ^ 32 + 1 = sparseVal := by decide +kernel

/-- `2^512`. -/
theorem pow512 : 2 ^ (64 * 8) = 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by decide +kernel

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
  have x1₁ : s₁.gpr .x1 = s.gpr .x1 := k₁.gpr _ (by decide)
  have x1₂ : s₂.gpr .x1 = s.gpr .x1 := by rw [k₂.gpr _ (by decide), x1₁]
  have z₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), hz]
  have v₃ := VG.Proof.Ed25519.Word64.addCarry_value (s₂.gpr .x3) (s₂.gpr .x1) false
  have v₄ := VG.Proof.Ed25519.Word64.addCarry_value (s₃.gpr .x7) (s₃.gpr .x7) s₃.c
  rw [← e₃, ← c₃] at v₃
  rw [← e₄, z₃] at v₄
  simp only [BitVec.toNat_zero, Nat.zero_add, Bool.toNat_false, Nat.add_zero] at v₃ v₄
  refine ⟨?_, ?_, ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans
    ((k₃.mono (by sub_regs)).trans (k₄.mono (by sub_regs)))⟩
  · rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide)]
    simpa only [Piece.reg, Piece.val] using e₁
  · have hx3 : s₄.gpr .x3 = s₃.gpr .x3 := k₄.gpr _ (by decide)
    have hc : (s₄.gpr .x23).toNat = s₃.c.toNat := by
      have := (s₄.gpr .x23).isLt
      have := Bool.toNat_le s₃.c
      have : (VG.Proof.Ed25519.Word64.carryOut 0 0 s₃.c).toNat = 0 := by cases s₃.c <;> rfl
      omega
    rw [hx3, hc, ← x1₂]
    omega

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
    have ht := (List.nodup_cons.mp hnd)
    rw [subsIn, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (diffM1_ok s t t r first rfl) fun s₁ ⟨e₁, k₁⟩ => ?_
    refine WP.mono (subsIn_ok false ts rs (.inl rfl) hl ht.2 fun q hq hq' =>
      hrt q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ hq')) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => ht.1 (h ▸ hq))
    have hM : regsVal s₁ rs = regsVal s rs := regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => hrt q (List.mem_cons_of_mem _ hq) (h ▸ List.mem_cons_self ..))
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.gpr t ht.1
    have hr : s.gpr r = s.gpr r := rfl
    simp only [Bool.false_eq_true, ite_false] at e₂
    rw [hR, hM] at e₂
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, List.length_cons, pow64_succ, ht₂]
    rw [Nat.mul_assoc]
    omega

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
  have hw := wins_regs hn i
  rw [WP.block_append_iff]
  refine WP.mono (ldR_ok hpa ha (by omega) .x1) fun s₁ ⟨c₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (by decide), hz]
  have hT₁ : ∀ ts : List Reg, (∀ q ∈ ts, q ∈ wins M.n i) → regsVal s₁ ts = regsVal s ts :=
    fun ts hts => regsVal_congr fun q hq => k₁.gpr q (by simp [(hw q (hts q hq)).2.1])
  have hRB : rwVal s₁ base (regWords bs) = regsVal s bs := by
    rw [rwVal_regWords]
    exact regsVal_keep hbs k₁ (by sub_regs)
  have hA := (word s.mem pa (8 * i)).isLt
  have hAB : (word s.mem pa (8 * i)).toNat * regsVal s bs ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega) (by omega)
  have hlen : (wins M.n i).length = M.n + 2 := wins_length M.n i
  have htake : ∀ q ∈ (wins M.n i).take (M.n + 1), q ∈ wins M.n i := fun q hq => List.mem_of_mem_take hq
  have hdrop : ∀ q ∈ (wins M.n i).drop (M.n + 1), q ∈ wins M.n i := fun q hq => List.mem_of_mem_drop hq
  have hnd := (fresh_wins hn i).1
  have hdisj : ∀ q ∈ (wins M.n i).drop (M.n + 1), q ∉ (wins M.n i).take (M.n + 1) := fun q hq ht => by
    have hnd' : ((wins M.n i).take (M.n + 1) ++ (wins M.n i).drop (M.n + 1)).Nodup := by
      rw [List.take_append_drop]; exact hnd
    exact (List.nodup_append.mp hnd').2.2 q ht q hq rfl
  have hn0 : Reg.x0 ∉ wins M.n i := fun h => (hw _ h).1 rfl
  have hRO := rowOk_regs (size := size) hn i hbs
  by_cases ht : M.tight = true
  · rw [prodWins, ite_eq_left_iff.mpr (fun h => absurd ht h)]
    have hti := Mod.ok_tight hok ht
    have hRT : regsVal s ((wins M.n i).take (M.n + 1)) < 2 * m := by
      have := regsVal_wins_split s M.n i; omega
    have hP1 : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    refine WP.mono (row_ok hs₁.ptr hz₁ (hRO.sub (List.take_sublist _ _)) (by decide) (by decide)
        (fun h => hn0 (List.mem_of_mem_take h))
        (by rw [regWords_length, List.length_take, hlen]; omega) (by
          rw [hT₁ _ htake, c₁, hRB, List.length_take, hlen, Nat.min_eq_left (by omega)]
          omega)) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono fun q hq => by
          simp only [List.mem_cons] at hq ⊢
          rcases hq with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (htake q h))))⟩
    have hd : ∀ q ∈ (wins M.n i).drop (M.n + 1), s₂.gpr q = s₁.gpr q := fun q hq => k₂.gpr q (by
      have := hw q (hdrop q hq)
      simp only [List.mem_cons, not_or]
      exact ⟨this.2.2.1, this.2.2.2.1, hdisj q hq⟩)
    rw [regsVal_wins_split s₂, regsVal_wins_split s, e₂, regsVal_congr hd, hT₁ _ hdrop, hT₁ _ htake,
      c₁, hRB]
    omega
  · rw [prodWins, ite_eq_right_iff.mpr (fun h => absurd h ht)]
    have hP : 2 ^ (64 * (M.n + 2)) = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
      rw [show 64 * (M.n + 2) = 64 * M.n + 64 + 64 by omega, Nat.pow_add, Nat.pow_add]
    have hmX : m ≤ 2 ^ (64 * M.n) := Nat.le_of_lt hm
    refine WP.mono (row_ok hs₁.ptr hz₁ hRO (by decide) (by decide) hn0
        (by rw [regWords_length, hlen]; omega) (by
        rw [hT₁ _ (fun _ h => h), c₁, hRB, hlen, hP]
        have : (2 ^ 64 - 1) * m ≤ (2 ^ 64 - 1) * 2 ^ (64 * M.n) := Nat.mul_le_mul_left _ hmX
        have : 2 ^ (64 * M.n) * 2 ^ 64 ≤ 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
        omega)) fun s₂ ⟨e₂, k₂⟩ => ?_
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
  have hred := Mod.ok_red hok
  have hw := wins_regs hn i
  have n0 : Reg.x0 ∉ wins M.n i := fun h => (hw _ h).1 rfl
  have n6 : Reg.x6 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.1 rfl
  have n7 : Reg.x7 ∉ wins M.n i := fun h => (hw _ h).2.2.2.2.2.2.2.1 rfl
  have hcons := wins_cons M.n i
  have ht0 : win M.n i 0 ∈ wins M.n i := by rw [hcons]; exact List.mem_cons_self ..
  have hlen : (wins M.n i).length = M.n + 2 := wins_length M.n i
  have hAB : (word s.mem pa (8 * i)).toNat * regsVal s bs ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by have := (word s.mem pa (8 * i)).isLt; omega) (by omega)
  have hrot : ∀ t : State, (t.gpr (win M.n i 0)).toNat = 0 →
      2 ^ 64 * regsVal t (wins M.n (i + 1)) = regsVal t (wins M.n i) := by
    intro t h0
    rw [wins_succ, regsVal_append, hcons, regsVal]
    simp only [regsVal, h0, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  have hkw : ∀ q ∈ Reg.x1 :: Reg.x2 :: Reg.x3 :: wins M.n i, q ∈ Reg.x1 :: .x2 :: .x3 :: .x23 :: wins M.n i :=
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
    have hcode : roundG M ra bs true i = ([.ldr .x .x1 ra (8 * i)] ++ row .x0 .x1 (prodWins M i) (regWords bs)) ++
        redSparse M.n i := by simp only [roundG, ite_true]
    have h6' : s.gpr .x6 = M.minv := by unfold ConstOk at h6; rw [hrg] at h6; exact h6
    rw [hcode, WP.block_append_iff]
    refine WP.mono (prodRowG_ok hs hn hpa hbs hbl ha hz hm' hok hB hT) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hs₂ := hs.of_keeps k₂ (by simp [n0])
    have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    have h6₂ : s₂.gpr .x6 = M.minv := by rw [k₂.gpr _ (by simp [n6]), h6']
    rw [redSparse, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (mulU_ok s₂ (win M.n i 0)) fun s₃ ⟨u₃, k₃⟩ => ?_
    have hs₃ := hs₂.of_keeps k₃ (by decide)
    have hz₃ : s₃.gpr .x7 = 0 := by rw [k₃.gpr .x7 (by decide), hz₂]
    have hT₃ : regsVal s₃ (wins M.n i) = regsVal s₂ (wins M.n i) := regsVal_congr fun q hq =>
      k₃.gpr q (by simp [(hw q hq).2.1])
    have hu := (s₃.gpr .x1).isLt
    rw [WP.block_append_iff]
    have hRO : RowOk size .x1 (wins M.n i) sparseWords :=
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
    have hRS : rwVal s₃ base sparseWords = sparseVal := by
      simp only [sparseWords, rwVal, RWord.val, Nat.mul_zero, Nat.add_zero, Nat.zero_add]; decide +kernel
    have hV₂ : regsVal s₂ (wins M.n i) < 2 * p384 + (2 ^ 64 - 1) * p384 := by rw [e₂]; omega
    refine WP.mono (row_ok hs₃.ptr hz₃ hRO (by decide) (by decide) n0
        (by rw [hlen, hn6]; decide) (by rw [hT₃, hRS, hlen, hn6, pow512]; omega)) fun s₄ ⟨e₄, k₄⟩ => ?_
    rw [hT₃, hRS] at e₄
    have hs₄ := hs₃.of_keeps k₄ (by simp [n0])
    have hz₄ : s₄.gpr .x7 = 0 := by rw [k₄.gpr _ (by simp [n7]), hz₃]
    have x1₄ : s₄.gpr .x1 = s₃.gpr .x1 := k₄.gpr _ (by simp [(hw .x1)])
    rw [WP.block_append_iff]
    refine WP.mono (nWords_ok hs₄ hz₄) fun s₅ ⟨n₂, n₃, k₅⟩ => ?_
    have n23 : Reg.x23 ∉ wins M.n i := fun h => by
      have := wins_sub_acc hn i _ h; rw [hn6] at this; exact absurd this (by decide)
    have hT₅ : regsVal s₅ (wins M.n i) = regsVal s₄ (wins M.n i) := regsVal_congr fun q hq =>
      k₅.gpr q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (rfl | rfl | rfl)
        · exact (hw _ hq).2.2.1 rfl
        · exact (hw _ hq).2.2.2.1 rfl
        · exact n23 hq)
    have x1₅ : s₅.gpr .x1 = s₃.gpr .x1 := by rw [k₅.gpr _ (by decide), x1₄]
    have z₅ : s₅.gpr .x7 = 0 := by rw [k₅.gpr _ (by decide), hz₄]
    have hrs : ∀ r ∈ ([.x1, .x2, .x3, .x23] ++ List.replicate (M.n - 2) .x7 : List Reg),
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
        (.inr (by rw [hcons]; exact List.cons_ne_nil _ _)) (by rw [hlen]; simp; omega) (fresh_wins hn i).1 hrs)
      fun s₆ ⟨e₆, k₆⟩ => ?_
    have hN : regsVal s₅ ([.x1, .x2, .x3, .x23] ++ List.replicate (M.n - 2) .x7) =
        (s₃.gpr .x1).toNat + 2 ^ 64 * ((s₃.gpr .x1).toNat * 2 ^ 32 % 2 ^ 64) +
          2 ^ 128 * ((s₃.gpr .x1).toNat / 2 ^ 32 + (s₃.gpr .x1).toNat) := by
      rw [hn6]
      simp only [show 6 - 2 = 4 from rfl, List.replicate, List.cons_append, List.nil_append, regsVal,
        z₅, BitVec.toNat_zero, x1₅, n₂, Nat.mul_zero, Nat.add_zero]
      rw [← n₃, ← x1₄]
      omega
    rw [hT₅, hN, e₄, hlen, hn6, pow512] at e₆
    simp only [ite_true, Bool.not_true, Bool.toNat_false, Nat.add_zero] at e₆
    have hRl := regsVal_lt s₆ (wins M.n i)
    rw [hlen, hn6, pow512] at hRl
    have hpe := p384_eq
    -- The sum: `T + u p`, without a borrow.
    have hsplit : (s₃.gpr .x1).toNat * 2 ^ 32 = (s₃.gpr .x1).toNat * 2 ^ 32 % 2 ^ 64 +
        2 ^ 64 * ((s₃.gpr .x1).toNat / 2 ^ 32) := by omega
    have hval : regsVal s₆ (wins M.n i) = regsVal s₂ (wins M.n i) + (s₃.gpr .x1).toNat * p384 := by
      rcases Bool.eq_false_or_eq_true (!s₆.c) with hb | hb <;> rw [hb] at e₆ <;>
        simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at e₆ <;>
        omega
    have h₆ : (regsVal s₆ (wins M.n i)) % 2 ^ 64 = (s₆.gpr (win M.n i 0)).toNat := by
      rw [hcons, regsVal]; omega
    have hlow : (s₆.gpr (win M.n i 0)).toNat = 0 := by
      have ht0₂ : (regsVal s₂ (wins M.n i)) % 2 ^ 64 = (s₂.gpr (win M.n i 0)).toNat := by
        rw [hcons, regsVal]; omega
      have h := mont_low (s₂.gpr (win M.n i 0)).toNat M.minv.toNat p384 hinv
      rw [h6₂] at u₃
      rw [← u₃] at h
      rw [← h₆, hval]
      omega
    have hum : (s₃.gpr .x1).toNat * p384 ≤ (2 ^ 64 - 1) * p384 := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    refine ⟨⟨(s₃.gpr .x1).toNat, by rw [hrot s₆ hlow, hval, e₂]⟩, ?_, ?_⟩
    · have : 2 ^ 64 * regsVal s₆ (wins M.n (i + 1)) < 2 ^ 64 * (2 * p384) := by
        rw [hrot s₆ hlow, hval, e₂]; omega
      exact Nat.lt_of_mul_lt_mul_left this
    · exact (((k₂.mono hkw).trans (k₃.mono (by sub_regs))).trans ((k₄.mono (by sub_regs)).trans
        (k₅.mono (by sub_regs)))).trans (k₆.mono (by sub_regs))
  | false =>
    obtain ⟨ws, hr⟩ := hfr hspv
    have hcode : roundG M ra bs false i = ([.ldr .x .x1 ra (8 * i)] ++ row .x0 .x1 (prodWins M i) (regWords bs)) ++
        (row .x0 (win M.n i 0) (wins M.n i).tail (ws.map (fWord (firstGen ws))) ++
          ([.movz .x (win M.n i 0) 0 0] : List Instr)) := by
      simp only [roundG, hr, Bool.false_eq_true, ite_false]
    have hok := hred
    rw [hr] at hok
    simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hwl, hm1⟩, hmv⟩, hwok⟩ := hok
    have h6' : ∀ v, firstGen ws = some v → s.gpr .x6 = BitVec.ofNat 64 v := by
      unfold ConstOk at h6; rw [hr] at h6; exact h6
    have hm2 : 2 ^ 64 * mwVal ws = m + 1 := by
      rw [hmv]
      have := Nat.div_add_mod (m + 1) (2 ^ 64)
      have : (m + 1) % 2 ^ 64 = 0 := by omega
      omega
    rw [hcode, WP.block_append_iff]
    refine WP.mono (prodRowG_ok hs hn hpa hbs hbl ha hz hm' hok hB hT) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hs₂ := hs.of_keeps k₂ (by simp [n0])
    have hz₂ : s₂.gpr .x7 = 0 := by rw [k₂.gpr _ (by simp [n7]), hz]
    have h6₂ : ∀ v, firstGen ws = some v → s₂.gpr .x6 = BitVec.ofNat 64 v := fun v hv => by
      rw [k₂.gpr _ (by simp [n6]), h6' v hv]
    have hRF : rwVal s₂ base (ws.map (fWord (firstGen ws))) = mwVal ws := rwVal_fWords h6₂ ws hwok
    have hsplit : ∀ t : State, regsVal t (wins M.n i) =
        (t.gpr (win M.n i 0)).toNat + 2 ^ 64 * regsVal t (wins M.n i).tail := by
      intro t; rw [hcons]; rfl
    have htl : (wins M.n i).tail.length = M.n + 1 := by rw [wins_tail]; simp
    have hPt : 2 ^ (64 * (M.n + 1)) = 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [show 64 * (M.n + 1) = 64 * M.n + 64 by omega, Nat.pow_add]
    have hS := hsplit s₂
    have ht0v := (s₂.gpr (win M.n i 0)).isLt
    have htm : (s₂.gpr (win M.n i 0)).toNat * m ≤ (2 ^ 64 - 1) * m :=
      Nat.mul_le_mul (by omega) (Nat.le_refl _)
    have hkey : 2 ^ 64 * (regsVal s₂ (wins M.n i).tail + (s₂.gpr (win M.n i 0)).toNat * mwVal ws) =
        regsVal s₂ (wins M.n i) + (s₂.gpr (win M.n i 0)).toNat * m := by
      rw [Nat.mul_add, Nat.mul_left_comm, hm2, Nat.mul_add, Nat.mul_one, hS]; omega
    have hmP : (2 ^ 64 - 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul (by omega) (by omega)
    rw [WP.block_append_iff]
    refine WP.mono (row_ok hs₂.ptr hz₂ (rowOkF hn i hwok (firstGen ws)) (by decide) (by decide)
        (fun h => n0 (List.mem_of_mem_tail h)) (by
        rw [List.length_map, hwl, htl]; omega) (by
        rw [hRF, htl, hPt]
        have : 2 ^ 64 * (regsVal s₂ (wins M.n i).tail + (s₂.gpr (win M.n i 0)).toNat * mwVal ws) <
            2 ^ 64 * (2 ^ (64 * M.n) * 2 ^ 64) := by
          rw [hkey, e₂]; omega
        exact Nat.lt_of_mul_lt_mul_left this)) fun s₃ ⟨e₃, k₃⟩ => ?_
    rw [hRF] at e₃
    refine WP.mono (movz0_ok s₃ (win M.n i 0)) fun s₄ ⟨z₄, k₄⟩ => ?_
    have htl₄ : regsVal s₄ (wins M.n i).tail = regsVal s₃ (wins M.n i).tail := regsVal_congr
      fun q hq => k₄.gpr q (by
        have hnd := (fresh_wins hn i).1
        rw [hcons] at hnd
        simp only [List.mem_singleton]
        intro h; subst h
        exact (List.nodup_cons.mp hnd).1 (by rw [← wins_tail]; exact hq))
    have hval : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) = regsVal s₂ (wins M.n i) +
        (s₂.gpr (win M.n i 0)).toNat * m := by
      rw [wins_succ, regsVal_append, ← wins_tail, htl, htl₄, e₃]
      simp only [regsVal, z₄, Nat.mul_zero, Nat.add_zero]
      exact hkey
    refine ⟨⟨(s₂.gpr (win M.n i 0)).toNat, by rw [hval, e₂]⟩, ?_, ?_⟩
    · have : 2 ^ 64 * regsVal s₄ (wins M.n (i + 1)) < 2 ^ 64 * (2 * m) := by
        rw [hval, e₂]; omega
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
  | 0, _, s, _, _, _, _, _, hB, h0 => WP.block_nil ⟨⟨0, by simp [h0, wordsVal]⟩, by rw [h0]; omega,
      ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩⟩
  | k + 1, hk, s, base, hs, hpa, hz, h6, hB, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (roundsG_ok hn hra hbs hbl hsp hfr ha hm' hinv hok k (by omega) hs hpa hz h6 hB h0)
      fun s₁ ⟨⟨U, eU⟩, hT, k₁⟩ => ?_
    have hmem : s₁.mem = s.mem := k₁.mem
    have hacc := acc_regs_lt _ hn
    have nk : ∀ r ∈ [Reg.x0, .x6, .x7], r ∉ Reg.x1 :: Reg.x2 :: Reg.x3 :: Reg.x23 :: acc M.n := by
      intro r hr h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases h with h | h | h | h | h
      · rcases hr with rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl <;> exact absurd h (by decide)
      · rcases hr with rfl | rfl | rfl <;> exact absurd h (by decide)
      · have := hacc r h
        rcases hr with rfl | rfl | rfl <;> simp at this
    have hs₁ := hs.of_keeps k₁ (nk .x0 (by simp))
    have hpa₁ := hpa.of_keeps k₁ hra
    have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr .x7 (nk .x7 (by simp)), hz]
    have hB₁ : regsVal s₁ bs = regsVal s bs := regsVal_keep hbs k₁ (fun _ h => h)
    have h6₁ : ConstOk M s₁ := h6.keep (k₁.gpr .x6 (nk .x6 (by simp)))
    refine WP.mono (roundG_ok hs₁ hn hpa₁ hbs hbl hsp hfr (i := k) (by omega) hz₁ hm' hinv hok h6₁
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
            rw [eU, Nat.add_mul, Nat.add_mul, Nat.zero_add]; omega
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
    have hdP := hd.2 d (List.mem_cons_self ..)
    rw [diffsM, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (diffM1_ok s t d r first rfl) fun s₁ ⟨e₁, k₁⟩ => ?_
    refine WP.mono (diffsM_ok false ts ds ms (.inl rfl) hl hm hf.tail hd.tail fun q hq hq' =>
      hmd q (List.mem_cons_of_mem _ hq) (List.mem_cons_of_mem _ hq')) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      have hq' := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => dPool_fresh hdP hq' h.symm)
    have hM : regsVal s₁ ms = regsVal s ms := regsVal_congr fun q hq => k₁.gpr q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => hmd q (List.mem_cons_of_mem _ hq) (h ▸ List.mem_cons_self ..))
    have hd₂ : s₂.gpr d = s₁.gpr d := k₂.gpr d (List.nodup_cons.mp hd.1).1
    simp only [Bool.false_eq_true, ite_false] at e₂
    rw [hR, hM] at e₂
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, List.length_cons, pow64_succ, hd₂]
    rw [Nat.mul_assoc]
    omega

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
  have hDl' := hDl (by omega)
  rw [csubM, List.append_assoc, WP.block_append_iff]
  refine WP.mono (diffsM_ok true ts (dRegs n) ms (.inr fun h => by subst h; simp at hlen; omega) (by rw [hlen, hDl']) (by rw [hml, hlen]) hft hD hmd)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (fun h => (dPool_ne _ (hD.2 _ h)).2.1 rfl), hz]
  rw [WP.block_append_iff]
  refine WP.mono (flagR_ok s₁ top hz₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have htopP : ∀ d ∈ dRegs n, d ≠ top := fun d hd => dPool_fresh (hD.2 d hd) (by
    simp [htop.2.1, htop.2.2.1, htop.2.2.2.1, htop.2.2.2.2.1, htop.2.2.2.2.2.1, htop.2.2.2.2.2.2.1,
      htop.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.2.2])
  have htop₁ : s₁.gpr top = s.gpr top := k₁.gpr top fun h => htopP _ h rfl
  rw [htop₁] at x₂
  have hDs : ∀ q ∈ dRegs n, q ∉ [Reg.x2] := fun q hq hq' =>
    (dPool_ne q (hD.2 q hq)).1 (List.mem_singleton.mp hq')
  refine WP.mono (selectsR_ok ts (dRegs n) (decide ((s.gpr top).toNat < (!s₁.c).toNat))
    (s := s₂) (by rw [hlen, hDl']) hft hD x₂) fun s₃ ⟨e₃, k₃, _⟩ => ?_
  have hR₂ : regsVal s₂ ts = regsVal s ts := by
    rw [regsVal_congr fun q hq => k₂.gpr q (by
      have := hft.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact this.2.2.1)]
    exact regsVal_congr fun q hq => k₁.gpr q (by
      have hq' := hft.2 q hq
      exact fun h => dPool_fresh (hD.2 _ h) hq' rfl)
  have hD₂ : regsVal s₂ (dRegs n) = regsVal s₁ (dRegs n) :=
    regsVal_congr fun q hq => k₂.gpr q (hDs q hq)
  rw [hlen, hm] at e₁
  simp only [ite_true, Bool.not_true, Bool.toNat_false, Nat.add_zero] at e₁
  refine ⟨?_, (k₁.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr)).trans
      ((k₂.mono (by sub_regs)).trans (k₃.mono fun r hr =>
        List.mem_cons_of_mem _ (List.mem_append_left _ hr)))⟩
  rw [e₃, hR₂, hD₂]
  simp only [decide_eq_true_eq]
  have hDlt := regsVal_lt s₁ (dRegs n)
  rw [hDl'] at hDlt
  exact csub_arith (b := !s₁.c) hmX hDlt hV (by omega)

/-! ## Constants into registers -/

/-- Each pair's constant into its register, for distinct registers. -/
theorem constLoads_ok : ∀ (L : List (Reg × BitVec 64)) {s : State}, (L.map Prod.fst).Nodup →
    WP isa (.block (L.flatMap fun p => const64 p.1 p.2)) s fun s' =>
      (∀ p ∈ L, s'.gpr p.1 = p.2) ∧ Keeps (L.map Prod.fst) s s'
  | [], s, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | p :: L, s, hnd => by
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (const64_ok s p.1 p.2) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hnd' := List.nodup_cons.mp hnd
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
      List.map_nil, regsVal]; omega
  | j, n + 1, x, hx, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.shiftRight_zero] at h0
    have hr := regsVal_of_shifts s f (j + 1) n (x >>> 64) (by
        rw [Nat.shiftRight_eq_div_pow]
        rw [pow64_succ] at hx
        exact Nat.div_lt_of_lt_mul hx) fun k hk => by
      rw [show j + 1 + k = j + (k + 1) by omega, h (k + 1) (by omega), ← Nat.shiftRight_add,
        show 64 + 64 * k = 64 * (k + 1) by omega]
    rw [List.range'_succ, List.map_cons, regsVal, hr, h0, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_add_div x _

end VG.Proof.Weierstrass.AArch64.Mont
