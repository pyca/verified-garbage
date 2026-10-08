import VerifiedGarbage.Impl.Ed25519.X86_64.CombTable
import VerifiedGarbage.Proof.Ed25519.WindowConstants
import VerifiedGarbage.Impl.Ed25519.X86_64.Comb
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowStep
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.CallLay

/-! Merged from `Proof.Ed25519.X86_64.CombConstants`. -/
section
/-!
# The comb's tables represent `[k 1024^j]B`, and `combG` represents `[G]B`

Each entry is turned back into affine `(x, y)` (`uncache`, which the kernel
checks inverts the caching) and `checkTables` walks the tables once: within
table `j`, each entry is the previous one plus the first, with the
specification's addition, compared projectively; the first entry of table `j +
1` is `[1024]` of table `j`'s, with the specification's `pointMul`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG.Spec.Ed25519 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open Spec.X25519 (Fe)

/-- `1/2`. -/
def half : Fe := ⟨(Spec.X25519.P + 1) / 2, by decide⟩

/-- The affine `(x, y)` of a cached entry `[y - x, y + x, 2dxy]` with `Z = 1`. -/
def uncache (e : Fe × Fe × Fe) : Fe × Fe := ((e.2.1 - e.1) * half, (e.2.1 + e.1) * half)

/-- The entries `p`, `p + b`, `p + 2b`, …, each compared with `p`'s representative. -/
private def checkRow (b p : Point) : List (Fe × Fe) → Bool
  | [] => true
  | q :: qs => (q.1 * p.Z == p.X && q.2 * p.Z == p.Y && p.Z != 0) &&
      checkRow b (pointAdd (affPt q) b) qs

private theorem checkRow_ok (b p : Point) (c a : EPoint dZ) (hb : Rep b c) (h : Rep p a)
    (qs : List (Fe × Fe)) (hc : checkRow b p qs = true) (i : Nat) (hi : i < qs.length) :
    Rep (affPt (qs.getD i (0, 1))) (i • c + a) := by
  induction qs generalizing p a i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons q qs ih =>
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨hx, hy⟩, hz⟩, hrest⟩ := hc
    have hq : Rep (affPt q) a := by
      refine h.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_
        (by show toZ (q.1 * q.2) * toZ 1 = toZ q.1 * toZ q.2; rw [toZ_mul, toZ_one, mul_one])
      · show toZ q.1 * toZ p.Z = toZ p.X * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hx]
      · show toZ q.2 * toZ p.Z = toZ p.Y * toZ 1
        rw [toZ_one, mul_one, ← toZ_mul, hy]
    cases i with
    | zero => simpa using hq
    | succ i =>
      have := ih _ _ (pointAdd_rep hq hb) hrest i (by simp only [List.length_cons] at hi; omega)
      rw [List.getD_cons_succ]
      convert this using 1
      rw [succ_nsmul]; abel

/-- Each table checked from the representative `b` of its first entry. -/
private def checkTables (b : Point) : List (List (Fe × Fe)) → Bool
  | [] => true
  | row :: rows => checkRow b b row && checkTables (pointMul 1024 b) rows

private theorem checkTables_ok (b : Point) (c : EPoint dZ) (hb : Rep b c)
    (rows : List (List (Fe × Fe))) (hc : checkTables b rows = true) (j : Nat) (hj : j < rows.length)
    (k : Nat) (hk : k < (rows.getD j []).length) :
    Rep (affPt ((rows.getD j []).getD k (0, 1))) ((k + 1) • ((1024 ^ j) • c)) := by
  induction rows generalizing b c j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons row rows ih =>
    simp only [checkTables, Bool.and_eq_true] at hc
    cases j with
    | zero =>
      rw [List.getD_cons_zero] at hk ⊢
      have := checkRow_ok b b c c hb hb row hc.1 k hk
      rw [pow_zero, one_nsmul, succ_nsmul]
      exact this
    | succ j =>
      rw [List.getD_cons_succ] at hk ⊢
      have := ih (pointMul 1024 b) ((1024 : Nat) • c) (pointMul_rep 1024 hb) hc.2 j
        (by simp only [List.length_cons] at hj; omega) hk
      rw [smul_smul, smul_smul] at this
      rw [smul_smul, pow_succ, ← Nat.mul_assoc]
      exact this

private theorem tables_check :
    checkTables basePoint (combTable.map (·.map uncache)) = true := by decide +kernel

/-- The caching of `affPt (uncache e)`. -/
private def recache (e : Fe × Fe × Fe) : Fe × Fe × Fe :=
  ((uncache e).2 - (uncache e).1, (uncache e).2 + (uncache e).1,
    (uncache e).1 * (uncache e).2 * 2 * d)

private theorem tables_cached :
    combTable.all (fun row => row.all fun e => decide (recache e = e)) = true := by decide +kernel

theorem tables_length :
    combTable.length = 26 ∧ combTable.all (fun row => row.length == 16) = true := by decide +kernel

private theorem getD_map' {α β : Type} (l : List α) (f : α → β) (n : Nat) (d : α) :
    (l.map f).getD n (f d) = f (l.getD n d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

private theorem uncache_default : uncache (1, 1, 0) = (0, 1) := by decide

theorem combCached_ok (j k : Nat) (hj : j < 26) (hk : k < 17) :
    ∃ q, combCached j k = cache q ∧ Rep q ((k * 1024 ^ j) • baseAff) := by
  cases k with
  | zero =>
    refine ⟨identity, ?_, ?_⟩
    · simp only [combCached, ↓reduceIte]; decide +kernel
    · rw [Nat.zero_mul, zero_smul]; exact identity_rep
  | succ k =>
    have hrow : (combTable.getD j []) ∈ combTable := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tables_length.1]; exact hj)]
      exact List.getElem_mem _
    have hlen : (combTable.getD j []).length = 16 :=
      beq_iff_eq.mp (List.all_eq_true.mp tables_length.2 _ hrow)
    have hmem : (combTable.getD j []).getD k (1, 1, 0) ∈ combTable.getD j [] := by
      have hk' : k < (combTable.getD j []).length := by rw [hlen]; omega
      rw [List.getD_eq_getElem?_getD (l := combTable.getD j []), List.getElem?_eq_getElem hk']
      exact List.getElem_mem _
    have hre := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp tables_cached _ hrow) _ hmem)
    refine ⟨affPt (uncache ((combTable.getD j []).getD k (1, 1, 0))), ?_, ?_⟩
    · simp only [combCached, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      generalize (combTable.getD j []).getD k (1, 1, 0) = e at hre
      obtain ⟨a, b, c⟩ := e
      simp only [recache, Prod.mk.injEq] at hre
      simp only [cache, affPt, Point.mk.injEq]
      exact ⟨hre.1.symm, hre.2.1.symm, hre.2.2.symm, rfl⟩
    · have hgj : (combTable.map (·.map uncache)).getD j [] = (combTable.getD j []).map uncache := by
        rw [show ([] : List (Fe × Fe)) = ([] : List (Fe × Fe × Fe)).map uncache from rfl, getD_map']
      have hr := checkTables_ok basePoint baseAff basePoint_rep _ tables_check j
        (by rw [List.length_map, tables_length.1]; exact hj) k
        (by rw [hgj, List.length_map, hlen]; omega)
      rw [hgj, ← uncache_default, getD_map', smul_smul] at hr
      exact hr

/-- The constant the comb's digits are offset by: `16 Σ_{j < 26} 1024^j`. -/
def combGVal : Nat := 16 * ((1024 ^ 26 - 1) / 1023)

private def combGCheck (p : Point) : Bool := combG.X * p.Z == p.X && combG.Y * p.Z == p.Y && p.Z != 0

private theorem combG_check : combGCheck (pointMul combGVal basePoint) = true := by decide +kernel

theorem combG_ok : Rep combG (combGVal • baseAff) := by
  have hp := pointMul_rep combGVal basePoint_rep
  have hc := combG_check
  simp only [combGCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  refine hp.of_proj (show toZ 1 ≠ 0 by decide) ?_ ?_ ?_
  · show toZ combG.X * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hx]
  · show toZ combG.Y * toZ _ = toZ _ * toZ 1
    rw [toZ_one, mul_one, ← toZ_mul, hy]
  · show toZ (combGAff.1 * combGAff.2) * toZ 1 = toZ combGAff.1 * toZ combGAff.2
    rw [toZ_mul, toZ_one, mul_one]

theorem combGCached_eq : combGCached = cache combG := by decide +kernel

end VG.Proof.Ed25519.X86_64
end

/-!
# The comb's constant-time selection, from the tables in the static

`combWords` holds entry `k = 1 … 16` of table `j` (`combCached j k`, without
its `2Z`) at word `192 j + 12 (k - 1)`, at `T + 1536 j + 96 (k - 1)` in a memory
holding the tables at `T` (`CombTbl`). The selection (`combSelect_ok`) sets
`rdx` to table `j`'s address (`combSelSetup_ok`), clears the accumulators,
keeps, for every entry `m`, its six 16-byte pieces under the mask of the
magnitude `a = m` (`combSelEntry_ok`), so that accumulator `c` ends with piece
`c` of entry `a`, or zero for `a = 0` (`accVal`), and stores them to slots
4–6; for `a = 0`, `combSelOne` sets the low words of `Y - X` and `Y + X` to 1,
the identity's.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside F val4)

/-! ## The tables' words -/

/-- The words of an entry: `Y - X`, `Y + X`, `2dT`. -/
abbrev entryWords (e : Spec.X25519.Fe × Spec.X25519.Fe × Spec.X25519.Fe) : List (BitVec 64) :=
  feWords e.1 ++ feWords e.2.1 ++ feWords e.2.2

theorem entryWords_length (e : Spec.X25519.Fe × Spec.X25519.Fe × Spec.X25519.Fe) :
    (entryWords e).length = 12 := by simp [feWords]

theorem length_flatMap_const {α β : Type} (f : α → List β) (k : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = k) → (l.flatMap f).length = l.length * k
  | [], _ => by simp
  | x :: l, h => by
    rw [List.flatMap_cons, List.length_append, h x (List.mem_cons_self ..),
      length_flatMap_const f k l (fun y hy => h y (List.mem_cons_of_mem _ hy)), List.length_cons,
      Nat.succ_mul, Nat.add_comm]

/-- Element `q k + r` of a list of lists of `k` elements each. -/
theorem getD_flatMap_const {α β : Type} (f : α → List β) (k : Nat) (d : β) :
    ∀ (l : List α) (da : α), (∀ x ∈ l, (f x).length = k) → ∀ q < l.length, ∀ r < k,
      (l.flatMap f).getD (q * k + r) d = (f (l.getD q da)).getD r d
  | [], _, _, q, hq, _, _ => absurd hq (Nat.not_lt_zero _)
  | x :: l, da, h, q, hq, r, hr => by
    have hx := h x (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    cases q with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    | succ q =>
      simp only [List.getD_cons_succ, List.length_cons] at hq ⊢
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hx, Nat.succ_mul]; omega), hx,
        show (q + 1) * k + r - k = q * k + r by rw [Nat.succ_mul]; omega, ← List.getD_eq_getElem?_getD]
      exact getD_flatMap_const f k d l da (fun y hy => h y (List.mem_cons_of_mem _ hy)) q (by omega) r hr

theorem combRow_length {row : List (Spec.X25519.Fe × Spec.X25519.Fe × Spec.X25519.Fe)}
    (h : row ∈ combTable) : row.length = 16 :=
  beq_iff_eq.mp (List.all_eq_true.mp tables_length.2 _ h)

theorem combTblWords_length : combTblWords.length = 4992 := by
  rw [combTblWords, length_flatMap_const _ 192 _ (fun row hrow => by
    rw [length_flatMap_const _ 12 _ (fun e _ => entryWords_length e), combRow_length hrow]),
    tables_length.1]

theorem combMagWords_length : combMagWords.length = 64 := by
  rw [combMagWords, length_flatMap_const _ 4 _ (fun _ _ => List.length_replicate ..), List.length_range]

theorem combWords_length : combWords.length = combWordCount := by
  rw [combWords, List.length_append, combTblWords_length, combMagWords_length]
  rfl

/-- Word `k < 4` of the magnitude `m` (from 1), after the tables: `m` in both doublewords. -/
theorem combWords_mag {m k : Nat} (hm1 : 1 ≤ m) (hm : m ≤ 16) (hk : k < 4) :
    combWords.getD (4992 + (4 * (m - 1) + k)) 0 = BitVec.ofNat 32 m ++ BitVec.ofNat 32 m := by
  rw [combWords, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [combTblWords_length]; omega),
    combTblWords_length, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD, Nat.mul_comm,
    combMagWords, getD_flatMap_const _ 4 0 _ 0 (fun _ _ => List.length_replicate ..) (m - 1)
      (by rw [List.length_range]; omega) k hk,
    show (List.range 16).getD (m - 1) 0 = m - 1 by
      rw [List.getD_eq_getElem?_getD, List.getElem?_range (by omega), Option.getD_some],
    Nat.sub_add_cancel hm1, List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hk, Option.getD_some]

/-- Word `i < 12` of entry `k < 16` of table `j < 26`. -/
theorem combWords_getD {j k i : Nat} (hj : j < 26) (hk : k < 16) (hi : i < 12) :
    combWords.getD (j * 192 + (k * 12 + i)) 0 =
      (entryWords ((combTable.getD j []).getD k (1, 1, 0))).getD i 0 := by
  have hrow : (combTable.getD j []) ∈ combTable := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tables_length.1]; exact hj)]
    exact List.getElem_mem _
  rw [combWords, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [combTblWords_length]; omega),
    ← List.getD_eq_getElem?_getD, combTblWords, getD_flatMap_const _ 192 0 combTable [] (fun row hrow => by
      rw [length_flatMap_const _ 12 _ (fun e _ => entryWords_length e), combRow_length hrow])
      j (by rw [tables_length.1]; exact hj) _ (by omega),
    getD_flatMap_const _ 12 0 _ (1, 1, 0) (fun e _ => entryWords_length e) k
      (by rw [combRow_length hrow]; exact hk) i hi]

theorem feWords_getD (v : Spec.X25519.Fe) {w : Nat} (hw : w < 4) : (feWords v).getD w 0 = feWord v w := by
  simp only [feWords, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw,
    Option.map_some, Option.getD_some]

theorem entryWords_getD (e : Spec.X25519.Fe × Spec.X25519.Fe × Spec.X25519.Fe) (f w : Nat) (hf : f < 3)
    (hw : w < 4) : (entryWords e).getD (4 * f + w) 0 =
      feWord ([e.1, e.2.1, e.2.2].getD f 0) w := by
  have hl : ∀ v, (feWords v).length = 4 := fun v => by simp [feWords]
  unfold entryWords
  rw [List.getD_eq_getElem?_getD]
  obtain rfl | rfl | rfl : f = 0 ∨ f = 1 ∨ f = 2 := by omega
  · rw [List.append_assoc, List.getElem?_append_left (by rw [hl]; omega), ← List.getD_eq_getElem?_getD,
      show 4 * 0 + w = w by omega, feWords_getD _ hw]
    try rfl
  · rw [List.append_assoc, List.getElem?_append_right (by rw [hl]; omega), hl,
      List.getElem?_append_left (by rw [hl]; omega), show 4 * 1 + w - 4 = w by omega,
      ← List.getD_eq_getElem?_getD, feWords_getD _ hw]
    try rfl
  · rw [List.getElem?_append_right (by simp [hl]), List.length_append, hl, hl,
      show 4 * 2 + w - (4 + 4) = w by omega, ← List.getD_eq_getElem?_getD, feWords_getD _ hw]
    try rfl

theorem feWord_val (v : Spec.X25519.Fe) :
    val4 (feWord v 0) (feWord v 1) (feWord v 2) (feWord v 3) = v.val := by
  simp only [feWord, Nat.mul_zero, pow_zero, Nat.div_one, Nat.reduceMul]
  exact limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega)

/-- The tables at `T`, the static's address: readable, and word `i` of
`combWords` at `T + 8 i`. -/
structure CombTbl (s : State) (T : Addr) : Prop where
  sym : s.syms combSym = T
  rd : InRegions (s.rd ++ s.wr) T (8 * combWordCount)
  val : ∀ i < combWordCount, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0

/-! ## Masks and pieces -/

/-- Runs a block by symbolic execution, reading registers through the writes. -/
syntax "erun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| erun) => `(tactic| erun [])
  | `(tactic| erun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
        execShift, execMul, State.setReg32, State.load8, State.ea, Option.bind_some,
        Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags,
        RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_arithFlags,
        RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setFlags,
        RegUpd.rd_setFlags, RegUpd.wr_setFlags, ite_true, ite_false, reduceCtorEq, Nat.le_refl,
        true_and, and_true, and_self, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte,
        Option.some.injEq, exists_eq_left', $ls,*]))

/-- All ones if `b`, else zero. -/
abbrev cmask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

/-- All ones in both quadwords if `b`, else zero. -/
abbrev cmask128 (b : Bool) : BitVec 128 := if b then BitVec.allOnes 128 else 0

theorem imm32_ofNat {v : Nat} (hv : v < 2 ^ 31) :
    (BitVec.ofNat 32 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : v < 2 ^ 32), Nat.mod_eq_of_lt (by omega : v < 2 ^ 64)]

/-- `rcx` all ones if `r8 = a` is `v`, else zero. -/
theorem combEqMask_ok (s : State) {v a : Nat} (hv : v < 2 ^ 31) (ha : a < 2 ^ 31)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block (combEqMask v)) s fun t => t.gpr .rcx = cmask (decide (a = v)) ∧ Keeps [.rcx] s t ∧
      t.xmm = s.xmm ∧ t.syms = s.syms := by
  erun [combEqMask, imm32_ofNat hv, h8, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  · have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
    have hx : decide ((BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 a).toNat < 1) = decide (a = v) := by
      refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
      · have e0 : BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 a = 0 :=
          BitVec.eq_of_toNat_eq ((Nat.lt_one_iff.mp h).trans rfl)
        have e := BitVec.xor_eq_zero_iff.mp e0
        have := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at this
        omega
      · subst h; rw [BitVec.xor_self, BitVec.toNat_zero]; decide
    rw [BitVec.sub_self, h1, hx]
    cases decide (a = v) <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem dup_cmask (b : Bool) :
    XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ cmask b) ((0 : BitVec 64) ++ cmask b) = cmask128 b := by
  cases b <;> rfl

theorem combAcc_ne : ∀ c < 6, combAcc c ≠ .xmm14 ∧ combAcc c ≠ .xmm15 := by decide

theorem combAcc_inj : ∀ c < 6, ∀ d < 6, combAcc c = combAcc d → c = d := by decide

theorem ea_combTblAt (s : State) (d : Nat) : s.ea (combTblAt d) = s.gpr .rdx + BitVec.ofNat 64 d := by
  simp only [State.ea, combTblAt, BitVec.ofInt_natCast]

/-- What the selection leaves of the other registers: the general-purpose
registers but `rs`, the memory and the regions, and the `xmm` registers but
those of `xs`. -/
structure XKeep (rs : List Reg) (xs : XReg → Prop) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  xmm : ∀ r, ¬ xs r → t.xmm r = s.xmm r
  syms : t.syms = s.syms

theorem XKeep.refl (rs : List Reg) (xs : XReg → Prop) (s : State) : XKeep rs xs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩

theorem XKeep.trans {rs : List Reg} {xs : XReg → Prop} {s₁ s₂ s₃ : State} (h₁ : XKeep rs xs s₁ s₂)
    (h₂ : XKeep rs xs s₂ s₃) : XKeep rs xs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, fun r hr => (h₂.xmm r hr).trans (h₁.xmm r hr), h₂.syms.trans h₁.syms⟩

theorem XKeep.mono {rs rs' : List Reg} {xs xs' : XReg → Prop} {s t : State} (h : XKeep rs xs s t)
    (hr : ∀ r ∈ rs, r ∈ rs') (hx : ∀ r, xs r → xs' r) : XKeep rs' xs' s t :=
  ⟨fun r h' => h.gpr r fun h'' => h' (hr r h''), h.mem, h.rd, h.wr,
    fun r h' => h.xmm r fun h'' => h' (hx r h''), h.syms⟩

/-- Piece `c` of the 16 bytes at `rdx + d`, kept under the mask `xmm15` in accumulator `c`. -/
theorem combSelStep_ok (s : State) {X : Addr} (hx : s.gpr .rdx = X) {d c : Nat} (hc : c < 6)
    (hr : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 d) 16) :
    WP isa (.block [.movdquLoad .xmm14 (combTblAt d), .xop (.bin .pand .xmm14 .xmm15),
        .xop (.bin .por (combAcc c) .xmm14)]) s fun t =>
      t.xmm (combAcc c) = s.xmm (combAcc c) ||| (s.mem.readW (X + BitVec.ofNat 64 d) 128 &&& s.xmm .xmm15) ∧
      XKeep [] (fun r => r = combAcc c ∨ r = .xmm14) s t := by
  have h14 := (combAcc_ne c hc).1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_combTblAt, hx, State.load128, hr,
    ite_true, Option.map_some, XOp.exec, XBinOp.eval, RegUpd.xmm_setXmm_self,
    RegUpd.xmm_setXmm_of_ne _ _ h14, Option.some.injEq,
    exists_eq_left', RegUpd.xmm_setXmm_of_ne _ _ (show XReg.xmm15 ≠ XReg.xmm14 from by decide)]
  refine ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl, fun r hr => ?_, rfl⟩
  simp only [not_or] at hr
  rw [RegUpd.xmm_setXmm_of_ne _ _ hr.1, RegUpd.xmm_setXmm_of_ne _ _ hr.2, RegUpd.xmm_setXmm_of_ne _ _ hr.2]

/-- The pieces `c < k` of entry `m` of the table at `rdx = X` kept under the
mask `xmm15` in their accumulators. -/
theorem combSelSteps_ok {m : Nat} {X : Addr} : ∀ k ≤ 6, ∀ (s : State), s.gpr .rdx = X →
    (∀ c < 6, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 16 * c)) 16) →
    WP isa (.block ((List.range k).flatMap fun c =>
        [.movdquLoad .xmm14 (combTblAt (combEntryBytes * (m - 1) + 16 * c)), .xop (.bin .pand .xmm14 .xmm15),
          .xop (.bin .por (combAcc c) .xmm14)])) s fun t =>
      (∀ c < 6, t.xmm (combAcc c) = if c < k then s.xmm (combAcc c) |||
          (s.mem.readW (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 16 * c)) 128 &&& s.xmm .xmm15)
        else s.xmm (combAcc c)) ∧
      XKeep [] (fun r => (∃ c < 6, r = combAcc c) ∨ r = .xmm14) s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun c _ => by simp, XKeep.refl _ _ _⟩
  | k + 1, hk, s, hx, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (combSelSteps_ok k (by omega) s hx hr) fun s₁ ⟨a₁, k₁⟩ => ?_
    have h15 : s₁.xmm .xmm15 = s.xmm .xmm15 := k₁.xmm _ (by
      rintro (⟨c, hc, h⟩ | h)
      · exact (combAcc_ne c hc).2 h.symm
      · exact absurd h (by decide))
    refine WP.mono (combSelStep_ok s₁ ((k₁.gpr _ (List.not_mem_nil)).trans hx) (c := k) (by omega)
      (by rw [k₁.rd, k₁.wr]; exact hr k (by omega))) fun t ⟨a₂, k₂⟩ => ⟨fun c hc => ?_, ?_⟩
    · by_cases hck : c = k
      · subst hck
        rw [a₂, a₁ c hc, h15, k₁.mem]
        simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]
      · rw [k₂.xmm _ (by
          rintro (h | h)
          · exact hck (combAcc_inj c hc k (by omega) h)
          · exact (combAcc_ne c hc).1 h), a₁ c hc]
        by_cases hlt : c < k
        · simp only [hlt, show c < k + 1 by omega, ↓reduceIte]
        · simp only [hlt, show ¬ c < k + 1 by omega, ↓reduceIte]
    · exact k₁.trans (k₂.mono (fun _ h => h) fun r h => by
        rcases h with h | h
        · exact Or.inl ⟨k, by omega, h⟩
        · exact Or.inr h)

/-- `xmm15` = the mask `rcx` in both quadwords. -/
theorem combDupMask_ok (s : State) {b : Bool} (hc : s.gpr .rcx = cmask b) :
    WP isa (.block [.xop (.movq .xmm15 .rcx), .xop (.bin .punpcklqdq .xmm15 .xmm15)]) s fun t =>
      t.xmm .xmm15 = cmask128 b ∧ XKeep [] (· = .xmm15) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, RegUpd.xmm_setXmm_self, hc,
    dup_cmask, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun _ _ => rfl, rfl, rfl, rfl, fun r hr => by
    rw [RegUpd.xmm_setXmm_of_ne _ _ hr, RegUpd.xmm_setXmm_of_ne _ _ hr], rfl⟩

/-- Accumulator `c` after the entries `1 … m` for the magnitude `a`: piece
`c` of entry `a` of the table at `X` if `1 ≤ a ≤ m`, else zero. -/
def accVal (mem : Mem) (X : Addr) (a m c : Nat) : BitVec 128 :=
  if 1 ≤ a ∧ a ≤ m then mem.readW (X + BitVec.ofNat 64 (combEntryBytes * (a - 1) + 16 * c)) 128 else 0

theorem accVal_step (mem : Mem) (X : Addr) (a m c : Nat) (hm : 1 ≤ m) :
    accVal mem X a (m - 1) c |||
      (mem.readW (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 16 * c)) 128 &&& cmask128 (decide (a = m))) =
      accVal mem X a m c := by
  unfold accVal
  by_cases h : a = m
  · subst h
    rw [decide_eq_true rfl, show cmask128 true = BitVec.allOnes 128 from rfl, BitVec.and_allOnes,
      ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
      ite_eq_left_of_eq_true _ _ (eq_true ⟨hm, Nat.le_refl _⟩)]
    simp
  · rw [decide_eq_false h, show cmask128 false = 0 from rfl]
    have e : ∀ x y : BitVec 128, x ||| (y &&& 0) = x := fun x y => by simp
    rw [e]
    by_cases h' : 1 ≤ a ∧ a ≤ m - 1
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h'), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h'), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- Entry `m` of the table at `rdx = X` kept in the accumulators under the
mask of `r8 = a`. -/
theorem combSelEntry_ok {s : State} {X : Addr} {a m : Nat} (hm1 : 1 ≤ m)
    (hm : m < 2 ^ 31) (ha : a < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hx : s.gpr .rdx = X)
    (hr : ∀ c < 6, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * (m - 1) + 16 * c)) 16)
    (hacc : ∀ c < 6, s.xmm (combAcc c) = accVal s.mem X a (m - 1) c) :
    WP isa (.block (combSelEntry m)) s fun t =>
      (∀ c < 6, t.xmm (combAcc c) = accVal s.mem X a m c) ∧
      XKeep [.rcx] (fun r => (∃ c < 6, r = combAcc c) ∨ r = .xmm14 ∨ r = .xmm15) s t := by
  rw [combSelEntry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (combEqMask_ok s hm ha h8) fun s₁ ⟨c₁, k₁, x₁, y₁⟩ => ?_
  refine WP.mono (combDupMask_ok s₁ c₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hx₂ : s₂.gpr .rdx = X := by rw [k₂.gpr _ List.not_mem_nil, k₁.1 _ (by decide), hx]
  have hm₂ : s₂.mem = s.mem := k₂.mem.trans k₁.2.1
  refine WP.mono (combSelSteps_ok 6 (Nat.le_refl _) s₂ hx₂ (by
      rw [k₂.rd, k₂.wr, k₁.2.2.1, k₁.2.2.2]; exact hr)) fun t ⟨a₃, k₃⟩ => ⟨fun c hc => ?_, ?_⟩
  · rw [a₃ c (by omega), ite_eq_left_of_eq_true _ _ (eq_true hc), x₂, hm₂,
      k₂.xmm _ (fun h => (combAcc_ne c (by omega)).2 h), x₁, hacc c hc]
    exact accVal_step _ _ _ _ _ hm1
  · refine ⟨fun r hr => ?_, k₃.mem.trans hm₂, by rw [k₃.rd, k₂.rd, k₁.2.2.1],
      by rw [k₃.wr, k₂.wr, k₁.2.2.2], fun r hr => ?_, by rw [k₃.syms, k₂.syms, y₁]⟩
    · rw [k₃.gpr r List.not_mem_nil, k₂.gpr r List.not_mem_nil, k₁.1 r hr]
    · simp only [not_or] at hr
      rw [k₃.xmm r (by rintro (h | h); exacts [hr.1 h, hr.2.1 h]), k₂.xmm r hr.2.2, x₁]

/-- The entries `1 … h` of the table at `rdx = X` kept in the cleared
accumulators under the masks of `r8 = a`. -/
theorem combSelEntries_ok {X : Addr} {a : Nat} (ha : a < 2 ^ 31) :
    ∀ h, h < 2 ^ 31 → ∀ (s : State), s.gpr .r8 = BitVec.ofNat 64 a → s.gpr .rdx = X →
    (∀ e < h, ∀ c < 6, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * e + 16 * c)) 16) →
    (∀ c < 6, s.xmm (combAcc c) = 0) →
    WP isa (.block ((List.range h).flatMap fun m => combSelEntry (m + 1))) s fun t =>
      (∀ c < 6, t.xmm (combAcc c) = accVal s.mem X a h c) ∧
      XKeep [.rcx] (fun r => (∃ c < 6, r = combAcc c) ∨ r = .xmm14 ∨ r = .xmm15) s t
  | 0, _, s, _, _, _, h0 => WP.block_nil ⟨fun c hc => by
      rw [h0 c hc, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega))], XKeep.refl _ _ _⟩
  | h + 1, hh, s, h8, hx, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (combSelEntries_ok ha h (by omega) s h8 hx (fun e he => hr e (by omega)) h0)
      fun s₁ ⟨a₁, k₁⟩ => ?_
    refine WP.mono (combSelEntry_ok (X := X) (m := h + 1) (by omega) hh ha
      (by rw [k₁.gpr _ (by decide), h8]) (by rw [k₁.gpr _ (by decide), hx])
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr h (by omega) c hc)
      (fun c hc => by rw [a₁ c hc, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, k₂⟩ =>
      ⟨fun c hc => by rw [a₂ c hc, k₁.mem], k₁.trans k₂⟩

/-- The accumulators `c < k` cleared. -/
theorem combClearAcc_ok : ∀ k ≤ 6, ∀ (s : State),
    WP isa (.block ((List.range k).map fun c => .xop (.bin .pxor (combAcc c) (combAcc c)))) s fun t =>
      (∀ c < k, t.xmm (combAcc c) = 0) ∧ XKeep [] (fun r => ∃ c < k, r = combAcc c) s t
  | 0, _, s => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), XKeep.refl _ _ _⟩
  | k + 1, hk, s => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (combClearAcc_ok k (by omega) s) fun s₁ ⟨a₁, k₁⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, XBinOp.eval, BitVec.xor_self,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun c hc => ?_, ⟨fun r hr => k₁.gpr r hr, k₁.mem, k₁.rd, k₁.wr, fun r hr => ?_, k₁.syms⟩⟩
    · by_cases hck : c = k
      · subst hck; exact RegUpd.xmm_setXmm_self _ _ _
      · rw [RegUpd.xmm_setXmm_of_ne _ _ fun h => hck (combAcc_inj c (by omega) k (by omega) h),
          a₁ c (by omega)]
    · rw [RegUpd.xmm_setXmm_of_ne _ _ fun h => hr ⟨k, by omega, h⟩,
        k₁.xmm r fun ⟨c, hc, h⟩ => hr ⟨c, by omega, h⟩]

/-- A 16-byte write changes only its bytes. -/
theorem writeW128_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 128) (h : d + 16 ≤ 2 ^ 64) :
    Outside base d 16 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

/-- 16 bytes outside the bytes that changed. -/
theorem outside_read128 {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 16 ≤ o ∨ o + n ≤ d) (hd' : d + 16 ≤ 2 ^ 64) :
    m'.readW (off base d) 128 = m.readW (off base d) 128 :=
  (Mem.readW_congr fun i hi => (h _ (by rw [Proof.X25519.X86_64.ofs_off base (by omega)]; omega)).symm).symm

/-- The accumulators `c < k` stored to the 16 bytes at `o + 16 c`. -/
theorem combStoreAcc_ok {base : Addr} {o : Nat} : ∀ k, ∀ (s : State), Scratch s base → o + 16 * k ≤ 8192 →
    WP isa (.block ((List.range k).map fun c => .movdquStore (Impl.X25519.X86_64.sc (o + 16 * c)) (combAcc c)))
      s fun t =>
      (∀ c < k, t.mem.readW (off base (o + 16 * c)) 128 = s.xmm (combAcc c)) ∧
      Outside base o (16 * k) s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.xmm = s.xmm ∧
      t.syms = s.syms
  | 0, s, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl,
      rfl, rfl, rfl⟩
  | k + 1, s, hs, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (combStoreAcc_ok k s hs (by omega)) fun s₁ ⟨a₁, O₁, g₁, r₁, w₁, x₁, y₁⟩ => ?_
    have hw : InRegions s₁.wr (off base (o + 16 * k)) 16 := by
      rw [w₁]; exact ⟨_, hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
    have hd₁ : s₁.gpr .rdi = base := by rw [g₁]; exact hs.rdi
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Proof.X25519.X86_64.ea_sc, hd₁,
      State.store128, hw, ite_true, Option.some.injEq, exists_eq_left']
    have O₂ := writeW128_outside s₁.mem base (s₁.xmm (combAcc k)) (d := o + 16 * k) (by omega)
    refine ⟨fun c hc => ?_, (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)),
      g₁, r₁, w₁, x₁, y₁⟩
    by_cases hck : c = k
    · subst hck
      rw [x₁]; exact Mem.readW_writeW_self (n := 16) _ _ _ (by decide)
    · rw [outside_read128 O₂ (by omega) (by omega), a₁ c (by omega)]

/-- `rdx` = the address of table `rdx = j`, `T + tb j` for the static `sym` at `T`, through
`rax` and `rcx`. -/
theorem tblSetup_ok (s : State) {j tb : Nat} {T : Addr} (sym : String) (htb : tb < 2 ^ 31)
    (hd : s.gpr .rdx = BitVec.ofNat 64 j) (hT : s.syms sym = T) :
    WP isa (.block [.mov .rax (.reg .rdx), .mov32 .rcx (.imm (BitVec.ofNat 32 tb)), .mul .rcx,
      .leaSym .rdx sym, .alu .add .rdx (.reg .rax)]) s fun t =>
      t.gpr .rdx = T + BitVec.ofNat 64 (j * tb) ∧
      Keeps [.rax, .rcx, .rdx] s t ∧ t.xmm = s.xmm ∧ t.syms = s.syms := by
  subst hT
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    execAlu, execMul, State.setReg32, imm32_ofNat htb, hd,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, Option.map_some, Option.bind_some,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show tb < 2 ^ 64 by omega), Nat.mod_mul_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2,
      ite_false]

/-- `rdx` = the address of table `rdx = j`, `T + 768 j`, through `rax` and `rcx`. -/
theorem combSelSetup_ok (s : State) {j : Nat} {T : Addr} (hd : s.gpr .rdx = BitVec.ofNat 64 j)
    (hT : s.syms combSym = T) :
    WP isa (.block combSelSetup) s fun t => t.gpr .rdx = T + BitVec.ofNat 64 (j * combTblBytes) ∧
      Keeps [.rax, .rcx, .rdx] s t ∧ t.xmm = s.xmm ∧ t.syms = s.syms :=
  tblSetup_ok s combSym (by decide) hd hT

/-- The accumulators cleared, entries `1 … 16` of the table at `rdx = X` kept
under the masks of `r8 = a`, and stored to slots 4–6. -/
theorem combSelPass_ok {s : State} {base : Addr} (hs : Scratch s base) {X : Addr} {a : Nat}
    (ha : a < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hx : s.gpr .rdx = X)
    (hr : ∀ e < 16, ∀ c < 6, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (combEntryBytes * e + 16 * c)) 16) :
    WP isa (.block combSelPass) s fun t =>
      (∀ c < 6, t.mem.readW (off base (offset 4 + 16 * c)) 128 = accVal s.mem X a 16 c) ∧
      Outside base (offset 4) 96 s.mem t.mem ∧ (∀ r, r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.syms = s.syms := by
  unfold combSelPass
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (combClearAcc_ok 6 (Nat.le_refl _) s) fun s₁ ⟨a₁, k₁⟩ => ?_
  refine WP.mono (combSelEntries_ok (X := X) ha 16 (by decide) s₁ (by rw [k₁.gpr _ List.not_mem_nil, h8])
    (by rw [k₁.gpr _ List.not_mem_nil, hx]) (by rw [k₁.rd, k₁.wr]; exact hr) a₁) fun s₂ ⟨a₂, k₂⟩ => ?_
  have hs₂ : Scratch s₂ base :=
    ⟨by rw [k₂.gpr _ (by decide), k₁.gpr _ List.not_mem_nil, hs.rdi], by rw [k₂.wr, k₁.wr]; exact hs.wr,
      hs.nowrap⟩
  refine WP.mono (combStoreAcc_ok (o := offset 4) 6 s₂ hs₂ (by decide)) fun t ⟨a₃, O₃, g₃, r₃, w₃, _, y₃⟩ =>
    ⟨fun c hc => by rw [a₃ c hc, a₂ c hc, k₁.mem], by rw [k₂.mem, k₁.mem] at O₃; exact O₃,
      fun r hr => by rw [g₃, k₂.gpr r (by simpa using hr), k₁.gpr r List.not_mem_nil],
      by rw [r₃, k₂.rd, k₁.rd], by rw [w₃, k₂.wr, k₁.wr], by rw [y₃, k₂.syms, k₁.syms]⟩

/-- The words the selection stores: those of entry `a` of the table at `X`
if `1 ≤ a ≤ 16`, else zero. -/
theorem accVal_word {mem mem' : Mem} {base X : Addr} {a o : Nat}
    (h : ∀ c < 6, mem'.readW (off base (o + 16 * c)) 128 = accVal mem X a 16 c) :
    ∀ i < 12, Proof.X25519.X86_64.word mem' base (o + 8 * i) =
      if 1 ≤ a ∧ a ≤ 16 then Proof.X25519.X86_64.word mem X (combEntryBytes * (a - 1) + 8 * i) else 0 := by
  intro i hi
  obtain ⟨c, q, hq, rfl⟩ : ∃ c q, q < 2 ∧ i = 2 * c + q :=
    ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by omega⟩
  have e := readW_extract mem' (off base (o + 16 * c)) (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * 8 = 64 from rfl, off, Offset.add_add, show o + 16 * c + 8 * q = o + 8 * (2 * c + q) by omega] at e
  rw [Proof.X25519.X86_64.word, off, ← e, h c (by omega), accVal]
  split
  · have e2 := readW_extract mem (X + BitVec.ofNat 64 (combEntryBytes * (a - 1) + 16 * c)) (w := 128)
      (k := 8 * q) (n := 8) (by omega)
    rw [show 8 * 8 = 64 from rfl, Offset.add_add] at e2
    rw [e2, Proof.X25519.X86_64.word, off]
    rw [show combEntryBytes * (a - 1) + 16 * c + 8 * q = combEntryBytes * (a - 1) + 8 * (2 * c + q) by omega]
  · simp

/-- Word `i < 12` of entry `a` (from 1) of table `j`, in the memory holding the tables at `T`. -/
theorem combTbl_word {s : State} {T : Addr} (ht : CombTbl s T) {j a i : Nat} (hj : j < 26) (ha1 : 1 ≤ a)
    (ha : a ≤ 16) (hi : i < 12) :
    Proof.X25519.X86_64.word s.mem (T + BitVec.ofNat 64 (j * combTblBytes)) (combEntryBytes * (a - 1) + 8 * i) =
      (entryWords ((combTable.getD j []).getD (a - 1) (1, 1, 0))).getD i 0 := by
  rw [← combWords_getD hj (by omega) hi, ← ht.val _ (by simp only [combWordCount]; omega),
    Proof.X25519.X86_64.word, off,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  congr 2
  simp only [combTblBytes, combEntryBytes]
  grind

/-- The identity's `Y - X = Y + X = 1` for a zero magnitude `r8 = a`. -/
theorem combSelOne_ok {s : State} {base : Addr} (hs : Scratch s base) {a : Nat} (ha : a < 2 ^ 64)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block combSelOne) s fun t =>
      t.mem = (s.mem.writeW (off base (offset 4))
          (Proof.X25519.X86_64.word s.mem base (offset 4) ||| (if a = 0 then 1 else 0))).writeW
        (off base (offset 5)) (Proof.X25519.X86_64.word s.mem base (offset 5) ||| (if a = 0 then 1 else 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.syms = s.syms := by
  have hw : ∀ d, d + 8 ≤ 8192 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, Offset.contains_base _ hd (by omega)⟩
  have hr : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ hd (by omega)⟩
  have hM : (BitVec.ofNat 64 a - BitVec.ofNat 64 a - BitVec.setWidth 64 (BitVec.ofBool
      (decide ((BitVec.ofNat 64 a).toNat < (BitVec.signExtend 64 (1 : BitVec 32)).toNat)))) &&&
      BitVec.signExtend 64 (1 : BitVec 32) = if a = 0 then 1 else 0 := by
    by_cases h : a = 0
    · subst h; decide
    · have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
      rw [h1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, decide_eq_false (by omega),
        ite_eq_right_iff.mpr (fun h2 => absurd h2 h)]
      simp
  erun [combSelOne, State.load64, State.store64, Impl.X25519.X86_64.sc, Impl.X25519.X86_64.at_,
    BitVec.ofInt_natCast, hs.rdi, h8,
    hw _ (show offset 4 + 8 ≤ 8192 by decide), hr _ (show offset 4 + 8 ≤ 8192 by decide),
    hw _ (show offset 5 + 8 ≤ 8192 by decide), hr _ (show offset 5 + 8 ≤ 8192 by decide), hM]
  constructor
  · rw [Mem.readW_writeW_sep (Proof.X25519.X86_64.sep_off base (by decide) (by decide) (by decide)) (by decide)]
  · repeat' constructor
    all_goals first | rfl | (intro r h1 h2; simp only [h1, h2, ite_false])

/-- The fields `Y - X`, `Y + X` and `2dT` of entry `a` of table `j`. -/
abbrev combField (j a f : Nat) : Spec.X25519.Fe :=
  [(combCached j a).X, (combCached j a).Y, (combCached j a).Z].getD f 0

/-- A field element from its words. -/
theorem F_of_words {m : Mem} {base : Addr} {o : Nat} {v : Spec.X25519.Fe}
    (h : ∀ w < 4, Proof.X25519.X86_64.word m base (o + 8 * w) = feWord v w) : F m base o = v := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1 h2 h3
  simp only [F, Proof.X25519.X86_64.fe, h0, h1, show o + 16 = o + 8 * 2 from rfl, h2,
    show o + 24 = o + 8 * 3 from rfl, h3, feWord_val, Proof.X25519.toFe_self]

private theorem ones_words : ∀ f < 3, ∀ w < 4, (if 4 * f + w = 0 ∨ 4 * f + w = 4 then (1 : BitVec 64) else 0) =
    feWord ([(1 : Spec.X25519.Fe), 1, 0].getD f 0) w := by decide

theorem combCached_succ (j a : Nat) (ha : 1 ≤ a) :
    combCached j a = ⟨((combTable.getD j []).getD (a - 1) (1, 1, 0)).1,
      ((combTable.getD j []).getD (a - 1) (1, 1, 0)).2.1, ((combTable.getD j []).getD (a - 1) (1, 1, 0)).2.2, 2⟩ := by
  simp only [combCached, show a ≠ 0 by omega, ↓reduceIte]

/-- After a pass leaving entry `a`'s words (or zero) in slots 4–6: the identity's ones for a zero
magnitude (`combSelOne`), and the slots are `combField j a`. -/
theorem combSelOne_slots {s₂ : State} {base : Addr} (hs₂ : Scratch s₂ base) {j a : Nat} (ha : a ≤ 16)
    (h8₂ : s₂.gpr .r8 = BitVec.ofNat 64 a)
    (hw₂ : ∀ i < 12, Proof.X25519.X86_64.word s₂.mem base (offset 4 + 8 * i) =
      if 1 ≤ a then (entryWords ((combTable.getD j []).getD (a - 1) (1, 1, 0))).getD i 0 else 0) :
    WP isa (.block combSelOne) s₂ fun t =>
      (∀ f < 3, F t.mem base (offset 4 + 32 * f) = combField j a f) ∧
      Outside base (offset 4) 96 s₂.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s₂.gpr r) ∧ t.rd = s₂.rd ∧ t.wr = s₂.wr ∧
      t.syms = s₂.syms := by
  have hnw := hs₂.nowrap
  refine WP.mono (combSelOne_ok hs₂ (by omega) h8₂) fun t ⟨mt, gt, rt, wt, yt⟩ => ?_
  -- After the identity's ones.
  have hwt : ∀ i < 12, Proof.X25519.X86_64.word t.mem base (offset 4 + 8 * i) =
      if 1 ≤ a then (entryWords ((combTable.getD j []).getD (a - 1) (1, 1, 0))).getD i 0 else
        if i = 0 ∨ i = 4 then 1 else 0 := by
    intro i hi
    have e0 : ∀ x : BitVec 64, x ||| 0 = x := fun x => by simp
    have e1 : (0 : BitVec 64) ||| 1 = 1 := by decide
    rw [mt]
    by_cases h4 : i = 4
    · subst h4
      rw [Proof.X25519.X86_64.word, show offset 4 + 8 * 4 = offset 5 from rfl, Mem.readW_writeW_self64,
        show offset 5 = offset 4 + 8 * 4 from rfl, hw₂ 4 (by decide)]
      by_cases h1 : 1 ≤ a
      · simp only [h1, ↓reduceIte, show a ≠ 0 by omega, e0]
      · obtain rfl : a = 0 := by omega
        simp only [show ¬ 1 ≤ 0 from by decide, ↓reduceIte, e1, or_true]
    · rw [Proof.X25519.X86_64.word, Mem.readW_writeW_sep
        (Proof.X25519.X86_64.sep_off base (by simp only [offset] at *; omega) (by simp only [offset]; omega)
          (by simp only [offset]; omega)) (by decide)]
      by_cases h0 : i = 0
      · subst h0
        rw [show offset 4 + 8 * 0 = offset 4 from rfl, Mem.readW_writeW_self64,
          show offset 4 = offset 4 + 8 * 0 from rfl, hw₂ 0 (by decide)]
        by_cases h1 : 1 ≤ a
        · simp only [h1, ↓reduceIte, show a ≠ 0 by omega, e0]
        · obtain rfl : a = 0 := by omega
          simp only [show ¬ 1 ≤ 0 from by decide, ↓reduceIte, e1, true_or]
      · rw [Mem.readW_writeW_sep
          (Proof.X25519.X86_64.sep_off base (by simp only [offset] at *; omega) (by simp only [offset]; omega)
            (by simp only [offset]; omega)) (by decide), ← Proof.X25519.X86_64.word, hw₂ i hi]
        by_cases h1 : 1 ≤ a
        · simp only [h1, ↓reduceIte]
        · simp only [h1, ↓reduceIte, h0, h4, or_self]
          done
  refine ⟨fun f hf => F_of_words fun w hw => ?_, ?_, gt, rt, wt, yt⟩
  · rw [show offset 4 + 32 * f + 8 * w = offset 4 + 8 * (4 * f + w) by omega, hwt _ (by omega)]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), entryWords_getD _ f w hf hw, combField, combCached_succ j a h1]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), combField,
        show combCached j a = ⟨1, 1, 0, 2⟩ by simp only [combCached, show a = 0 by omega, ↓reduceIte]]
      exact ones_words f hf w hw
  · rw [mt]
    exact ((Proof.X25519.X86_64.writeW_outside _ base _ (d := offset 4) (by decide)).mono
      (by decide) (by decide)).trans
      ((Proof.X25519.X86_64.writeW_outside _ base _ (d := offset 5) (by decide)).mono (by decide) (by decide))

/-- The selection: entry `a ≤ 16` (`combCached`, but its `2Z`) of table `j < 26`, from the tables
at `T`, to slots 4–6. -/
theorem combSelect_ok {s : State} {base T : Addr} (hs : Scratch s base) (ht : CombTbl s T)
    {j a : Nat} (hj : j < 26) (ha : a ≤ 16) (hd : s.gpr .rdx = BitVec.ofNat 64 j)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block combSelect) s fun t =>
      (∀ f < 3, F t.mem base (offset 4 + 32 * f) = combField j a f) ∧
      Outside base (offset 4) 96 s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.syms = s.syms := by
  have hnw := hs.nowrap
  rw [combSelect, List.append_assoc, WP.block_append_iff]
  refine WP.mono (combSelSetup_ok s hd ht.sym) fun s₁ ⟨x₁, k₁, _, y₁⟩ => ?_
  rw [WP.block_append_iff]
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  have hr : ∀ e < 16, ∀ c < 6, InRegions (s₁.rd ++ s₁.wr)
      (T + BitVec.ofNat 64 (j * combTblBytes) + BitVec.ofNat 64 (combEntryBytes * e + 16 * c)) 16 := by
    intro e he c hc
    rw [k₁.2.2.1, k₁.2.2.2, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine VG.CallLay.inRegions_sub ht.rd ?_ (by decide)
    simp only [combTblBytes, combEntryBytes, combWordCount]; omega
  refine WP.mono (combSelPass_ok hs₁ (by omega) h8₁ x₁ hr) fun s₂ ⟨a₂, O₂, g₂, r₂, w₂, y₂⟩ => ?_
  have hs₂ : Scratch s₂ base := ⟨by rw [g₂ _ (by decide)]; exact hs₁.rdi, by rw [w₂]; exact hs₁.wr, hnw⟩
  have h8₂ : s₂.gpr .r8 = BitVec.ofNat 64 a := by rw [g₂ _ (by decide), h8₁]
  have W := accVal_word a₂
  rw [k₁.2.1] at W
  -- The words of slots 4–6 after the pass: entry `a`'s, or zero.
  have hw₂ : ∀ i < 12, Proof.X25519.X86_64.word s₂.mem base (offset 4 + 8 * i) =
      if 1 ≤ a then (entryWords ((combTable.getD j []).getD (a - 1) (1, 1, 0))).getD i 0 else 0 := by
    intro i hi
    rw [W i hi]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩), ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact combTbl_word ht hj h1 ha hi
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h1)]
  refine WP.mono (combSelOne_slots hs₂ ha h8₂ hw₂) fun t ⟨ft, ot, gt, rt, wt, yt⟩ =>
    ⟨ft, by rw [← k₁.2.1]; exact O₂.trans ot, fun r h1 h2 h3 => ?_, by rw [rt, r₂, k₁.2.2.1], by rw [wt, w₂, k₁.2.2.2], by rw [yt, y₂, y₁]⟩
  rw [gt r h1 h2, g₂ r h2, k₁.1 r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2, h3⟩)]

/-- What the comb needs of its selection `sel` (`combSelect_ok`'s statement): entry `a ≤ 16` of
table `j < 26` to slots 4–6, keeping the rest of the scratch and the registers but `rax`, `rcx`
and `rdx`. -/
def SelOk (sel : List Instr) : Prop :=
  ∀ {s : State} {base T : Addr}, Scratch s base → CombTbl s T → ∀ {j a : Nat}, j < 26 → a ≤ 16 →
    s.gpr .rdx = BitVec.ofNat 64 j → s.gpr .r8 = BitVec.ofNat 64 a →
    WP isa (.block sel) s fun t =>
      (∀ f < 3, F t.mem base (offset 4 + 32 * f) = combField j a f) ∧
      Outside base (offset 4) 96 s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.syms = s.syms

theorem combSelect_sel : SelOk combSelect := by
  intro _ _ _ hs ht _ _ hj ha hd h8; exact combSelect_ok hs ht hj ha hd h8

/-! ## The tables -/

/-- The tables' bytes lie past the scratch. -/
def TblFar (base T : Addr) : Prop := ∀ i < 8 * combWordCount, 8192 ≤ ofs base (T + BitVec.ofNat 64 i)

/-- The tables survive what changes only the scratch, the registers and nothing else. -/
theorem CombTbl.keep {s t : State} {base T : Addr} (h : CombTbl s T) (hf : TblFar base T)
    (hk : PowersKeep base 56 7368 s t) (hsy : t.syms = s.syms) : CombTbl t T :=
  ⟨(congrFun hsy combSym).trans h.sym, by rw [hk.rd, hk.wr]; exact h.rd, fun i hi => by
    rw [← h.val i hi]
    refine Mem.readW_congr fun b hb => hk.mem _ (Or.inr ?_) (Or.inr ?_) <;>
    · have := hf (8 * i + b) (by omega)
      rw [Offset.add_add]
      omega⟩

/-- The tables' region at `T`. -/
abbrev combRegion (T : Addr) : Region := ⟨T, 8 * combWordCount⟩

/-- What a contract with the comb's static (`Abi.withConsts combConsts`) says of its tables:
held at the static's address, not wrapping around, and apart from the regions `wr`. -/
def CombHeld (s : State) (wr : List Region) : Prop :=
  (∀ i < combWordCount, s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0) ∧
  (s.syms combSym).toNat + 8 * combWordCount ≤ 2 ^ 64 ∧ ∀ r ∈ wr, Region.Disjoint (combRegion (s.syms combSym)) r

theorem CombTbl.of_held {s : State} {wr : List Region} (hrd : combRegion (s.syms combSym) ∈ s.rd)
    (h : CombHeld s wr) : CombTbl s (s.syms combSym) :=
  ⟨rfl, ⟨_, List.mem_append_left _ hrd, Region.contains_self _ _⟩, h.1⟩

/-- The tables survive a change of memory within regions apart from them. -/
theorem CombTbl.frame {s t : State} {T : Addr} {rs : List Region} (h : CombTbl s T)
    (hf : Frame rs s.mem t.mem) (hd : ∀ r ∈ rs, (combRegion T).Disjoint r)
    (hrd : t.rd ++ t.wr = s.rd ++ s.wr) (hsy : t.syms = s.syms) : CombTbl t T :=
  ⟨by rw [hsy]; exact h.sym, by rw [hrd]; exact h.rd, fun i hi => by
    rw [hf.readW (r := combRegion T) (Offset.contains_base _ (by simp only [combWordCount] at *; omega)
      (by simp only [combWordCount] at *; omega)) hd (by decide)]
    exact h.val i hi⟩

end VG.Proof.Ed25519.X86_64
