import VerifiedGarbage.Impl.Ed448.AArch64.Scalar
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.AArch64.Chain

/-!
# Ed448 scalar arithmetic on AArch64: one word

`wordFold` turns the remainder `r < L` in `x5–x11` and the next word `w` in
`x4` into `n = l + h c` (in `N`) for `2^64 r + w = h 2^446 + l`
(`fold_words`), and `csub` reduces a value below `2L` modulo `L`. Each block
is checked against the numbers it computes, with the carry chains of
`Chain.lean`.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x const64_ok)
open VG.Spec.Ed448 (L)

/-- The remainder: the seven words of `x5–x11`. -/
abbrev rem (s : State) : Nat := rv s R

/-- The constants of `consts` in their registers. -/
structure Consts (s : State) : Prop where
  c0 : s.gpr C0 = c0
  c1 : s.gpr C1 = c1
  c2 : s.gpr C2 = c2
  c3 : s.gpr C3 = c3
  kt : s.gpr KT = 0xc000000000000000
  z : s.gpr Z = 0

/-- The registers the constants are in. -/
def constRegs : List Reg := [C0, C1, C2, C3, KT, Z]

theorem Consts.of_keeps {rs : List Reg} {s t : State} (h : Consts s) (k : Keeps rs s t)
    (hr : ∀ r ∈ constRegs, r ∉ rs) : Consts t :=
  ⟨(k.gpr _ (hr _ (by decide))).trans h.c0, (k.gpr _ (hr _ (by decide))).trans h.c1,
    (k.gpr _ (hr _ (by decide))).trans h.c2, (k.gpr _ (hr _ (by decide))).trans h.c3,
    (k.gpr _ (hr _ (by decide))).trans h.kt, (k.gpr _ (hr _ (by decide))).trans h.z⟩

/-- The registers the loop's body changes. -/
def clob : List Reg :=
  [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20]

theorem constRegs_clob : ∀ r ∈ constRegs, r ∉ clob := by decide

theorem rem_eq (s : State) : rem s = (s.gpr .x5).toNat + 2 ^ 64 * ((s.gpr .x6).toNat + 2 ^ 64 *
    ((s.gpr .x7).toNat + 2 ^ 64 * ((s.gpr .x8).toNat + 2 ^ 64 * ((s.gpr .x9).toNat + 2 ^ 64 *
    ((s.gpr .x10).toNat + 2 ^ 64 * (s.gpr .x11).toNat))))) := by
  simp only [rem, rv, R, Nat.mul_zero, Nat.add_zero]

/-! ## Folding a word in -/

theorem toNat_zero64 : (0 : BitVec 64).toNat = 0 := rfl

theorem extr62 (lo hi : BitVec 64) (h : hi.toNat < 2 ^ 62) :
    ((hi ++ lo).extractLsb' 62 64).toNat = lo.toNat / 2 ^ 62 + 4 * hi.toNat := by
  have := lo.isLt
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem shl_shr2 (x : BitVec 64) : ((x <<< 2) >>> 2).toNat = x.toNat % 2 ^ 62 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

/-- `foldSplit`: `h` into `x11`, `r₅ mod 2^62` into `x10`. -/
theorem foldSplit_ok (s : State) (h6 : (s.gpr .x11).toNat < 2 ^ 62) :
    WP isa (.block foldSplit) s fun t =>
      (t.gpr .x11).toNat = (s.gpr .x10).toNat / 2 ^ 62 + 4 * (s.gpr .x11).toNat ∧
      (t.gpr .x10).toNat = (s.gpr .x10).toNat % 2 ^ 62 ∧ Keeps [.x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [foldSplit, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 62 < Size.x.bits from by decide, show 2 < Size.x.bits from by decide,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨extr62 _ _ h6, shl_shr2 _, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem mul_halves (a b : BitVec 64) :
    (a * b).toNat + 2 ^ 64 * (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat =
      a.toNat * b.toNat := by
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' a.isLt b.isLt
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega)]
  omega

/-- `foldMul`: the products of `h` by the words of `c`. -/
theorem foldMul_ok (s : State) :
    WP isa (.block foldMul) s fun t =>
      (t.gpr .x12).toNat + 2 ^ 64 * (t.gpr .x16).toNat = (s.gpr .x11).toNat * (s.gpr C0).toNat ∧
      (t.gpr .x13).toNat + 2 ^ 64 * (t.gpr .x17).toNat = (s.gpr .x11).toNat * (s.gpr C1).toNat ∧
      (t.gpr .x14).toNat + 2 ^ 64 * (t.gpr .x19).toNat = (s.gpr .x11).toNat * (s.gpr C2).toNat ∧
      (t.gpr .x15).toNat + 2 ^ 64 * (t.gpr .x20).toNat = (s.gpr .x11).toNat * (s.gpr C3).toNat ∧
      Keeps [.x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20] s t := by
  apply WP.of_runBlock
  simp only [foldMul, C0, C1, C2, C3, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨mul_halves _ _, mul_halves _ _, mul_halves _ _, mul_halves _ _,
    ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

theorem foldProd_eq : foldProd = .adds .x .x13 .x13 .x16 ::
    adcsOf [(.x14, .x14, .x17), (.x15, .x15, .x19), (.x20, .x20, Z)] := rfl

theorem c_words : c0.toNat + 2 ^ 64 * (c1.toNat + 2 ^ 64 * (c2.toNat + 2 ^ 64 * c3.toNat)) = cL := by
  decide

/-- `foldMul` and `foldProd`: `h c` in `x12–x15`, `x20`. -/
theorem foldMul_prod_ok (s : State) (hc : Consts s) :
    WP isa (.block (foldMul ++ foldProd)) s fun t =>
      (t.gpr .x12).toNat + 2 ^ 64 * rv t [.x13, .x14, .x15, .x20] = (s.gpr .x11).toNat * cL ∧
      Keeps [.x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (foldMul_ok s) fun a ⟨e0, e1, e2, e3, ka⟩ => ?_
  rw [foldProd_eq]
  refine WP.mono (adds_ok _ _ _ _ a (by decide)) fun t ⟨et, kt⟩ => ?_
  have hz : a.gpr Z = 0 := (ka.gpr _ (by decide)).trans hc.z
  have h12 : t.gpr .x12 = a.gpr .x12 := kt.gpr _ (by decide)
  simp only [dsts, lhs, rhs, List.map_cons, List.map_nil, List.length_cons, List.length_nil, rv,
    hz, toNat_zero64, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.reduceAdd, Nat.reduceMul] at et
  simp only [rv, Nat.mul_zero, Nat.add_zero]
  rw [h12]
  rw [hc.c0, hc.c1, hc.c2, hc.c3] at *
  have hb : (s.gpr .x11).toNat * cL < 2 ^ 64 * 2 ^ 224 :=
    Nat.mul_lt_mul'' (s.gpr .x11).isLt cL_lt
  have hcL : (s.gpr .x11).toNat * cL = (s.gpr .x11).toNat * c0.toNat + 2 ^ 64 *
      ((s.gpr .x11).toNat * c1.toNat + 2 ^ 64 * ((s.gpr .x11).toNat * c2.toNat + 2 ^ 64 *
        ((s.gpr .x11).toNat * c3.toNat))) := by
    rw [← c_words]; grind
  have l3 : (a.gpr .x20).toNat < 2 ^ 32 := by
    have : (s.gpr .x11).toNat * c3.toNat < 2 ^ 64 * 2 ^ 32 :=
      Nat.mul_lt_mul'' (s.gpr .x11).isLt (by decide)
    have := (a.gpr .x15).isLt
    omega
  refine ⟨?_, (ka.mono (by decide)).trans (kt.mono (by decide))⟩
  have hc' := Bool.toNat_le t.c
  generalize (s.gpr .x11).toNat * c0.toNat = P0 at *
  generalize (s.gpr .x11).toNat * c1.toNat = P1 at *
  generalize (s.gpr .x11).toNat * c2.toNat = P2 at *
  generalize (s.gpr .x11).toNat * c3.toNat = P3 at *
  generalize (s.gpr .x11).toNat * cL = P at *
  have := (t.gpr .x13).isLt; have := (t.gpr .x14).isLt; have := (t.gpr .x15).isLt
  have := (t.gpr .x20).isLt
  omega

theorem foldAdd_eq : foldAdd = .adds .x .x4 .x4 .x12 ::
    adcsOf [(.x5, .x5, .x13), (.x6, .x6, .x14), (.x7, .x7, .x15), (.x8, .x8, .x20),
      (.x9, .x9, Z), (.x10, .x10, Z)] := rfl

/-- `foldAdd`: `x4–x10 += x12–x15, x20`, for a sum below `2^448`. -/
theorem foldAdd_ok (s : State) (hz : s.gpr Z = 0)
    (hlt : rv s N + ((s.gpr .x12).toNat + 2 ^ 64 * rv s [.x13, .x14, .x15, .x20]) < 2 ^ 448) :
    WP isa (.block foldAdd) s fun t =>
      rv t N = rv s N + ((s.gpr .x12).toNat + 2 ^ 64 * rv s [.x13, .x14, .x15, .x20]) ∧
      Keeps N s t := by
  rw [foldAdd_eq]
  refine WP.mono (adds_ok _ _ _ _ s (by decide)) fun t ⟨et, kt⟩ => ⟨?_, kt⟩
  have hc := Bool.toNat_le t.c
  simp only [dsts, lhs, rhs, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul] at et
  have hp : rv s [.x12, .x13, .x14, .x15, .x20, Z, Z] =
      (s.gpr .x12).toNat + 2 ^ 64 * rv s [.x13, .x14, .x15, .x20] := by
    simp only [rv, hz, toNat_zero64, Nat.mul_zero, Nat.add_zero]
  rw [hp] at et
  simp only [N] at hlt ⊢
  generalize rv t [.x4, .x5, .x6, .x7, .x8, .x9, .x10] = T at et ⊢
  generalize rv s [.x4, .x5, .x6, .x7, .x8, .x9, .x10] + ((s.gpr .x12).toNat + 2 ^ 64 * rv s [.x13, .x14, .x15, .x20]) = A at et hlt ⊢
  generalize (2 : Nat) ^ 448 = M at et hlt
  rcases Nat.lt_or_ge t.c.toNat 1 with h | h
  · obtain h0 : t.c.toNat = 0 := by omega
    rw [h0, Nat.mul_zero, Nat.add_zero] at et
    exact et
  · have := Nat.mul_le_mul_left M h
    omega

/-- The registers `wordFold` changes. -/
def foldClob : List Reg :=
  [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19, .x20]

/-- `wordFold`: from the remainder `r < L` and the next word `w` in `x4`, a
value below `2L` congruent to `2^64 r + w`. -/
theorem wordFold_ok (s : State) (hc : Consts s) (hr : rem s < L) :
    WP isa (.block wordFold) s fun t => rv t N < 2 * L ∧
      rv t N % L = ((s.gpr .x4).toNat + 2 ^ 64 * rem s) % L ∧ Keeps foldClob s t := by
  have hw := (s.gpr .x4).isLt
  have h0 := (s.gpr .x5).isLt; have h1 := (s.gpr .x6).isLt; have h2 := (s.gpr .x7).isLt
  have h3 := (s.gpr .x8).isLt; have h4 := (s.gpr .x9).isLt; have h5 := (s.gpr .x10).isLt
  have h6 := (s.gpr .x11).isLt
  rw [rem_eq] at hr
  obtain ⟨h6', hh, hlt, hmod⟩ := fold_words _ _ _ _ _ _ _ _ hw h0 h1 h2 h3 h4 h5 h6 hr
  simp only [wordFold, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (foldSplit_ok s h6') fun a ⟨a11, a10, ka⟩ => ?_
  have hca : Consts a := hc.of_keeps ka (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (foldMul_prod_ok a hca) fun b ⟨eb, kb⟩ => ?_
  have hcb : Consts b := hca.of_keeps kb (by decide)
  have nb : rv b N = (s.gpr .x4).toNat + 2 ^ 64 * ((s.gpr .x5).toNat + 2 ^ 64 *
      ((s.gpr .x6).toNat + 2 ^ 64 * ((s.gpr .x7).toNat + 2 ^ 64 * ((s.gpr .x8).toNat +
      2 ^ 64 * ((s.gpr .x9).toNat + 2 ^ 64 * ((s.gpr .x10).toNat % 2 ^ 62)))))) := by
    simp only [N, rv, Nat.mul_zero, Nat.add_zero]
    rw [kb.gpr .x4 (by decide), kb.gpr .x5 (by decide), kb.gpr .x6 (by decide),
      kb.gpr .x7 (by decide), kb.gpr .x8 (by decide), kb.gpr .x9 (by decide),
      kb.gpr .x10 (by decide), ka.gpr .x4 (by decide), ka.gpr .x5 (by decide),
      ka.gpr .x6 (by decide), ka.gpr .x7 (by decide), ka.gpr .x8 (by decide),
      ka.gpr .x9 (by decide), a10]
  rw [a11] at eb
  have hb : rv b N + ((b.gpr .x12).toNat + 2 ^ 64 * rv b [.x13, .x14, .x15, .x20]) < 2 ^ 448 := by
    have : 2 * L < 2 ^ 448 := by decide +kernel
    rw [nb, eb]; omega
  refine WP.mono (foldAdd_ok b hcb.z hb) fun t ⟨et, kt⟩ => ?_
  rw [et, nb, eb]
  refine ⟨hlt, ?_, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩
  rw [hmod, rem_eq]

/-! ## The conditional subtraction -/

theorem csubAdd_eq : csubAdd = .adds .x .x12 .x4 C0 ::
    adcsOf [(.x13, .x5, C1), (.x14, .x6, C2), (.x15, .x7, C3), (.x16, .x8, Z), (.x17, .x9, Z),
      (.x19, .x10, KT)] := rfl

theorem k_words : c0.toNat + 2 ^ 64 * (c1.toNat + 2 ^ 64 * (c2.toNat + 2 ^ 64 * (c3.toNat +
    2 ^ 64 * (0 + 2 ^ 64 * (0 + 2 ^ 64 * (0xc000000000000000 : BitVec 64).toNat))))) =
    2 ^ 448 - L := by decide +kernel

/-- `csubAdd`: `S = N + K`, with the carry out of 448 bits. -/
theorem csubAdd_ok (s : State) (hc : Consts s) :
    WP isa (.block csubAdd) s fun t =>
      rv t S + 2 ^ 448 * t.c.toNat = rv s N + (2 ^ 448 - L) ∧ Keeps S s t := by
  rw [csubAdd_eq]
  refine WP.mono (adds_ok _ _ _ _ s (by decide)) fun t ⟨et, kt⟩ => ⟨?_, kt⟩
  simp only [dsts, lhs, rhs, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul] at et
  rw [← k_words]
  simp only [S, N, rv, Nat.mul_zero, Nat.add_zero] at et ⊢
  rw [hc.c0, hc.c1, hc.c2, hc.c3, hc.kt, hc.z, toNat_zero64] at et
  exact et

def mask (c : Bool) : BitVec 64 := if c then 0 else -1

theorem sel_mask (c : Bool) (n s : BitVec 64) : s ^^^ ((n ^^^ s) &&& mask c) = if c then s else n := by
  cases c
  · simp only [mask, Bool.false_eq_true, ite_false]
    rw [show (-1 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, BitVec.xor_comm n s,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [mask, ite_true]
    rw [show (n ^^^ s) &&& (0 : BitVec 64) = 0#64 from BitVec.and_zero, BitVec.xor_zero]

theorem sbcs_mask (c : Bool) :
    (0 : BitVec 64) + ~~~(0 : BitVec 64) + BitVec.ofNat 64 c.toNat = mask c := by
  cases c <;> decide

/-- The mask, then the selection: `R` from `N` (without a carry) or `S`. -/
theorem csubSel_ok (s : State) (hz : s.gpr Z = 0) :
    WP isa (.block (.sbcs .x .x20 Z Z :: selTriples.flatMap fun (r, n, s) => sel r n s)) s
      fun t => rem t = (if s.c then rv s S else rv s N) ∧
        Keeps [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x20] s t := by
  apply WP.of_runBlock
  simp only [selTriples, sel, Z, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left']
  simp only [Z] at hz
  simp only [hz, sbcs_mask]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp only [rem, R, S, N, rv, RegUpd.gpr_write, RegUpd.gpr_addWithCarry, BitVec.setWidth_eq,
      ite_true, ite_false, reduceCtorEq, sel_mask]
    cases s.c <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]

/-- `csub`: `N` (below `2L`) modulo `L` into `R`. -/
theorem csub_ok (s : State) (hc : Consts s) (hx : rv s N < 2 * L) :
    WP isa (.block csub) s fun t => rem t = rv s N % L ∧ Keeps foldClob s t := by
  rw [csub, WP.block_append_iff]
  refine WP.mono (csubAdd_ok s hc) fun a ⟨ea, ka⟩ => ?_
  have hza : a.gpr Z = 0 := (ka.gpr _ (by decide)).trans hc.z
  refine WP.mono (csubSel_ok a hza) fun t ⟨et, kt⟩ => ⟨?_, (ka.mono (by decide)).trans
    (kt.mono (by decide))⟩
  have na : rv a N = rv s N := Keeps.rv_eq ka (by decide)
  have hlt := rv_lt a S
  rw [na] at et
  have h2L : 2 * L ≤ 2 ^ 448 := by decide +kernel
  rw [et]
  simp only [S, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at hlt
  exact csub_nat h2L hx hlt ea

end VG.Proof.Ed448.AArch64
