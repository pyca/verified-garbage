import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Sample.Signs
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.BallLoop`. -/
section

/-!
# ML-DSA on AArch64: the loop of `vg_mldsa_sample_in_ball`

The polynomial `c` is kept in memory as the words that represent its
coefficients modulo `q` (`CStored`), from zeros; iteration `t` of the loop
over the 264 bytes after the sign bits does what `bStep` does to it and to `i`
(in `x10`, with `256 - i` in `x11`), with the sign bits not yet used in `x9`
(`step_ok`). The loop reads only the output, and writes only `c`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample.Ball

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_movk1 wp_addImm wp_subImm wp_strw
  wp_ldrw wp_ldrx wp_ldrb wp_sub wp_add wp_lsr wp_lsl wp_and wp_madd ptr_zero ptr_add toNat_sub_n
  toNat_add_n toNat_lsl_n toNat_byte toNat_lsr toNat_readW32 count_loop eval_zero eval_nonzero eq_zero_iff
  ne_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (lt_bit movQ_ok q_eq)
open VG.Spec.MlDsa (coeffAt Zq q ofInt IPoly n)

/-- The polynomial `c` of `R` is stored at `p`, as elements of `ℤ_q`. -/
def CStored (m : Mem) (p : Addr) (c : IPoly) : Prop := ∀ k < 256, coeffAt m p k = zw (ofInt c[k]!)

/-- What the loop needs of the state it starts from: the 272 bytes `X` at
`bP = x25 + 840`, which it may read, zeros at `aP = x26`, which it may
write, and `τ` in `x27`. -/
structure LPre (X : List Byte) (bP aP : Addr) (τ : Nat) (s : State) : Prop where
  buf : ∀ p < 272, s.mem (bP + BitVec.ofNat 64 p) = X.getD p 0
  inb : ∀ p < 272, InRegions (s.rd ++ s.wr) (bP + BitVec.ofNat 64 p) 1
  inw : InRegions (s.rd ++ s.wr) bP 8
  ina : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4
  disj : (⟨bP, 272⟩ : Region).Disjoint (polyR aP)
  x25 : s.gpr .x25 + BitVec.ofNat 64 840 = bP
  x26 : s.gpr .x26 = aP
  x27 : (s.gpr .x27).toNat = τ
  tau : τ ≤ 256
  zero : ∀ i < 256, coeffAt s.mem aP i = 0

/-- The sign bits, as a `u64`. -/
abbrev W (X : List Byte) : BitVec 64 := BitVec.ofNat 64 (leNat (X.take 8))

/-- The polynomial and `i` after `t` iterations. -/
abbrev St (X : List Byte) (τ t : Nat) : IPoly × Nat :=
  bFold τ (signs X) (Vector.replicate n 0, 256 - τ) ((X.drop 8).take t)

/-- The registers the loop writes. -/
abbrev lRegs : List Reg := [.x2, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

/-- At the start of iteration `t`, from the loop's entry state `s₀`. -/
structure BAt (X : List Byte) (bP aP : Addr) (τ : Nat) (s₀ : State) (t : Nat) (s : State) : Prop where
  keep : Keep VG.Proof.MlDsa.AArch64.Sample.Ball.lRegs s₀ s
  frame : Frame [polyR aP] s₀.mem s.mem
  x2 : s.gpr .x2 = bP + BitVec.ofNat 64 (8 + t)
  x5 : (s.gpr .x5).toNat = 264 - t
  x9 : s.gpr .x9 = VG.Proof.MlDsa.AArch64.Sample.Ball.W X >>> ((VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 - (256 - τ))
  x10 : (s.gpr .x10).toNat = (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2
  x11 : (s.gpr .x11).toNat = 256 - (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2
  x12 : (s.gpr .x12).toNat = q - 2
  x15 : (s.gpr .x15).toNat = 1
  st : VG.Proof.MlDsa.AArch64.Sample.Ball.CStored s.mem aP (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).1

theorem St_le (X : List Byte) (τ t : Nat) : (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 ≤ 256 := bFold_le (by simp) _

theorem St_ge (X : List Byte) (τ t : Nat) : 256 - τ ≤ (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 :=
  bFold_ge (τ := τ) (h := signs X) (Vector.replicate n 0, 256 - τ) _

theorem take_succ'' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The sign bit of `i`. -/
theorem sign_bit {X : List Byte} {τ i : Nat} (hτ : τ ≤ 256) (hi0 : 256 - τ ≤ i) (hi : i < 256) (hτ' : τ ≤ 64) :
    (VG.Proof.MlDsa.AArch64.Sample.Ball.W X >>> (i - (256 - τ))).getLsbD 0 = (signs X).getD (i + τ - 256) false := by
  rw [BitVec.getLsbD_ushiftRight, Nat.add_zero, signs_getD, BitVec.getLsbD_ofNat,
    show i - (256 - τ) = i + τ - 256 by omega, decide_eq_true (show i + τ - 256 < 64 by omega), Bool.true_and]

/-- The word of the sign `b`, `1 + (q - 2) b`. -/
theorem sgn_word (x : BitVec 64) {v : BitVec 64} (hv : v.toNat = q - 2) {o : BitVec 64} (ho : o.toNat = 1) :
    (o + (x &&& o) * v).setWidth 32 = zw (ofInt (if x.getLsbD 0 then -1 else 1)) := by
  have hb : (x &&& o).toNat = if x.getLsbD 0 then 1 else 0 := by
    rw [BitVec.toNat_and, ho, show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two]
    split <;> rename_i h <;> simp at h <;> omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, hb, hv, ho, zw_toNat]
  split <;> decide

/-- `c[i] ← c[j]`, `c[j] ← ±1` (with the sign bit 0 of `x9`), `i` incremented. -/
theorem set_ok {aP : Addr} {c : IPoly} {i j : Nat} (hij : j ≤ i) (hi : i < 256) {s : State}
    (h26 : s.gpr .x26 = aP) (h6 : (s.gpr .x6).toNat = j) (h10 : (s.gpr .x10).toNat = i)
    (h11 : (s.gpr .x11).toNat = 256 - i) (h12 : (s.gpr .x12).toNat = q - 2) (h15 : (s.gpr .x15).toNat = 1)
    (hw : ∀ k < 256, InRegions s.wr (coeffAddr aP k) 4) (hst : VG.Proof.MlDsa.AArch64.Sample.Ball.CStored s.mem aP c) :
    WP isa (.block bSet) s fun s' =>
      Keep [.x8, .x13, .x14, .x9, .x10, .x11] s s' ∧ (s'.gpr .x10).toNat = i + 1 ∧ (s'.gpr .x11).toNat = 256 - (i + 1) ∧
      s'.gpr .x9 = s.gpr .x9 >>> 1 ∧
      VG.Proof.MlDsa.AArch64.Sample.Ball.CStored s'.mem aP ((c.set! i c[j]!).set! j (if (s.gpr .x9).getLsbD 0 then -1 else 1)) ∧
      Frame [polyR aP] s.mem s'.mem := by
  have addr : ∀ {x : BitVec 64} {k : Nat}, x.toNat = k → k < 256 → aP + x <<< 2 = coeffAddr aP k :=
    fun {x k} hx hk => by
      rw [coeffAddr]; congr 1; apply BitVec.eq_of_toNat_eq
      rw [toNat_lsl_n (by rw [hx]; simp only [Nat.reducePow]; omega), hx, BitVec.toNat_ofNat]; omega
  refine wp_lsl (by decide) fun s₁ o₁ e₁ => wp_add fun s₂ o₂ e₂ => wp_lsl (by decide) fun s₃ o₃ e₃ =>
    wp_add fun s₄ o₄ e₄ => ?_
  have a8 : s₄.gpr .x8 = coeffAddr aP j := by
    rw [o₄.get .x8, o₃.get .x8, e₂, o₁.get .x26, h26, e₁]; exact addr h6 (by omega)
  have a13 : s₄.gpr .x13 = coeffAddr aP i := by
    rw [e₄, o₃.get .x26, o₂.get .x26, o₁.get .x26, h26, e₃, o₂.get .x10, o₁.get .x10]; exact addr h10 hi
  have w4 : s₄.wr = s.wr := by rw [o₄.wr, o₃.wr, o₂.wr, o₁.wr]
  have r4 : s₄.rd = s.rd := by rw [o₄.rd, o₃.rd, o₂.rd, o₁.rd]
  have m4 : s₄.mem = s.mem := by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  refine wp_ldrw (a := coeffAddr aP j) (by decide) (by rw [a8, ptr_zero])
    (by rw [r4, w4]; exact Proof.MlKem.AArch64.in_rd_wr (hw j (by omega))) fun s₅ o₅ e₅ => ?_
  refine wp_strw (a := coeffAddr aP i) (by decide) (by rw [o₅.get .x13, a13, ptr_zero])
    (by rw [o₅.wr, w4]; exact hw i hi) fun s₆ o₆ => ?_
  refine wp_and fun s₇ o₇ e₇ => wp_madd fun s₈ o₈ e₈ => ?_
  refine wp_strw (a := coeffAddr aP j) (by decide)
    (by rw [o₈.get .x8, o₇.get .x8, o₆.gpr, o₅.get .x8, a8, ptr_zero])
    (by rw [o₈.wr, o₇.wr, o₆.wr, o₅.wr, w4]; exact hw j (by omega)) fun s₉ o₉ => ?_
  refine wp_lsr (by decide) fun s₁₀ o₁₀ e₁₀ => wp_addImm (by decide) fun s₁₁ o₁₁ e₁₁ =>
    wp_subImm (by decide) fun s₁₂ o₁₂ e₁₂ => wp_nil ?_
  have k₈ := (((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans o₆.keep).trans
    o₇.keep).trans o₈.keep).mono (rs' := [.x8, .x13, .x14]) (by decide)
  have k₅ := ((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).mono
    (rs' := [.x8, .x13, .x14]) (by decide)
  have v14 : s₈.gpr .x14 = s.gpr .x15 + (s.gpr .x9 &&& s.gpr .x15) * s.gpr .x12 := by
    rw [e₈, o₇.get .x15, o₇.get .x12, e₇, o₆.gpr, k₅.get .x9, k₅.get .x15, k₅.get .x12]
  have m₉ : s₉.mem = (s.mem.writeW (coeffAddr aP i) (s.mem.readW (coeffAddr aP j) 32)).writeW
      (coeffAddr aP j) (zw (ofInt (if (s.gpr .x9).getLsbD 0 then -1 else 1))) := by
    rw [o₉.mem, o₈.mem, o₇.mem, o₆.mem, v14, VG.Proof.MlDsa.AArch64.Sample.Ball.sgn_word _ h12 h15, e₅, o₅.mem, m4]
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, toNat_readW32, Nat.mod_eq_of_lt (s.mem.readW _ 32).isLt]
  have k₁₂ := (((((((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans
    o₆.keep).trans o₇.keep).trans o₈.keep).trans o₉.keep).trans o₁₀.keep).trans o₁₁.keep).trans
    o₁₂.keep).mono (rs' := [.x8, .x13, .x14, .x9, .x10, .x11]) (by decide)
  have m₁₂ : s₁₂.mem = s₉.mem := by rw [o₁₂.mem, o₁₁.mem, o₁₀.mem]
  refine ⟨k₁₂, ?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [o₁₂.get .x10, e₁₁, o₁₀.get .x10, o₉.gpr, k₈.get .x10, toNat_add_n (by rw [h10]; simp; omega), h10]; rfl
  · rw [e₁₂, o₁₁.get .x11, o₁₀.get .x11, o₉.gpr, k₈.get .x11, toNat_sub_n (by rw [h11]; simp; omega),
      h11]; simp; omega
  · rw [o₁₂.get .x9, o₁₁.get .x9, e₁₀, o₉.gpr, k₈.get .x9]
  · rw [m₁₂, m₉, coeffAt_writeW _ _ hk (by omega), coeffAt_writeW _ _ hk hi,
      ipoly_set!_get _ _ (by simp only [n]; omega), ipoly_set!_get _ _ (by simp only [n]; omega)]
    by_cases ejk : j = k
    · subst ejk; rw [ifT rfl, ifT rfl]
    · rw [ifF ejk, ifF ejk]
      by_cases eik : i = k
      · subst eik; rw [ifT rfl, ifT rfl, ← coeffAt_eq, hst j (by omega)]
      · rw [ifF eik, ifF eik]; exact hst k hk
  · rw [m₁₂, m₉]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hi)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (by omega))


end VG.Proof.MlDsa.AArch64.Sample.Ball

namespace VG.Proof.MlDsa.AArch64.Sample.Ball

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_addImm wp_subImm wp_ldrx wp_ldrb wp_sub
  wp_lsr ptr_zero ptr_add toNat_sub_n toNat_byte toNat_lsr count_loop eval_zero eval_nonzero eq_zero_iff
  ne_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (lt_bit movQ_ok q_eq)
open VG.Spec.MlDsa (coeffAt Zq q ofInt IPoly n)

/-- The byte `p` of the output, in any state of the loop. -/
theorem BAt.byte {X : List Byte} {bP aP : Addr} {τ : Nat} {s₀ : State} (hp : VG.Proof.MlDsa.AArch64.Sample.Ball.LPre X bP aP τ s₀) {t : Nat}
    {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.Ball.BAt X bP aP τ s₀ t s) {p : Nat} (hp' : p < 272) :
    s.mem (bP + BitVec.ofNat 64 p) = X.getD p 0 := by
  rw [← hp.buf p hp']
  exact h.frame _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.disj _ (Offset.contains_base _ (by omega) (by omega))

/-- An iteration, from `BAt t`. -/
theorem step_ok {X : List Byte} (hX : X.length = 272) {bP aP : Addr} {τ : Nat} (hτ : τ ≤ 64) {s₀ : State}
    (hp : VG.Proof.MlDsa.AArch64.Sample.Ball.LPre X bP aP τ s₀) {t : Nat} (ht : t < 264) {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.Ball.BAt X bP aP τ s₀ t s) :
    WP isa bBody s fun s' => VG.Proof.MlDsa.AArch64.Sample.Ball.BAt X bP aP τ s₀ (t + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 264) := by
  have hle := VG.Proof.MlDsa.AArch64.Sample.Ball.St_le X τ t
  have hge := VG.Proof.MlDsa.AArch64.Sample.Ball.St_ge X τ t
  have hj : ((X.drop 8).getD t 0) = X.getD (8 + t) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have ht1 : VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ (t + 1) = bStep τ (signs X) (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t) ((X.drop 8).getD t 0) := by
    simp only [VG.Proof.MlDsa.AArch64.Sample.Ball.St]
    rw [VG.Proof.MlDsa.AArch64.Sample.Ball.take_succ'' _ (by rw [List.length_drop, hX]; omega), bFold_snoc]
  have hw : ∀ k < 256, InRegions s.wr (coeffAddr aP k) 4 := fun k hk => by rw [h.keep.wr]; exact hp.ina k hk
  -- the tail of the iteration
  have tail : ∀ u : State, Keep [.x6, .x7, .x8, .x13, .x14, .x9, .x10, .x11] s u → Frame [polyR aP] s.mem u.mem →
      u.gpr .x9 = VG.Proof.MlDsa.AArch64.Sample.Ball.W X >>> ((VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ (t + 1)).2 - (256 - τ)) → (u.gpr .x10).toNat = (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ (t + 1)).2 →
      (u.gpr .x11).toNat = 256 - (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ (t + 1)).2 → VG.Proof.MlDsa.AArch64.Sample.Ball.CStored u.mem aP (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ (t + 1)).1 →
      WP isa (.block [.addImm .x .x2 .x2 1, .subImm .x .x5 .x5 1]) u fun s' =>
        VG.Proof.MlDsa.AArch64.Sample.Ball.BAt X bP aP τ s₀ (t + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 264) := by
    intro u ku fu x9 x10 x11 st
    refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_subImm (by decide) fun u₂ o₂ e₂ => wp_nil ?_
    have c5 : (u₁.gpr .x5).toNat = 264 - t := by rw [o₁.get .x5, ku.get .x5, h.x5]
    have v5 : (u₂.gpr .x5).toNat = 264 - (t + 1) := by
      rw [e₂, toNat_sub_n (by rw [c5]; simp; omega), c5]; simp; omega
    refine ⟨⟨((h.keep.trans ku).trans (o₁.keep.trans o₂.keep)).mono, h.frame.trans (by
        rw [o₂.mem, o₁.mem]; exact fu), ?_, v5, by rw [o₂.get .x9, o₁.get .x9, x9],
      by rw [o₂.get .x10, o₁.get .x10, x10], by rw [o₂.get .x11, o₁.get .x11, x11],
      by rw [o₂.get .x12, o₁.get .x12, ku.get .x12, h.x12], by rw [o₂.get .x15, o₁.get .x15, ku.get .x15, h.x15],
      by rw [o₂.mem, o₁.mem]; exact st⟩, by rw [v5]; omega⟩
    rw [o₂.get .x2, e₁, ku.get .x2, h.x2, ptr_add, Nat.add_assoc]
  by_cases hf : (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 = 256
  · -- `i = 256`: nothing to do
    have e : VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ (t + 1) = VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t := by rw [ht1, bStep_full (by simp only [n]; omega)]
    refine WP.seq (WP.ite true (by rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, h.x11, hf]; rfl) (fun _ => wp_nil ?_)
      (fun h => nomatch h))
    exact tail s (Keep.refl _ _) (Frame.refl _ _) (by rw [e, h.x9]) (by rw [e, h.x10]) (by rw [e, h.x11])
      (by rw [e]; exact h.st)
  refine WP.seq (WP.ite false (by rw [VG.Proof.MlKem.AArch64.eval_zero, eq_zero_iff, h.x11]; simp; omega) (fun h => nomatch h)
    fun _ => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x2) 1 := by
    rw [h.keep.rd, h.keep.wr, h.x2]; exact hp.inb _ (by omega)
  have hb : s.mem (s.gpr .x2) = (X.drop 8).getD t 0 := by rw [hj, h.x2]; exact h.byte hp (by omega)
  refine WP.seq (wp_ldrb (a := s.gpr .x2) (by decide) (ptr_zero _) hin fun s₁ o₁ e₁ =>
    wp_sub fun s₂ o₂ e₂ => wp_lsr (by decide) fun s₃ o₃ e₃ => wp_nil ?_)
  have k₃ := ((o₁.keep.trans o₂.keep).trans o₃.keep).mono (rs' := [.x6, .x7]) (by decide)
  have v6 : (s₃.gpr .x6).toNat = ((X.drop 8).getD t 0).toNat := by
    rw [o₃.get .x6, o₂.get .x6, e₁, toNat_byte, hb]
  have hjl := ((X.drop 8).getD t 0).isLt
  have v7 : (s₃.gpr .x7).toNat = if (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 < ((X.drop 8).getD t 0).toNat then 1 else 0 := by
    rw [e₃, e₂, o₁.get .x10]
    exact lt_bit h.x10 (by rw [e₁, toNat_byte, hb])
      (by omega) (by simp only [Nat.reducePow] at hjl ⊢; omega)
  have hi : (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 < n := by simp only [n]; omega
  by_cases hr : (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 < ((X.drop 8).getD t 0).toNat
  · -- rejected
    have e : VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ (t + 1) = VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t := by
      rw [ht1]; unfold bStep; rw [ifT hi, ifT hr]
    refine WP.ite true (by rw [eval_nonzero, ne_zero_iff, v7, ifT hr]; rfl) (fun _ => wp_nil ?_)
      (fun h => nomatch h)
    exact tail s₃ k₃.mono (by rw [o₃.mem, o₂.mem, o₁.mem]; exact Frame.refl _ _)
      (by rw [e, k₃.get .x9, h.x9]) (by rw [e, k₃.get .x10, h.x10]) (by rw [e, k₃.get .x11, h.x11])
      (by rw [e, o₃.mem, o₂.mem, o₁.mem]; exact h.st)
  · -- a coefficient set
    have e : VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ (t + 1) = (((VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).1.set! (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).1[((X.drop 8).getD t 0).toNat]!).set!
        ((X.drop 8).getD t 0).toNat (if (signs X).getD ((VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 + τ - 256) false then -1 else 1),
        (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 + 1) := by
      rw [ht1]; unfold bStep; rw [ifT hi, ifF hr]
    refine WP.ite false (by rw [eval_nonzero, ne_zero_iff, v7, ifF hr]; rfl) (fun h => nomatch h)
      (fun _ => WP.mono (VG.Proof.MlDsa.AArch64.Sample.Ball.set_ok (aP := aP) (c := (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).1) (i := (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2)
        (j := ((X.drop 8).getD t 0).toNat) (by omega) (by omega)
        (by rw [k₃.get .x26, h.keep.get .x26, hp.x26]) v6 (by rw [k₃.get .x10, h.x10])
        (by rw [k₃.get .x11, h.x11]) (by rw [k₃.get .x12, h.x12]) (by rw [k₃.get .x15, h.x15])
        (by rw [o₃.wr, o₂.wr, o₁.wr]; exact hw) (by rw [o₃.mem, o₂.mem, o₁.mem]; exact h.st))
        fun s₄ ⟨k₄, x10, x11, x9, st, f₄⟩ => ?_)
    have sg : (s₃.gpr .x9).getLsbD 0 = (signs X).getD ((VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 + τ - 256) false := by
      rw [k₃.get .x9, h.x9]; exact VG.Proof.MlDsa.AArch64.Sample.Ball.sign_bit (by omega) hge (by omega) hτ
    rw [sg] at st
    refine tail s₄ (k₃.trans k₄).mono (by rw [← show s₃.mem = s.mem by rw [o₃.mem, o₂.mem, o₁.mem]]; exact f₄) ?_
      (by rw [e, x10]) (by rw [e, x11]) (by rw [e]; exact st)
    rw [x9, k₃.get .x9, h.x9, e, ← BitVec.shiftRight_add, show (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 + 1 - (256 - τ) =
      (VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ t).2 - (256 - τ) + 1 by omega]

/-- The loop: `BAt 264` at the end. -/
theorem loop_ok {X : List Byte} (hX : X.length = 272) {bP aP : Addr} {τ : Nat} (hτ : τ ≤ 64) {s₀ : State}
    (hp : VG.Proof.MlDsa.AArch64.Sample.Ball.LPre X bP aP τ s₀) : WP isa bLoop s₀ (VG.Proof.MlDsa.AArch64.Sample.Ball.BAt X bP aP τ s₀ 264) := by
  unfold bLoop bSetup movQ
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_ldrx (a := bP) (by decide) hp.x25 hp.inw fun s₁ o₁ e₁ => wp_movz fun s₂ o₂ e₂ =>
    wp_sub fun s₃ o₃ e₃ => wp_mov fun s₄ o₄ e₄ => wp_addImm (by decide) fun s₅ o₅ e₅ =>
    wp_movz fun s₆ o₆ e₆ => movQ_ok fun s₇ o₇ e₇ => wp_subImm (by decide) fun s₈ o₈ e₈ =>
    wp_movz fun s₉ o₉ e₉ => wp_nil ?_)
  have k₉ := ((((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans o₆.keep).trans
    o₇.keep).trans o₈.keep).trans o₉.keep)
  have m₉ : s₉.mem = s₀.mem := by
    rw [o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have hS : VG.Proof.MlDsa.AArch64.Sample.Ball.St X τ 0 = (Vector.replicate n 0, 256 - τ) := rfl
  have x27 : s₂.gpr .x27 = s₀.gpr .x27 := by rw [o₂.get .x27, o₁.get .x27]
  have i₀ : VG.Proof.MlDsa.AArch64.Sample.Ball.BAt X bP aP τ s₀ 0 s₉ := ⟨k₉.mono, by rw [m₉]; exact Frame.refl _ _,
    by rw [o₉.get .x2, o₈.get .x2, o₇.get .x2, o₆.get .x2, e₅, o₄.get .x25, o₃.get .x25, o₂.get .x25,
      o₁.get .x25, ← hp.x25, ptr_add],
    by rw [o₉.get .x5, o₈.get .x5, o₇.get .x5, e₆]; rfl,
    by rw [o₉.get .x9, o₈.get .x9, o₇.get .x9, o₆.get .x9, o₅.get .x9, o₄.get .x9, o₃.get .x9, o₂.get .x9, e₁,
      hS, Nat.sub_self, BitVec.ushiftRight_zero]
       exact readW_leNat _ _ _ fun k hk => hp.buf k (by omega),
    by rw [o₉.get .x10, o₈.get .x10, o₇.get .x10, o₆.get .x10, o₅.get .x10, o₄.get .x10, e₃,
      BitVec.toNat_sub, e₂, x27, hp.x27, hS]; simp; omega,
    by rw [o₉.get .x11, o₈.get .x11, o₇.get .x11, o₆.get .x11, o₅.get .x11, e₄, o₃.get .x27, x27, hp.x27, hS]
       simp only; have := hp.tau; omega,
    by rw [o₉.get .x12, e₈, toNat_sub_n (by rw [e₇, q_eq]; decide), e₇, q_eq]; rfl,
    by rw [e₉]; rfl,
    by rw [m₉, hS]; intro k hk
       rw [hp.zero k hk, getElem!_pos _ k (by simp only [n]; omega), Vector.getElem_replicate]; rfl⟩
  exact count_loop (by decide) (VG.Proof.MlDsa.AArch64.Sample.Ball.BAt X bP aP τ s₀) (fun t ht s h => VG.Proof.MlDsa.AArch64.Sample.Ball.step_ok hX hτ hp ht h) i₀

end VG.Proof.MlDsa.AArch64.Sample.Ball

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball`. -/
section

/-!
# ML-DSA on AArch64: `vg_mldsa_sample_in_ball`

Correctness: the prologue, the sponge (272 bytes of SHAKE256 of `c̃`), `c` set
to zeros, the loop (`BallLoop.lean`), which leaves what `bFold` computes, and
the end, which returns whether `i` reached 256. Constant time up to `c̃`, as
for `vg_mldsa_rej_ntt_poly` (`RejNttCT.lean`): the loop, whose branches and
addresses depend on the output, by `memTaint`, since both runs have the same
output and zeros in `c`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep only_write wp_nil wp_lsr ptr_add toNat_lsr agree_of)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H PolyIs coeffAt ballParams toRq n)
open VG.Spec.Sha3 (bytesAt)

/-- `τ`, the `u32` argument in `w2`. -/
abbrev tauOf (s : State) : Nat := ((s.gpr .x2).setWidth 32).toNat

/-- `vg_mldsa_sample_in_ball(ctilde = x0, len = x1, tau = w2, c = x3, scratch = x4) -> w0`,
with 16 bytes of stack below `sp`. -/
def sbK : Contract isa where
  pre s :=
    let ct : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let c : Region := ⟨s.gpr .x3, 1024⟩
    let scratch : Region := ⟨s.gpr .x4, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [ct] ∧ s.wr = [c, scratch] ∧ ct.Disjoint c ∧ ct.Disjoint scratch ∧
    c.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint ct ∧ stack.Disjoint c ∧
    stack.Disjoint scratch ∧ ((s.gpr .x1).toNat, VG.Proof.MlDsa.AArch64.Sample.tauOf s) ∈ ballParams
  post s s' :=
    (s'.gpr .x0).setWidth 32 =
        (if (ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256 then 1 else 0) ∧
      ((ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256 →
        PolyIs s'.mem (s.gpr .x3)
          (toRq (ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).1))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    (s₁.gpr .x2).setWidth 32 = (s₂.gpr .x2).setWidth 32 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat = bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat

namespace Ball

theorem ballParams_le {len τ : Nat} (h : (len, τ) ∈ ballParams) : len ≤ 64 ∧ 39 ≤ τ ∧ τ ≤ 60 := by
  simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  omega

/-- The call. -/
abbrev spOf (σ : State) : Sp :=
  ⟨σ.gpr .x0, (σ.gpr .x1).toNat, σ.gpr .x4, σ.gpr .x3, ((σ.gpr .x2).setWidth 32).setWidth 64⟩

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H ((VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ).msg σ) 272

theorem X_length (σ : State) : (VG.Proof.MlDsa.AArch64.Sample.Ball.X σ).length = 272 := VG.Proof.MlDsa.Sample.H_length _ _

section
variable {σ : State} (hp : sbK.pre σ)
include hp

theorem params : (σ.gpr .x1).toNat ≤ 64 ∧ 39 ≤ VG.Proof.MlDsa.AArch64.Sample.tauOf σ ∧ VG.Proof.MlDsa.AArch64.Sample.tauOf σ ≤ 60 :=
  VG.Proof.MlDsa.AArch64.Sample.Ball.ballParams_le hp.2.2.2.2.2.2.2.2.2

theorem spOk : SpOk (VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ) σ :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1, (σ.gpr .x1).isLt⟩

theorem pro_ok : WP isa (.block (pro .x4 .x3 (.addImm .w .x27 .x2 0) (mov .x4 .x1))) σ (J0 (VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ) σ) :=
  Sample.pro_ok (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) rfl rfl (by decide) rfl
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, ite_true, hs .x2 (by decide) (by decide)]
      congr 1
      exact BitVec.add_zero _⟩)
    (fun s hs => ⟨_, rfl, only_write _ _ _ _, by
      simp only [State.write, State.read, Size.bits, ite_true, BitVec.setWidth_eq, hs .x1 (by decide)
        (by decide) (by decide) (by decide), BitVec.add_zero]⟩)

/-- After the sponge, and `c` set to zeros. -/
structure Z (σ s : State) : Prop where
  env : Env (VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ) σ s
  out : bytesAt s.mem ((VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ).at' 840) 272 = VG.Proof.MlDsa.AArch64.Sample.Ball.X σ
  zero : ∀ i < 256, coeffAt s.mem (σ.gpr .x3) i = 0

theorem zero_ok {s : State} (h : J6 136 272 (VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ) σ s) : WP isa zeroPoly s (VG.Proof.MlDsa.AArch64.Sample.Ball.Z σ) :=
  WP.mono (zeroPoly_ok (fun i hi => inA (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) h.env.wr hi) h.env.x26) fun u ⟨k, z, f⟩ =>
    ⟨h.env.keepA (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) k f, by
      rw [MlKem.bytesAt_frame f (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact (a_scr' (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) (by omega)).symm) (by omega), h.out,
        (VG.Proof.MlDsa.Sample.H_eq _ _).symm], z⟩

theorem lpre {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.Ball.Z σ s) : Ball.LPre (VG.Proof.MlDsa.AArch64.Sample.Ball.X σ) ((VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ).at' 840) (σ.gpr .x3) (VG.Proof.MlDsa.AArch64.Sample.tauOf σ) s :=
  ⟨fun p hp' => by rw [← h.out, MlKem.bytesAt_getD _ _ hp'],
    fun p hp' => by rw [at_add]; exact inScrRd (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) h.env.rd h.env.wr (by omega),
    inScrRd (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) h.env.rd h.env.wr (by omega),
    fun i hi => inA (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) h.env.wr hi, (a_scr' (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) (by omega)).symm,
    by rw [h.env.x25], h.env.x26, by rw [h.env.x27]; simp; omega,
    by have := (VG.Proof.MlDsa.AArch64.Sample.Ball.params hp).2.2; omega, h.zero⟩

/-- After the loop. -/
structure LP (σ s : State) : Prop where
  env : Env (VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ) σ s
  x10 : (s.gpr .x10).toNat = (ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf σ) (VG.Proof.MlDsa.AArch64.Sample.Ball.X σ)).2
  st : VG.Proof.MlDsa.AArch64.Sample.Ball.CStored s.mem (σ.gpr .x3) (ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf σ) (VG.Proof.MlDsa.AArch64.Sample.Ball.X σ)).1

omit hp in
theorem St_264 : Ball.St (VG.Proof.MlDsa.AArch64.Sample.Ball.X σ) (VG.Proof.MlDsa.AArch64.Sample.tauOf σ) 264 = ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf σ) (VG.Proof.MlDsa.AArch64.Sample.Ball.X σ) := by
  simp only [Ball.St, ballFold]; rw [List.take_of_length_le (by rw [List.length_drop, VG.Proof.MlDsa.AArch64.Sample.Ball.X_length])]

theorem loopP_ok {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.Ball.Z σ s) : WP isa bLoop s (VG.Proof.MlDsa.AArch64.Sample.Ball.LP σ) :=
  WP.mono (Ball.loop_ok (VG.Proof.MlDsa.AArch64.Sample.Ball.X_length σ) (by have := (VG.Proof.MlDsa.AArch64.Sample.Ball.params hp).2.2; omega) (VG.Proof.MlDsa.AArch64.Sample.Ball.lpre hp h)) fun u hu => by
    have x10 := hu.x10
    have st := hu.st
    rw [VG.Proof.MlDsa.AArch64.Sample.Ball.St_264] at x10 st
    exact ⟨h.env.keepA (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) hu.keep hu.frame, x10, st⟩

/-- The end: the postcondition, and the calling convention. -/
theorem end_ok {s : State} (h : VG.Proof.MlDsa.AArch64.Sample.Ball.LP σ s) :
    WP isa (.block (.lsr .x .x0 .x10 8 :: epi)) s fun s' => abiPreserved σ s' ∧ sbK.post σ s' := by
  refine wp_lsr (by decide) fun s₁ h₁ e₁ => ?_
  have hl : (ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf σ) (VG.Proof.MlDsa.AArch64.Sample.Ball.X σ)).2 ≤ 256 := bFold_le (by simp only [n]; omega) _
  have v0 : (s₁.gpr .x0).toNat = if (ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf σ) (VG.Proof.MlDsa.AArch64.Sample.Ball.X σ)).2 = 256 then 1 else 0 := by
    rw [e₁, toNat_lsr, h.x10]
    split <;> simp only [Nat.reducePow] <;> omega
  refine WP.mono (epi_ok (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) (h.env.keep h₁.keep h₁.mem)) fun s' ⟨abi, m, k⟩ => ⟨abi, ?_, fun hf => ?_⟩
  · rw [k.get .x0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, v0]
    split <;> rfl
  · rw [m, h₁.mem]
    refine polyIs_of_coeffAt fun i hi => ?_
    rw [h.st i hi, getElem!_pos _ i hi, getElem!_pos _ i hi]
    simp only [toRq, Vector.getElem_map]

end

theorem correctWith (v : Proof.Sha3.AArch64.Permutation) (σ : State) (hp : sbK.pre σ) :
    ∃ t s', Exec isa (sampleInBallWith v.callee) σ t s' ∧ abiPreserved σ s' ∧ sbK.post σ s' :=
  WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Ball.pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (spongeWith_ok (v := v) (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) (rate := 136) (outlen := 272) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Ball.zero_ok hp h2) fun _ h3 =>
        WP.seq (WP.mono (VG.Proof.MlDsa.AArch64.Sample.Ball.loopP_ok hp h3) fun _ h4 => VG.Proof.MlDsa.AArch64.Sample.Ball.end_ok hp h4))))

theorem correct (σ : State) (hp : sbK.pre σ) :
    ∃ t s', Exec isa sampleInBall σ t s' ∧ abiPreserved σ s' ∧ sbK.post σ s' :=
  VG.Proof.MlDsa.AArch64.Sample.Ball.correctWith .scalar σ hp

end Ball

end VG.Proof.MlDsa.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H ballParams)
open VG.Spec.Sha3 (bytesAt)

namespace Ball

/-- The loop's regions. -/
abbrev lrd (σ : State) : List Region := [⟨(VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ).at' 840, 272⟩]
abbrev lwr (σ : State) : List Region := [polyR (σ.gpr .x3)]

theorem pub_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ₁ = VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ₂ := by
  rw [VG.Proof.MlDsa.AArch64.Sample.Ball.spOf, VG.Proof.MlDsa.AArch64.Sample.Ball.spOf, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]

theorem X_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : VG.Proof.MlDsa.AArch64.Sample.Ball.X σ₁ = VG.Proof.MlDsa.AArch64.Sample.Ball.X σ₂ := by
  simp only [VG.Proof.MlDsa.AArch64.Sample.Ball.X, Sp.msg]; rw [hq.2.2.2.2.2.2]

theorem loop_ct : RelCT isa (Rel2 sbK.pre sbK.pub VG.Proof.MlDsa.AArch64.Sample.Ball.Z) bLoop fun _ _ => True := by
  refine relMem VG.Proof.MlDsa.AArch64.Sample.Ball.lrd VG.Proof.MlDsa.AArch64.Sample.Ball.lwr [.x25, .x26, .x27]
    (fun σ₁ σ₂ _ _ hq => by simp [VG.Proof.MlDsa.AArch64.Sample.Ball.lrd, VG.Proof.MlDsa.AArch64.Sample.Ball.lwr, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq, hq.2.2.2.1]) (fun σ s hp h => ?_)
    (fun σ s hp h => ?_) (fun σ₁ σ₂ s₁ s₂ p₁ p₂ hq h₁ h₂ => ?_) (by taint_decide)
  · rw [regions (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) h.env]
    refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
    · rcases mem2 hr with rfl | rfl
      · exact ⟨(VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ).scrR, by simp, 840, rfl, by simp⟩
      · exact ⟨polyR (σ.gpr .x3), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
    · rw [List.mem_singleton.mp hr, h.env.wr, (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp).wr]
      exact ⟨polyR (σ.gpr .x3), by simp, 0, (Proof.MlKem.AArch64.ptr_zero _).symm, by simp⟩
  · have l := VG.Proof.MlDsa.AArch64.Sample.Ball.lpre hp h
    obtain ⟨t, u, e, -⟩ := Ball.loop_ok (VG.Proof.MlDsa.AArch64.Sample.Ball.X_length σ) (by have := (VG.Proof.MlDsa.AArch64.Sample.Ball.params hp).2.2; omega)
      (s₀ := s.withRegions (VG.Proof.MlDsa.AArch64.Sample.Ball.lrd σ) (VG.Proof.MlDsa.AArch64.Sample.Ball.lwr σ))
      ⟨l.buf, fun p hp' => Proof.MlKem.AArch64.in_rd (Proof.MlKem.AArch64.in_regions
        (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))),
        ⟨⟨(VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ).at' 840, 272⟩, by simp, by simp [Region.Contains]⟩,
        fun i hi => Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ hi),
        l.disj, l.x25, l.x26, l.x27, l.tau, l.zero⟩
    exact ⟨t, u, e⟩
  · refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1], fun r hr => ?_, fun x hx => ?_⟩
    · rcases VG.Proof.MlDsa.AArch64.Sample.mem3 hr with rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq]
    · obtain ⟨R, hR, hc⟩ := hx
      rcases mem2 hR with rfl | rfl
      · obtain ⟨p, hp', rfl⟩ := Proof.MlKem.AArch64.Sample.at_off hc
        rw [← MlKem.bytesAt_getD s₁.mem _ hp', h₁.out, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq, ← MlKem.bytesAt_getD s₂.mem _ hp', h₂.out,
          VG.Proof.MlDsa.AArch64.Sample.Ball.X_eq hq]
      · rw [byte_zero h₁.zero hc, byte_zero h₂.zero (by rw [← hq.2.2.2.1]; exact hc)]

theorem ctWith (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa sbK.pre sbK.pub (sampleInBallWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.mldsaBallTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True)
    (P := Rel2 sbK.pre sbK.pub fun σ s => s = σ)
    ?_ (fun s₁ s₂ h => ⟨s₁, s₂, h.1, h.2.1, h.2.2, rfl, rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ) σ) [.x0, .x1, .x3, .x4]
    (fun σ s hp h => by subst h; exact VG.Proof.MlDsa.AArch64.Sample.Ball.pro_ok hp) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂
      refine ⟨hq.2.2.2.2.2.1, fun r hr => ?_⟩
      rcases VG.Proof.MlDsa.AArch64.Sample.mem4 hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.2.1, hq.2.2.2.2.1]) (by taint_decide)) ?_
  refine RelCT.seq (vectorRelTaintStep (J' := fun σ => J6 136 272 (VG.Proof.MlDsa.AArch64.Sample.Ball.spOf σ) σ) [.x25, .x26, .x27, .x3, .x4]
    (fun σ s hp h => spongeWith_ok (v := v) (VG.Proof.MlDsa.AArch64.Sample.Ball.spOk hp) (by decide) (by decide) h) (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      refine ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h₁.env.x25, h₂.env.x25, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq]
      · rw [h₁.env.x26, h₂.env.x26, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq]
      · rw [h₁.env.x27, h₂.env.x27, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq]
      · rw [h₁.x3, h₂.x3, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq]
      · exact toNat_inj h₁.x4 (by rw [h₂.x4, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq])) hhint) ?_
  refine RelCT.seq (relTaintStep (J' := VG.Proof.MlDsa.AArch64.Sample.Ball.Z) [.x26] (fun σ s hp h => VG.Proof.MlDsa.AArch64.Sample.Ball.zero_ok hp h)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1], fun r hr => by
      rw [List.mem_singleton.mp hr, h₁.env.x26, h₂.env.x26, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq]⟩) (by taint_decide)) ?_
  refine RelCT.seq (relStep (J' := VG.Proof.MlDsa.AArch64.Sample.Ball.LP) (fun σ s hp h => VG.Proof.MlDsa.AArch64.Sample.Ball.loopP_ok hp h) VG.Proof.MlDsa.AArch64.Sample.Ball.loop_ct) ?_
  exact relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp, h₂.env.sp, hq.2.2.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr, h₁.env.x25, h₂.env.x25, VG.Proof.MlDsa.AArch64.Sample.Ball.pub_eq hq]⟩) (by taint_decide)

theorem ct : ConstantTime isa sbK.pre sbK.pub sampleInBall :=
  VG.Proof.MlDsa.AArch64.Sample.Ball.ctWith .scalar

end Ball

end VG.Proof.MlDsa.AArch64.Sample

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)

/-- A state satisfying the precondition. -/
def sbSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 32 | .x2 => 39 | .x3 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sampleInBall_verifiedWith (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target (Impl.MlDsa.AArch64.Sample.sampleInBallWith v.callee)
    (Spec.MlDsa.sampleInBallContract AArch64.abi 16) :=
  Verified.of_correct (Ball.correctWith v) (Ball.ctWith v)
    { pre := by sig_implies_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, VG.Proof.MlDsa.AArch64.Sample.sbK,
        AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, VG.Proof.MlDsa.AArch64.Sample.sbK, AArch64.abi,
          AArch64.argRegs]
        dsimp only [VG.Proof.MlDsa.AArch64.Sample.sbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with ball := 272 }, by
            show Option.map _ (Spec.MlDsa.sampleInBall _ 272 _) = _
            rw [sampleInBall_some _ (by decide) hf, hpoly]; rfl⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.sampleInBall _ Spec.MlDsa.minBounds.ball _) = none
              rw [sampleInBall_none (B := 272) _ (by decide) (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, VG.Proof.MlDsa.AArch64.Sample.sbK, AArch64.abi,
          AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2, hx3, hx4⟩ := h
        exact ⟨hx0, hx1, hx2, hx3, hx4, hsp, VG.Proof.MlKem.map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, VG.Proof.MlDsa.AArch64.Sample.sbK,
        AArch64.abi, AArch64.argRegs] [sbSat] using VG.Proof.MlDsa.AArch64.Sample.sbSat }

theorem sampleInBall_verified : Verified AArch64.target Impl.MlDsa.AArch64.Sample.sampleInBall
    (Spec.MlDsa.sampleInBallContract AArch64.abi 16) :=
  VG.Proof.MlDsa.AArch64.Sample.sampleInBall_verifiedWith .scalar

end VG.Proof.MlDsa.AArch64.Sample

end
