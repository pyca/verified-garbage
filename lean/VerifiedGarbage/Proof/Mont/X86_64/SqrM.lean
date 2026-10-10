import VerifiedGarbage.Proof.Mont.X86_64.SqrS
import VerifiedGarbage.Proof.Mont.X86_64.Rounds
import VerifiedGarbage.Proof.Mont.X86_64.Friendly

/-!
# Montgomery arithmetic on x86-64: P-384's squaring

`sqrS M o a` (`Impl/Mont/X86_64.lean`), with BMI2 and ADX or without: the square
`[a]²` in the registers the operations change and the temporary area, then six
of P-384's reductions of its low half and the high half added (`sqrS_ok`).

Without BMI2 and ADX, the parts are: the round of the reduction on six words
(`redShortM_ok`, `redShortX_ok` with `uSparse` and `prodSparse`), the rows of
the cross products by `mulRow` (`row0M_ok`, `crossRowM_ok`), and the cross
products doubled in one carry chain and the squares added with a carry word
(`dblHalfM_ok`, `sq01M_ok`, `sqStepsM_ok`, `sqrDblM_ok`). Each has the
postcondition of its BMI2 and ADX counterpart (`SqrS.lean`), so either way:

* the cross products (`sqCrossG_ok`), each row given that its window does not
  overflow, which the rows' partial sums bound;
* `C` doubled and the squares added (`sqrDbl'_ok`), which makes `[a]²`;
* the reductions (`redsShort_ok`), on six words rotating through `sqWin6`,
  leave `(L + U p) / 2³⁸⁴ ≤ p` for the low half `L`, and with the high half
  `H < p` added, below `2p`.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry sub_borrow sbb_borrow
  toNat_ofBool mulx_arith)

/-! ## The reduction -/

theorem subShortM_ok (s : State) {d0 d1 d2 d3 d4 d5 : Reg} (hf : Fresh [d0, d1, d2, d3, d4, d5])
    (hC : (s.gpr .rbp).toNat + 2 ^ 64 * (s.gpr .rdx).toNat + 2 ^ 128 * (s.gpr d0).toNat ≤
      2 ^ 66 * (s.gpr .rcx).toNat) :
    WP isa (.block [.alu .sub d1 (.reg .rbp), .alu .sbb d2 (.reg .rdx), .alu .sbb d3 (.reg d0),
      .alu .sbb d4 (.imm 0), .alu .sbb d5 (.imm 0), .mov d0 (.reg .rcx), .alu .sbb d0 (.imm 0)]) s fun s' =>
      regsVal s' [d1, d2, d3, d4, d5, d0] +
          ((s.gpr .rbp).toNat + 2 ^ 64 * (s.gpr .rdx).toNat + 2 ^ 128 * (s.gpr d0).toNat) =
        regsVal s [d1, d2, d3, d4, d5] + 2 ^ 320 * (s.gpr .rcx).toNat ∧
      Keeps [d0, d1, d2, d3, d4, d5] s s' := by
  obtain ⟨hnd, hr⟩ := hf
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨⟨n01, n02, n03, n04, n05⟩, ⟨n12, n13, n14, n15⟩, ⟨n23, n24, n25⟩, ⟨n34, n35⟩, n45, -⟩ := hnd
  obtain ⟨⟨ia0, ic0, id0, ib0, -⟩, ⟨ia1, ic1, id1, ib1, -⟩, ⟨ia2, ic2, id2, ib2, -⟩, ⟨ia3, ic3, id3, ib3, -⟩,
    ⟨ia4, ic4, id4, ib4, -⟩, ⟨ia5, ic5, id5, ib5, -⟩⟩ := hr
  have m01 := Ne.symm n01
  have m02 := Ne.symm n02
  have m03 := Ne.symm n03
  have m04 := Ne.symm n04
  have m05 := Ne.symm n05
  have m12 := Ne.symm n12
  have m13 := Ne.symm n13
  have m14 := Ne.symm n14
  have m15 := Ne.symm n15
  have m23 := Ne.symm n23
  have m24 := Ne.symm n24
  have m25 := Ne.symm n25
  have m34 := Ne.symm n34
  have m35 := Ne.symm n35
  have m45 := Ne.symm n45
  have ia0' := Ne.symm ia0
  have ic0' := Ne.symm ic0
  have id0' := Ne.symm id0
  have ib0' := Ne.symm ib0
  have ia1' := Ne.symm ia1
  have ic1' := Ne.symm ic1
  have id1' := Ne.symm id1
  have ib1' := Ne.symm ib1
  have ia2' := Ne.symm ia2
  have ic2' := Ne.symm ic2
  have id2' := Ne.symm id2
  have ib2' := Ne.symm ib2
  have ia3' := Ne.symm ia3
  have ic3' := Ne.symm ic3
  have id3' := Ne.symm id3
  have ib3' := Ne.symm ib3
  have ia4' := Ne.symm ia4
  have ic4' := Ne.symm ic4
  have id4' := Ne.symm id4
  have ib4' := Ne.symm ib4
  have ia5' := Ne.symm ia5
  have ic5' := Ne.symm ic5
  have id5' := Ne.symm id5
  have ib5' := Ne.symm ib5
  simp only [regsVal]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ↓reduceIte, se0, Option.some.injEq, exists_eq_left', *]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · generalize s.gpr d1 = x1 at *
    generalize s.gpr d2 = x2 at *
    generalize s.gpr d3 = x3 at *
    generalize s.gpr d4 = x4 at *
    generalize s.gpr d5 = x5 at *
    generalize s.gpr .rbp = r at *
    generalize s.gpr .rdx = d at *
    generalize s.gpr d0 = y at *
    generalize s.gpr .rcx = u at *
    have e1 := sub_borrow x1 r
    generalize decide (x1.toNat < r.toNat) = β1 at e1 ⊢
    have e2 := sbb_borrow x2 d β1
    generalize decide (x2.toNat < d.toNat + β1.toNat) = β2 at e2 ⊢
    have e3 := sbb_borrow x3 y β2
    generalize decide (x3.toNat < y.toNat + β2.toNat) = β3 at e3 ⊢
    have e4 := sbb_borrow x4 0 β3
    generalize decide (x4.toNat < (0 : BitVec 64).toNat + β3.toNat) = β4 at e4 ⊢
    have e5 := sbb_borrow x5 0 β4
    generalize decide (x5.toNat < (0 : BitVec 64).toNat + β4.toNat) = β5 at e5 ⊢
    have e6 := sbb_borrow u 0 β5
    have z : (0 : BitVec 64).toNat = 0 := rfl
    rw [z] at e4 e5 e6
    have k1 := (x1 - r).isLt
    have k2 := (x2 - d - BitVec.setWidth 64 (BitVec.ofBool β1)).isLt
    have k3 := (x3 - y - BitVec.setWidth 64 (BitVec.ofBool β2)).isLt
    have k4 := (x4 - 0 - BitVec.setWidth 64 (BitVec.ofBool β3)).isLt
    have k5 := (x5 - 0 - BitVec.setWidth 64 (BitVec.ofBool β4)).isLt
    have k6 := (u - 0 - BitVec.setWidth 64 (BitVec.ofBool β5)).isLt
    have q5 := Bool.toNat_le β5
    generalize (x1 - r).toNat = R1 at *
    generalize (x2 - d - BitVec.setWidth 64 (BitVec.ofBool β1)).toNat = R2 at *
    generalize (x3 - y - BitVec.setWidth 64 (BitVec.ofBool β2)).toNat = R3 at *
    generalize (x4 - 0 - BitVec.setWidth 64 (BitVec.ofBool β3)).toNat = R4 at *
    generalize (x5 - 0 - BitVec.setWidth 64 (BitVec.ofBool β4)).toNat = R5 at *
    generalize (u - 0 - BitVec.setWidth 64 (BitVec.ofBool β5)).toNat = U at *
    generalize (decide (u.toNat < 0 + β5.toNat)).toNat = D6 at *
    generalize β1.toNat = B1 at *
    generalize β2.toNat = B2 at *
    generalize β3.toNat = B3 at *
    generalize β4.toNat = B4 at *
    generalize β5.toNat = B5 at *
    generalize x1.toNat = X1 at *
    generalize x2.toNat = X2 at *
    generalize x3.toNat = X3 at *
    generalize x4.toNat = X4 at *
    generalize x5.toNat = X5 at *
    generalize r.toNat = Rb at *
    generalize d.toNat = Dd at *
    generalize y.toNat = Y at *
    generalize u.toNat = Uu at *
    have h5 : R1 + 2 ^ 64 * (R2 + 2 ^ 64 * (R3 + 2 ^ 64 * (R4 + 2 ^ 64 * R5))) +
        (Rb + 2 ^ 64 * Dd + 2 ^ 128 * Y) =
        X1 + 2 ^ 64 * (X2 + 2 ^ 64 * (X3 + 2 ^ 64 * (X4 + 2 ^ 64 * X5))) + 2 ^ 320 * B5 := by
      omega_using [e1, e2, e3, e4, e5]
    have hD6 : D6 = 0 := by omega_using [h5, e6, hC, k1, k2, k3, k4, k5, k6, q5]
    subst hD6
    rw [pow128w, pow320w] at h5 ⊢
    clear hC
    grind only
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2, ite_false]

theorem keeps_shortM {s s₁ s₂ s₃ : State} {d0 d1 d2 d3 d4 d5 : Reg} (k₁ : Keeps [.rcx] s s₁)
    (k₂ : Keeps [.rax, .rdx, .rbp, d0] s₁ s₂) (k₃ : Keeps [d0, d1, d2, d3, d4, d5] s₂ s₃) :
    Keeps [.rax, .rcx, .rdx, .rbp, d0, d1, d2, d3, d4, d5] s s₃ :=
  ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))

/-- A round of P-384's reduction on six words without BMI2: as `redShortX_ok`. -/
theorem redShortM_ok {s : State} {d0 d1 d2 d3 d4 d5 : Reg} (hf : Fresh [d0, d1, d2, d3, d4, d5]) {m : Nat}
    (hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319) :
    WP isa (.block (redShortM [d0, d1, d2, d3, d4, d5])) s fun s' =>
      (∃ u, u < 2 ^ 64 ∧ 2 ^ 64 * regsVal s' [d1, d2, d3, d4, d5, d0] =
        regsVal s [d0, d1, d2, d3, d4, d5] + u * m) ∧
      Keeps [.rax, .rcx, .rdx, .rbp, d0, d1, d2, d3, d4, d5] s s' := by
  have h0 := hf.head
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h0
  obtain ⟨⟨n01, n02, n03, n04, n05⟩, ha0, hc0, hd0, hb0, -⟩ := h0
  have hR : ∀ q ∈ [d1, d2, d3, d4, d5], q ≠ .rax ∧ q ≠ .rcx ∧ q ≠ .rdx ∧ q ≠ .rbp ∧ q ≠ d0 :=
    fun q hq => by
      have := hf.2 q (List.mem_cons_of_mem _ hq)
      refine ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, fun h => ?_⟩
      subst h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with h | h | h | h | h <;> subst h
      exacts [n01 rfl, n02 rfl, n03 rfl, n04 rfl, n05 rfl]
  rw [redShortM, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (uSparse_ok s hc0) fun s₁ ⟨e₁, k₁⟩ => ?_
  refine WP.mono (prodSparse_ok s₁ ⟨ha0, hc0, hd0, hb0⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  have g₁ : ∀ q ∈ [d1, d2, d3, d4, d5], s₂.gpr q = s.gpr q := fun q hq => by
    obtain ⟨qa, qc, qd, qb, q0⟩ := hR q hq
    rw [k₂.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨qa, qd, qb, q0⟩),
      k₁.1 q (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact qc)]
  have hL₂ : regsVal s₂ [d1, d2, d3, d4, d5] = regsVal s [d1, d2, d3, d4, d5] := regsVal_congr g₁
  have hu₂ : s₂.gpr .rcx = s₁.gpr .rcx := k₂.1 _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, by decide, by decide,
      Ne.symm hc0⟩)
  have hx₁ : s₁.gpr d0 = s.gpr d0 := k₁.1 _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hc0)
  generalize hU : (s₁.gpr .rcx).toNat = U at e₁ e₂
  generalize hx : (s.gpr d0).toNat = x at e₁
  have hUlt : U < 2 ^ 64 := hU ▸ (s₁.gpr .rcx).isLt
  have hx64 : x < 2 ^ 64 := hx ▸ (s.gpr d0).isLt
  have hlow : U * 0xffffffff00000001 % 2 ^ 64 = x := by omega_using [e₁, hx64]
  rw [hlow] at e₂
  generalize hC : (s₂.gpr .rbp).toNat + 2 ^ 64 * (s₂.gpr .rdx).toNat + 2 ^ 128 * (s₂.gpr d0).toNat = C at e₂
  have hTv : regsVal s [d0, d1, d2, d3, d4, d5] = x + 2 ^ 64 * regsVal s [d1, d2, d3, d4, d5] := by
    rw [regsVal, hx]
  have hU₂ : (s₂.gpr .rcx).toNat = U := by rw [hu₂, hU]
  subst hm
  refine WP.mono (subShortM_ok s₂ hf (by omega_using [e₂, hC, hU₂])) fun s₃ ⟨e₃, k₃⟩ =>
    ⟨⟨U, hUlt, ?_⟩, keeps_shortM k₁ k₂ k₃⟩
  rw [hTv]
  omega_using [e₂, e₃, hL₂, hC, hU₂]

/-! ## The rows of the cross products -/

/-- `mov r, [d]`. -/
theorem movLoad_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (r : Reg) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov r (.mem (sc d))]) s fun s' => s'.gpr r = word s.mem base d ∧ s'.cf = s.cf ∧
      Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs hd, Option.map_some,
    RegUpd.gpr_setReg_self, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg_of_ne _ _ hq]

/-- `mov y, r`. -/
theorem movRegM_ok (s : State) (y r : Reg) :
    WP isa (.block [.mov y (.reg r)]) s fun s' => s'.gpr y = s.gpr r ∧ Keeps [y] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg_of_ne _ _ hq]

/-- `ts ++ [y] = ts + rcx · [d …]` by `mulRow`, its carry word moved to `y`. -/
theorem rowTailM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} {ts : List Reg}
    {y : Reg} (hd : d + 8 * ts.length ≤ size) (hf : Fresh (ts ++ [y])) :
    WP isa (.block (mulRow ts d ++ ([.mov y (.reg .rbp)] : List Instr))) s fun s' =>
      regsVal s' (ts ++ [y]) = regsVal s ts + (s.gpr .rcx).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.rbp :: .rax :: .rdx :: y :: ts) s s' := by
  have hft : Fresh ts := ⟨(List.nodup_append.mp hf.1).1, fun q hq => hf.2 q (List.mem_append_left _ hq)⟩
  have hy := hf.2 y (List.mem_append_right _ (List.mem_singleton_self y))
  have hyt : y ∉ ts := fun h => (List.nodup_append.mp hf.1).2.2 y h y (List.mem_singleton_self y) rfl
  rw [mulRow, ← List.singleton_append, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mov32zero_ok s .rbp) fun s₁ ⟨z₁, _, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulSteps_ok ts hs₁ hd hft) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine WP.mono (movRegM_ok s₂ y .rbp) fun s₃ ⟨e₃, k₃⟩ => ⟨?_, ?_⟩
  · have hR : regsVal s₃ ts = regsVal s₂ ts := regsVal_congr fun q hq => k₃.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hyt (h ▸ hq))
    have hR₁ : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact (hft.2 q hq).2.2.2.1)
    rw [regsVal_append, hR]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    rw [e₃, e₂, hR₁, z₁, k₁.1 .rcx (by decide), k₁.2.1]
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
  · exact ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))

/-- A row of the cross products without BMI2 and ADX: `ts ++ [y] = ts + [d₀] · [d …]`. -/
theorem crossRowM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d₀ d : Nat}
    {ts : List Reg} {y : Reg} (hd₀ : d₀ + 8 ≤ size) (hd : d + 8 * ts.length ≤ size) (hf : Fresh (ts ++ [y])) :
    WP isa (.block (([.mov .rcx (.mem (sc d₀))] : List Instr) ++ mulRow ts d ++ ([.mov y (.reg .rbp)] : List Instr))) s fun s' =>
      regsVal s' (ts ++ [y]) = regsVal s ts + (word s.mem base d₀).toNat * wordsVal s.mem base d ts.length ∧
      Keeps (.rdx :: .rbp :: .rcx :: .rax :: y :: ts) s s' := by
  have hft : ∀ q ∈ ts, q ≠ .rcx := fun q hq => (hf.2 q (List.mem_append_left _ hq)).2.1
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (movLoad_ok hs .rcx hd₀) fun s₁ ⟨e₁, _, k₁⟩ => ?_
  refine WP.mono (rowTailM_ok (hs.of_keeps k₁ (by decide)) hd hf) fun s₂ ⟨e₂, k₂⟩ =>
    ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  rw [e₂, e₁, k₁.2.1, regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hft q hq)]

/-- Row 0 of the cross products without BMI2 and ADX: `r8–r13 = a₀ · (a₁, …, a₅)`. -/
theorem row0M_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a + 48 ≤ size) :
    WP isa (.block (sqrRow0M a)) s fun s' => regsVal s' [.r8, .r9, .r10, .r11, .r12, .r13] =
          (word s.mem base a).toNat * wordsVal s.mem base (a + 8) 5 ∧
        Keeps [.rdx, .rbp, .rcx, .rax, .r8, .r9, .r10, .r11, .r12, .r13] s s' := by
  rw [sqrRow0M, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movLoad_ok hs .rcx (d := a) (by omega_arith)) fun s₁ ⟨e₁, _, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok s₁ [.r8, .r9, .r10, .r11, .r12]) fun s₂ ⟨z₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (rowTailM_ok hs₂ (ts := [.r8, .r9, .r10, .r11, .r12]) (y := .r13) (d := a + 8)
    (by simp only [List.length_cons, List.length_nil]; omega_arith) ⟨by decide, by decide⟩) fun s₃ ⟨e₃, k₃⟩ =>
    ⟨?_, ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))⟩
  rw [show ([.r8, .r9, .r10, .r11, .r12, .r13] : List Reg) = [.r8, .r9, .r10, .r11, .r12] ++ [.r13] from rfl, e₃,
    regsVal_zero z₂, k₂.1 .rcx (by decide), e₁, k₂.2.1, k₁.2.1, Nat.zero_add]
  rfl

/-! ## The squares -/

/-- `mov rax, [d]`, `mul rax`: `rax + 2⁶⁴ rdx = [d]²`, the high half at most `2⁶⁴ - 2`. -/
theorem sqLoad_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rax (.mem (sc d)), .mul .rax]) s fun s' =>
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = (word s.mem base d).toNat * (word s.mem base d).toNat ∧
      (s'.gpr .rdx).toNat + 2 ≤ 2 ^ 64 ∧ Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs hd, execMul, Option.map_some,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  have hw := (word s.mem base d).isLt
  have hp : (word s.mem base d).toNat * (word s.mem base d).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega_arith) (by omega_arith)
  refine ⟨mulx_arith _ _, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

/-- `add rax, rbp`, `adc rdx, 0`: the carry word added to `rax + 2⁶⁴ rdx`, whose
high half does not overflow. -/
theorem addWordM_ok (s : State) (hd : (s.gpr .rdx).toNat + 2 ≤ 2 ^ 64) (hb : (s.gpr .rbp).toNat ≤ 1) :
    WP isa (.block [.alu .add .rax (.reg .rbp), .alu .adc .rdx (.imm 0)]) s fun s' =>
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat =
        (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat + (s.gpr .rbp).toNat ∧
      Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ↓reduceIte, reduceCtorEq, se0, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e1 := add_carry (s.gpr .rax) (s.gpr .rbp)
    have e2 := adc_carry (s.gpr .rdx) 0 (decide (2 ^ 64 ≤ (s.gpr .rax).toNat + (s.gpr .rbp).toNat))
    generalize decide (2 ^ 64 ≤ (s.gpr .rax).toNat + (s.gpr .rbp).toNat) = c at e1 e2 ⊢
    have := Bool.toNat_le c
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero] at e2 ⊢
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- `add lo, rax`, `adc hi, rdx`, `mov ebp, 0`, `adc rbp, 0`: `rax + 2⁶⁴ rdx`
added at `lo`, `hi`, the carry out in `rbp`. -/
theorem addPairM_ok (s : State) {lo hi : Reg} (hf : [lo, hi, .rax, .rdx, .rbp].Nodup) :
    WP isa (.block [.alu .add lo (.reg .rax), .alu .adc hi (.reg .rdx), .mov32 .rbp (.imm 0),
      .alu .adc .rbp (.imm 0)]) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
        (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat ∧
      Keeps [lo, hi, .rbp] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hf
  obtain ⟨⟨hlh, hla, hld, hlb⟩, ⟨hha, hhd, hhb⟩, -⟩ := hf
  have hhl := Ne.symm hlh
  have hal := Ne.symm hla
  have hdl := Ne.symm hld
  have hbl := Ne.symm hlb
  have hah := Ne.symm hha
  have hdh := Ne.symm hhd
  have hbh := Ne.symm hhb
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, Option.bind_some,
    Option.map_some, State.setReg32, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, ↓reduceIte, se0, Option.some.injEq, exists_eq_left', *]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e1 := add_carry (s.gpr lo) (s.gpr .rax)
    generalize decide (2 ^ 64 ≤ (s.gpr lo).toNat + (s.gpr .rax).toNat) = c₁ at e1 ⊢
    have e2 := adc_carry (s.gpr hi) (s.gpr .rdx) c₁
    generalize decide (2 ^ 64 ≤ (s.gpr hi).toNat + (s.gpr .rdx).toNat + c₁.toNat) = c₂ at e2 ⊢
    have z : ∀ c : Bool, (BitVec.setWidth 64 (0 : BitVec 32) + 0 + (BitVec.ofBool c).setWidth 64).toNat =
        c.toNat := by intro c; cases c <;> rfl
    rw [z]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A square added at two registers: `lo + 2⁶⁴ hi + 2¹²⁸ rbp' = lo + 2⁶⁴ hi + rbp + [d]²`
for a carry word `rbp ≤ 1`. -/
theorem sqStepM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) {lo hi : Reg} (hf : [lo, hi, .rax, .rdx, .rbp].Nodup) (hb : (s.gpr .rbp).toNat ≤ 1) :
    WP isa (.block (sqStepM d lo hi)) s fun s' =>
      (s'.gpr lo).toNat + 2 ^ 64 * (s'.gpr hi).toNat + 2 ^ 128 * (s'.gpr .rbp).toNat =
        (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr .rbp).toNat +
          (word s.mem base d).toNat * (word s.mem base d).toNat ∧
      (s'.gpr .rbp).toNat ≤ 1 ∧ Keeps [.rax, .rdx, lo, hi, .rbp] s s' := by
  have hf' := hf
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hf'
  obtain ⟨⟨hlh, hla, hld, hlb⟩, ⟨hha, hhd, hhb⟩, -⟩ := hf'
  rw [sqStepM, show ([.mov .rax (.mem (sc d)), .mul .rax, .alu .add .rax (.reg .rbp), .alu .adc .rdx (.imm 0),
    .alu .add lo (.reg .rax), .alu .adc hi (.reg .rdx), .mov32 .rbp (.imm 0), .alu .adc .rbp (.imm 0)] :
    List Instr) = [.mov .rax (.mem (sc d)), .mul .rax] ++ ([.alu .add .rax (.reg .rbp), .alu .adc .rdx (.imm 0)] ++
    [.alu .add lo (.reg .rax), .alu .adc hi (.reg .rdx), .mov32 .rbp (.imm 0), .alu .adc .rbp (.imm 0)])
    from rfl, WP.block_append_iff]
  refine WP.mono (sqLoad_ok hs hd) fun s₁ ⟨e₁, b₁, k₁⟩ => ?_
  have r₁ : s₁.gpr .rbp = s.gpr .rbp := k₁.1 _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (addWordM_ok s₁ b₁ (by rw [r₁]; exact hb)) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine WP.mono (addPairM_ok s₂ hf) fun s₃ ⟨e₃, k₃⟩ => ⟨?_, ?_, ?_⟩
  · have l₂ : s₂.gpr lo = s.gpr lo := by
      rw [k₂.1 lo (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hla, hld⟩),
        k₁.1 lo (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hla, hld⟩)]
    have h₂ : s₂.gpr hi = s.gpr hi := by
      rw [k₂.1 hi (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hha, hhd⟩),
        k₁.1 hi (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hha, hhd⟩)]
    rw [l₂, h₂] at e₃
    rw [r₁] at e₂
    omega_arith
  · have := (s₃.gpr .rbp).isLt
    have := (s₃.gpr lo).isLt; have := (s₃.gpr hi).isLt
    have := (s.gpr lo).isLt; have := (s.gpr hi).isLt
    have := (s₂.gpr .rax).isLt; have := (s₂.gpr .rdx).isLt
    omega_arith
  · exact ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))

/-! ## The doubling -/

/-- `dblChain .adc` on `FreshX` registers with the carry in: twice them. -/
theorem adcDblM_ok : ∀ (ts : List Reg) {s : State} {c : Bool}, s.cf = some c → FreshX ts →
    WP isa (.block (dblChain .adc ts)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' ts + 2 ^ (64 * ts.length) * c'.toNat = 2 * regsVal s ts + c.toNat ∧ Keeps ts s s'
  | [], s, c, hc, _ => WP.block_nil ⟨c, hc, by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, c, hc, hf => by
    rw [dblChain, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .adc t (.reg t)]) s (fun s₁ =>
        (s₁.gpr t).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (s.gpr t).toNat + (s.gpr t).toNat +
          c.toNat)).toNat = (s.gpr t).toNat + (s.gpr t).toNat + c.toNat ∧
        s₁.cf = some (decide (2 ^ 64 ≤ (s.gpr t).toNat + (s.gpr t).toNat + c.toNat)) ∧
        Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
        Option.map_some, hc, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
        Option.some.injEq, exists_eq_left']
      refine ⟨adc_carry _ _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    refine WP.mono (adcDblM_ok ts c₁ hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
    rw [hR] at e₂
    refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega_arith

/-- `op r, [d]` for `add` (no carry in) or `adc` (carry `c` in): the carry out in CF. -/
theorem opMem_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (r : Reg) {d : Nat}
    (hd : d + 8 ≤ size) {op : AluOp} {c : Bool} (hop : op = .add ∧ c = false ∨ op = .adc ∧ s.cf = some c) :
    WP isa (.block [.alu op r (.mem (sc d))]) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      (s'.gpr r).toNat + 2 ^ 64 * c'.toNat = (s.gpr r).toNat + (word s.mem base d).toNat + c.toNat ∧
      Keeps [r] s s' := by
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc_sc hs hd, Option.bind_some,
      RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
      exists_eq_left', Bool.toNat_false, Nat.add_zero]
    refine ⟨add_carry _ _, fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc_sc hs hd, hc, Option.bind_some,
      Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
      exists_eq_left']
    refine ⟨adc_carry _ _ _, fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]

/-- `op rax, rax` for `add` or `adc`: twice `rax`, with the carry in and out. -/
theorem dblRax_ok (s : State) {op : AluOp} {c : Bool} (hop : op = .add ∧ c = false ∨ op = .adc ∧ s.cf = some c) :
    WP isa (.block [.alu op .rax (.reg .rax)]) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      (s'.gpr .rax).toNat + 2 ^ 64 * c'.toNat = 2 * (s.gpr .rax).toNat + c.toNat ∧ Keeps [.rax] s s' := by
  rcases hop with ⟨rfl, rfl⟩ | ⟨rfl, hc⟩
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
      exists_eq_left', Bool.toNat_false, Nat.add_zero]
    refine ⟨by have := add_carry (s.gpr .rax) (s.gpr .rax); omega_arith, fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]
  · apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, hc, Option.bind_some,
      Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
      exists_eq_left']
    refine ⟨by have := adc_carry (s.gpr .rax) (s.gpr .rax) c; omega_arith, fun q hq => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]

/-- `adc r, x`: `r + x` with the carry in and out. -/
theorem adcReg_ok (s : State) {r x : Reg} {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .adc r (.reg x)]) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      (s'.gpr r).toNat + 2 ^ 64 * c'.toNat = (s.gpr r).toNat + (s.gpr x).toNat + c.toNat ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, hc, Option.bind_some,
    Option.map_some, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
    exists_eq_left']
  refine ⟨adc_carry _ _ _, fun q hq => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]

/-- `mov r32, 0`, `adc r, x` for `x` either `r` or `0`: the carry in `r`. -/
theorem capture_ok (s : State) (r : Reg) {x : Src} (hx : x = .reg r ∨ x = .imm 0) {c : Bool}
    (hc : s.cf = some c) :
    WP isa (.block [.mov32 r (.imm 0), .alu .adc r x]) s fun s' => (s'.gpr r).toNat = c.toNat ∧
      Keeps [r] s s' := by
  rw [show ([.mov32 r (.imm 0), .alu .adc r x] : List Instr) = [.mov32 r (.imm 0)] ++ [.alu .adc r x] from rfl,
    WP.block_append_iff]
  refine WP.mono (mov32zero_ok s r) fun s₁ ⟨z₁, cf₁, k₁⟩ => ?_
  apply WP.of_runBlock
  rcases hx with rfl | rfl
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, cf₁, hc, Option.bind_some,
      Option.map_some, RegUpd.gpr_setReg_self, z₁, Option.some.injEq, exists_eq_left']
    refine ⟨by cases c <;> rfl, (k₁.mono (by sub_regs)).trans ⟨fun q hq => ?_, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, cf₁, hc, Option.bind_some,
      Option.map_some, RegUpd.gpr_setReg_self, z₁, se0, Option.some.injEq, exists_eq_left']
    refine ⟨by cases c <;> rfl, (k₁.mono (by sub_regs)).trans ⟨fun q hq => ?_, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]

/-- `dblHalfM`: words 1 to 10 of the cross products doubled, the carry into `rcx`. -/
theorem dblHalfM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Nat} (ht : t + 24 ≤ size) :
    WP isa (.block (dblHalfM t)) s fun s' =>
      wordsVal s'.mem base (t + 8) 2 + 2 ^ 128 * regsVal s' [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] =
        2 * (wordsVal s.mem base (t + 8) 2 + 2 ^ 128 * regsVal s [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9]) ∧
      KeepRegs [.rax, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' ∧
      Outside base (t + 8) 16 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [dblHalfM, show ([.mov .rax (.mem (sc (t + 8))), .alu .add .rax (.reg .rax), .store (sc (t + 8)) .rax,
    .mov .rax (.mem (sc (t + 16))), .alu .adc .rax (.reg .rax), .store (sc (t + 16)) .rax] : List Instr) =
    [.mov .rax (.mem (sc (t + 8)))] ++ ([.alu .add .rax (.reg .rax)] ++ ([.store (sc (t + 8)) .rax] ++
    ([.mov .rax (.mem (sc (t + 16)))] ++ ([.alu .adc .rax (.reg .rax)] ++ [.store (sc (t + 16)) .rax])))) from rfl]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (movLoad_ok hs .rax (d := t + 8) (by omega_arith)) fun s₁ ⟨d₁, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dblRax_ok s₁ (op := .add) (c := false) (Or.inl ⟨rfl, rfl⟩)) fun s₂ ⟨c₂, cf₂, E2, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok hs₂ (d := t + 8) (by omega_arith) .rax) fun s₃ ⟨M₃, G₃, cf₃, _, rd₃, wr₃⟩ => ?_
  have hs₃ : Scr s₃ base size := ⟨by rw [G₃]; exact hs₂.rdi, wr₃ ▸ hs₂.wr, hs₂.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (movLoad_ok hs₃ .rax (d := t + 16) (by omega_arith)) fun s₄ ⟨d₄, cf₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dblRax_ok s₄ (op := .adc) (c := c₂) (Or.inr ⟨rfl, cf₄.trans (cf₃.trans cf₂)⟩))
    fun s₅ ⟨c₅, cf₅, E5, k₅⟩ => ?_
  have hs₅ := (hs₃.of_keeps k₄ (by decide)).of_keeps k₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok hs₅ (d := t + 16) (by omega_arith) .rax) fun s₆ ⟨M₆, G₆, cf₆, _, rd₆, wr₆⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcDblM_ok [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] (cf₆.trans cf₅) ⟨by decide, by decide⟩)
    fun s₇ ⟨c₇, cf₇, E7, k₇⟩ => ?_
  refine WP.mono (capture_ok s₇ .rcx (Or.inl rfl) cf₇) fun s₈ ⟨E8, k₈⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  have hm₅ : s₅.mem = s₃.mem := by rw [k₅.2.1, k₄.2.1]
  have hm₈ : s₈.mem = s₆.mem := by rw [k₈.2.1, k₇.2.1]
  have O₃ : Outside base (t + 8) 8 s.mem s₃.mem := by rw [M₃, hm₂]; exact writeW_outside _ _ _ (by omega_arith)
  have O₆ : Outside base (t + 16) 8 s₃.mem s₆.mem := by rw [M₆, hm₅]; exact writeW_outside _ _ _ (by omega_arith)
  have P6 : ∀ q, q ≠ .rax → s₆.gpr q = s.gpr q := fun q hq => by
    rw [G₆, k₅.1 q (by simpa using hq), k₄.1 q (by simpa using hq), G₃, k₂.1 q (by simpa using hq),
      k₁.1 q (by simpa using hq)]
  have hR6 : regsVal s₆ [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] =
      regsVal s [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] := regsVal_congr fun q hq => P6 q (by
        intro h; subst h; simp at hq)
  refine ⟨?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have hw : wordsVal s₈.mem base (t + 8) 2 = (s₂.gpr .rax).toNat + 2 ^ 64 * (s₅.gpr .rax).toNat := by
      simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
      rw [hm₈, M₆, show t + 8 + 8 = t + 16 from rfl, word_writeW_self,
        (writeW_outside s₅.mem base (d := t + 16) _ (by omega_arith)).word (by omega_arith) (by omega_arith), hm₅, M₃,
        word_writeW_self]
    have hw0 : wordsVal s.mem base (t + 8) 2 =
        (word s.mem base (t + 8)).toNat + 2 ^ 64 * (word s.mem base (t + 16)).toNat := by
      simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
    have h8 : regsVal s₈ [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] =
        regsVal s₇ [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] := regsVal_congr fun q hq => k₈.1 q (by
          intro h; simp only [List.mem_singleton] at h; subst h; simp at hq)
    rw [show ([.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] : List Reg) =
      [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] ++ [.rcx] from rfl, regsVal_append, h8, hw, hw0]
    rw [hR6, show ([.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] : List Reg).length = 8 from rfl] at E7
    rw [d₁] at E2
    rw [d₄, O₃.word (by omega_arith) (by omega_arith)] at E5
    have hc : regsVal s₈ [.rcx] = c₇.toNat := by simp only [regsVal, Nat.mul_zero, Nat.add_zero, E8]
    rw [hc]
    simp only [Bool.toNat_false, Nat.add_zero] at E2
    generalize (2 : Nat) ^ (64 * 8) = P at E7 ⊢
    generalize regsVal s₇ [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] = Y at E7 ⊢
    generalize regsVal s [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] = X at E7 ⊢
    omega_arith
  · rw [k₈.1 r (not_mem_of hr (by decide)), k₇.1 r (not_mem_of hr (by decide)), P6 r (fun h => hr (by rw [h]; decide))]
  · rw [k₈.2.2.1, k₇.2.2.1, rd₆, k₅.2.2.1, k₄.2.2.1, rd₃, k₂.2.2.1, k₁.2.2.1]
  · rw [k₈.2.2.2, k₇.2.2.2, wr₆, k₅.2.2.2, k₄.2.2.2, wr₃, k₂.2.2.2, k₁.2.2.2]
  · rw [hm₈]; exact (O₃.mono (by omega_arith) (by omega_arith)).trans (O₆.mono (by omega_arith) (by omega_arith))

/-- `sq01M`: `a₀²` and `a₁²` added at words 0 to 3, words 1 and 2 at `[t + 8]`,
word 3 in `r10`, the carry word out in `rbp`. -/
theorem sq01M_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t a : Nat}
    (ha : a + 48 ≤ size) (ht : t + 24 ≤ size) (hat : a + 48 ≤ t ∨ t + 24 ≤ a) :
    WP isa (.block (sq01M t a)) s fun s' =>
      wordsVal s'.mem base t 3 + 2 ^ 192 * (s'.gpr .r10).toNat + 2 ^ 256 * (s'.gpr .rbp).toNat =
        2 ^ 64 * wordsVal s.mem base (t + 8) 2 + 2 ^ 192 * (s.gpr .r10).toNat +
          (word s.mem base a).toNat * (word s.mem base a).toNat +
          2 ^ 128 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 8)).toNat) ∧
      (s'.gpr .rbp).toNat ≤ 1 ∧ KeepRegs [.rax, .rdx, .rbp, .r10] s s' ∧ Outside base t 24 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [sq01M, show ([.mov .rax (.mem (sc a)), .mul .rax, .store (sc t) .rax, .alu .add .rdx (.mem (sc (t + 8))),
    .store (sc (t + 8)) .rdx, .mov32 .rbp (.imm 0), .alu .adc .rbp (.imm 0),
    .mov .rax (.mem (sc (a + 8))), .mul .rax, .alu .add .rax (.reg .rbp), .alu .adc .rdx (.imm 0),
    .alu .add .rax (.mem (sc (t + 16))), .store (sc (t + 16)) .rax, .alu .adc .r10 (.reg .rdx),
    .mov32 .rbp (.imm 0), .alu .adc .rbp (.imm 0)] : List Instr) =
    [.mov .rax (.mem (sc a)), .mul .rax] ++ ([.store (sc t) .rax] ++ ([.alu .add .rdx (.mem (sc (t + 8)))] ++
    ([.store (sc (t + 8)) .rdx] ++ ([.mov32 .rbp (.imm 0), .alu .adc .rbp (.imm 0)] ++
    ([.mov .rax (.mem (sc (a + 8))), .mul .rax] ++ ([.alu .add .rax (.reg .rbp), .alu .adc .rdx (.imm 0)] ++
    ([.alu .add .rax (.mem (sc (t + 16)))] ++ ([.store (sc (t + 16)) .rax] ++ ([.alu .adc .r10 (.reg .rdx)] ++
    [.mov32 .rbp (.imm 0), .alu .adc .rbp (.imm 0)]))))))))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (sqLoad_ok hs (d := a) (by omega_arith)) fun s₉ ⟨E9, _, k₉⟩ => ?_
  have hs₉ := hs.of_keeps k₉ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok hs₉ (d := t) (by omega_arith) .rax) fun s₁₀ ⟨M₁₀, G₁₀, _, _, rd₁₀, wr₁₀⟩ => ?_
  have hs₁₀ : Scr s₁₀ base size := ⟨by rw [G₁₀]; exact hs₉.rdi, wr₁₀ ▸ hs₉.wr, hs₉.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (opMem_ok hs₁₀ .rdx (d := t + 8) (by omega_arith) (op := .add) (c := false) (Or.inl ⟨rfl, rfl⟩))
    fun s₁₁ ⟨c₁₁, cf₁₁, E11, k₁₁⟩ => ?_
  have hs₁₁ := hs₁₀.of_keeps k₁₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok hs₁₁ (d := t + 8) (by omega_arith) .rdx) fun s₁₂ ⟨M₁₂, G₁₂, cf₁₂, _, rd₁₂, wr₁₂⟩ => ?_
  have hs₁₂ : Scr s₁₂ base size := ⟨by rw [G₁₂]; exact hs₁₁.rdi, wr₁₂ ▸ hs₁₁.wr, hs₁₁.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (capture_ok s₁₂ .rbp (Or.inr rfl) (cf₁₂.trans cf₁₁)) fun s₁₃ ⟨E13, k₁₃⟩ => ?_
  have hs₁₃ := hs₁₂.of_keeps k₁₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqLoad_ok hs₁₃ (d := a + 8) (by omega_arith)) fun s₁₄ ⟨E14, b₁₄, k₁₄⟩ => ?_
  have hs₁₄ := hs₁₃.of_keeps k₁₄ (by decide)
  have r₁₄ : (s₁₄.gpr .rbp).toNat ≤ 1 := by
    rw [k₁₄.1 _ (by decide), E13]; exact Bool.toNat_le _
  rw [WP.block_append_iff]
  refine WP.mono (addWordM_ok s₁₄ b₁₄ r₁₄) fun s₁₅ ⟨E15, k₁₅⟩ => ?_
  have hs₁₅ := hs₁₄.of_keeps k₁₅ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (opMem_ok hs₁₅ .rax (d := t + 16) (by omega_arith) (op := .add) (c := false) (Or.inl ⟨rfl, rfl⟩))
    fun s₁₆ ⟨c₁₆, cf₁₆, E16, k₁₆⟩ => ?_
  have hs₁₆ := hs₁₅.of_keeps k₁₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st1_ok hs₁₆ (d := t + 16) (by omega_arith) .rax) fun s₁₇ ⟨M₁₇, G₁₇, cf₁₇, _, rd₁₇, wr₁₇⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (adcReg_ok s₁₇ (r := .r10) (x := .rdx) (cf₁₇.trans cf₁₆)) fun s₁₈ ⟨c₁₈, cf₁₈, E18, k₁₈⟩ => ?_
  refine WP.mono (capture_ok s₁₈ .rbp (Or.inr rfl) cf₁₈) fun s₁₉ ⟨E19, k₁₉⟩ => ?_
  -- Memory.
  have hm₁₁ : s₁₁.mem = s₁₀.mem := k₁₁.2.1
  have hm₁₆ : s₁₆.mem = s₁₂.mem := by rw [k₁₆.2.1, k₁₅.2.1, k₁₄.2.1, k₁₃.2.1]
  have hm₁₉ : s₁₉.mem = s₁₇.mem := by rw [k₁₉.2.1, k₁₈.2.1]
  have O₁₀ : Outside base t 8 s.mem s₁₀.mem := by rw [M₁₀, k₉.2.1]; exact writeW_outside _ _ _ (by omega_arith)
  have O₁₂ : Outside base (t + 8) 8 s₁₀.mem s₁₂.mem := by rw [M₁₂, hm₁₁]; exact writeW_outside _ _ _ (by omega_arith)
  have O₁₇ : Outside base (t + 16) 8 s₁₂.mem s₁₇.mem := by rw [M₁₇, hm₁₆]; exact writeW_outside _ _ _ (by omega_arith)
  have r₁₀ : word s₁₀.mem base (t + 8) = word s.mem base (t + 8) := O₁₀.word (by omega_arith) (by omega_arith)
  have r₁₅ : word s₁₅.mem base (t + 16) = word s.mem base (t + 16) := by
    rw [k₁₅.2.1, k₁₄.2.1, k₁₃.2.1, O₁₂.word (by omega_arith) (by omega_arith), O₁₀.word (by omega_arith) (by omega_arith)]
  have a₁₃ : word s₁₃.mem base (a + 8) = word s.mem base (a + 8) := by
    rw [k₁₃.2.1, O₁₂.word (by omega_using [hat]) (by omega_using [ha, hnw]),
      O₁₀.word (by omega_using [hat]) (by omega_using [ha, hnw])]
  have hw2 : word s₁₉.mem base (t + 16) = s₁₆.gpr .rax := by rw [hm₁₉, M₁₇, word_writeW_self]
  have hw1 : word s₁₉.mem base (t + 8) = s₁₁.gpr .rdx := by
    rw [hm₁₉, O₁₇.word (by omega_arith) (by omega_arith), M₁₂, word_writeW_self]
  have hw0 : word s₁₉.mem base t = s₉.gpr .rax := by
    rw [hm₁₉, O₁₇.word (by omega_arith) (by omega_arith), O₁₂.word (by omega_arith) (by omega_arith), M₁₀, word_writeW_self]
  have r10₁₇ : s₁₇.gpr .r10 = s.gpr .r10 := by
    rw [G₁₇, k₁₆.1 _ (by decide), k₁₅.1 _ (by decide), k₁₄.1 _ (by decide), k₁₃.1 _ (by decide), G₁₂,
      k₁₁.1 _ (by decide), G₁₀, k₉.1 _ (by decide)]
  have rdx₁₇ : s₁₇.gpr .rdx = s₁₅.gpr .rdx := by rw [G₁₇, k₁₆.1 _ (by decide)]
  refine ⟨?_, by rw [E19]; exact Bool.toNat_le _, ⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
    rw [hw0, hw1, show t + 8 + 8 = t + 16 from rfl, hw2, k₁₉.1 .r10 (by decide), E19]
    rw [r₁₀, G₁₀] at E11
    rw [k₁₄.1 .rbp (by decide), E13] at E15
    rw [r₁₅] at E16
    rw [r10₁₇, rdx₁₇] at E18
    rw [a₁₃] at E14
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 from rfl, show (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 from rfl,
      show (2 : Nat) ^ 256 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 from rfl]
    simp only [Bool.toNat_false, Nat.add_zero] at E11 E16
    have m11 := congrArg (2 ^ 64 * ·) E11
    have m14 := congrArg (2 ^ 64 * 2 ^ 64 * ·) E14
    have m15 := congrArg (2 ^ 64 * 2 ^ 64 * ·) E15
    have m16 := congrArg (2 ^ 64 * 2 ^ 64 * ·) E16
    have m18 := congrArg (2 ^ 64 * 2 ^ 64 * 2 ^ 64 * ·) E18
    generalize (2 : Nat) ^ 64 = B at *
    grind
  · rw [k₁₉.1 r (not_mem_of hr (by decide)), k₁₈.1 r (not_mem_of hr (by decide)), G₁₇,
      k₁₆.1 r (not_mem_of hr (by decide)), k₁₅.1 r (not_mem_of hr (by decide)),
      k₁₄.1 r (not_mem_of hr (by decide)), k₁₃.1 r (not_mem_of hr (by decide)), G₁₂,
      k₁₁.1 r (not_mem_of hr (by decide)), G₁₀, k₉.1 r (not_mem_of hr (by decide))]
  · rw [k₁₉.2.2.1, k₁₈.2.2.1, rd₁₇, k₁₆.2.2.1, k₁₅.2.2.1, k₁₄.2.2.1, k₁₃.2.2.1, rd₁₂, k₁₁.2.2.1, rd₁₀, k₉.2.2.1]
  · rw [k₁₉.2.2.2, k₁₈.2.2.2, wr₁₇, k₁₆.2.2.2, k₁₅.2.2.2, k₁₄.2.2.2, k₁₃.2.2.2, wr₁₂, k₁₁.2.2.2, wr₁₀, k₉.2.2.2]
  · rw [hm₁₉]
    exact ((O₁₀.mono (by omega_arith) (by omega_arith)).trans (O₁₂.mono (by omega_arith) (by omega_arith))).trans
      (O₁₇.mono (by omega_arith) (by omega_arith))

/-- The four squares' equations, weighted. -/
theorem sqSteps_arith {B r11 r12 r13 r14 r15 r8 r9 rc w11 w12 w13 w14 w15 w8 w9 wc k0 k2 k3 k4 k5 v2 v3 v4 v5 : Nat}
    (S2 : w11 + B * w12 + B * B * k2 = r11 + B * r12 + k0 + v2)
    (S3 : w13 + B * w14 + B * B * k3 = r13 + B * r14 + k2 + v3)
    (S4 : w15 + B * w8 + B * B * k4 = r15 + B * r8 + k3 + v4)
    (S5 : w9 + B * wc + B * B * k5 = r9 + B * rc + k4 + v5) :
    w11 + B * (w12 + B * (w13 + B * (w14 + B * (w15 + B * (w8 + B * (w9 + B * wc)))))) +
      B * B * B * B * B * B * B * B * k5 =
    r11 + B * (r12 + B * (r13 + B * (r14 + B * (r15 + B * (r8 + B * (r9 + B * rc)))))) + k0 +
      (v2 + B * B * (v3 + B * B * (v4 + B * B * v5))) := by
  have n3 := congrArg (B * B * ·) S3
  have n4 := congrArg (B * B * B * B * ·) S4
  have n5 := congrArg (B * B * B * B * B * B * ·) S5
  grind

/-- `sqStepsM`: `a₂²` to `a₅²` added at words 4 to 11 with the carry word in. -/
theorem sqStepsM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a + 48 ≤ size) (hb : (s.gpr .rbp).toNat ≤ 1) :
    WP isa (.block (sqStepsM a)) s fun s' =>
      regsVal s' [.r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] + 2 ^ (64 * 8) * (s'.gpr .rbp).toNat =
        regsVal s [.r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] + (s.gpr .rbp).toNat +
          sqSum s.mem base (a + 16) 4 ∧
      (s'.gpr .rbp).toNat ≤ 1 ∧
      Keeps [.rax, .rdx, .rbp, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] s s' := by
  rw [sqStepsM, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sqStepM_ok hs (d := a + 16) (by omega_arith) (lo := .r11) (hi := .r12) (by decide) hb)
    fun s₂₀ ⟨S2, b₂₀, k₂₀⟩ => ?_
  have hs₂₀ := hs.of_keeps k₂₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqStepM_ok hs₂₀ (d := a + 24) (by omega_arith) (lo := .r13) (hi := .r14) (by decide) b₂₀)
    fun s₂₁ ⟨S3, b₂₁, k₂₁⟩ => ?_
  have hs₂₁ := hs₂₀.of_keeps k₂₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqStepM_ok hs₂₁ (d := a + 32) (by omega_arith) (lo := .r15) (hi := .r8) (by decide) b₂₁)
    fun s₂₂ ⟨S4, b₂₂, k₂₂⟩ => ?_
  have hs₂₂ := hs₂₁.of_keeps k₂₂ (by decide)
  refine WP.mono (sqStepM_ok hs₂₂ (d := a + 40) (by omega_arith) (lo := .r9) (hi := .rcx) (by decide) b₂₂)
    fun s₂₃ ⟨S5, b₂₃, k₂₃⟩ => ⟨?_, b₂₃, ?_⟩
  · rw [k₂₀.2.1] at S3
    rw [k₂₁.2.1, k₂₀.2.1] at S4
    rw [k₂₂.2.1, k₂₁.2.1, k₂₀.2.1] at S5
    rw [k₂₀.1 .r13 (by decide), k₂₀.1 .r14 (by decide)] at S3
    rw [k₂₁.1 .r15 (by decide), k₂₁.1 .r8 (by decide), k₂₀.1 .r15 (by decide), k₂₀.1 .r8 (by decide)] at S4
    rw [k₂₂.1 .r9 (by decide), k₂₂.1 .rcx (by decide), k₂₁.1 .r9 (by decide), k₂₁.1 .rcx (by decide),
      k₂₀.1 .r9 (by decide), k₂₀.1 .rcx (by decide)] at S5
    rw [pow128 2] at S2 S3 S4 S5
    have key := sqSteps_arith S2 S3 S4 S5
    have p8 : (2 : Nat) ^ (64 * 8) = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by
      rw [show 64 * 8 = 64 + 64 + 64 + 64 + 64 + 64 + 64 + 64 from rfl]; simp only [Nat.pow_add]
    simp only [regsVal, sqSum, Nat.mul_zero, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd, pow128 2, p8]
    rw [k₂₃.1 .r11 (by decide), k₂₂.1 .r11 (by decide), k₂₁.1 .r11 (by decide), k₂₃.1 .r12 (by decide),
      k₂₂.1 .r12 (by decide), k₂₁.1 .r12 (by decide), k₂₃.1 .r13 (by decide), k₂₂.1 .r13 (by decide),
      k₂₃.1 .r14 (by decide), k₂₂.1 .r14 (by decide), k₂₃.1 .r15 (by decide), k₂₃.1 .r8 (by decide)]
    simp only [Nat.add_assoc] at key ⊢
    exact key
  · exact (((k₂₀.mono (by sub_regs)).trans (k₂₁.mono (by sub_regs))).trans (k₂₂.mono (by sub_regs))).trans
      (k₂₃.mono (by sub_regs))

/-- The three parts of `sqrDblM`, weighted. -/
theorem dblM_arith {B W1 W2 y10 Zs C1 X r10 k k' Z S4 v0 v1 : Nat}
    (H1 : W1 + B * B * (y10 + B * Zs) = 2 * (C1 + B * B * X))
    (H2 : W2 + B * B * B * r10 + B * B * B * B * k = B * W1 + B * B * B * y10 + v0 + B * B * v1)
    (H3 : Z + B * B * B * B * B * B * B * B * k' = Zs + k + S4) :
    W2 + B * B * B * (r10 + B * Z) + B * B * B * B * B * B * B * B * B * B * B * B * k' =
      2 * B * (C1 + B * B * X) + (v0 + B * B * (v1 + B * B * S4)) := by
  have m1 := congrArg (B * ·) H1
  have m3 := congrArg (B * B * B * B * ·) H3
  grind

/-- `sqrDblM`: as `sqrDbl_ok`. -/
theorem sqrDblM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t a : Nat}
    (ha : a + 48 ≤ size) (ht : t + 24 ≤ size) (hat : a + 48 ≤ t ∨ t + 24 ≤ a)
    (hC : 2 * 2 ^ 64 * (wordsVal s.mem base (t + 8) 2 +
      2 ^ 128 * regsVal s [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9]) + sqSum s.mem base a 6 <
      2 ^ (64 * 12)) :
    WP isa (.block (sqrDblM t a)) s fun s' =>
      wordsVal s'.mem base t 3 + 2 ^ (64 * 3) * regsVal s' [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] =
        2 * 2 ^ 64 * (wordsVal s.mem base (t + 8) 2 +
          2 ^ 128 * regsVal s [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9]) + sqSum s.mem base a 6 ∧
      KeepRegs [.rdx, .rcx, .rax, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' ∧
      Outside base t 24 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [sqrDblM, List.append_assoc, WP.block_append_iff]
  refine WP.mono (dblHalfM_ok hs ht) fun s₁ ⟨E1, K1, O1⟩ => ?_
  have hs₁ := hs.of_keepRegs K1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sq01M_ok hs₁ ha ht hat) fun s₂ ⟨E2, b₂, K2, O2⟩ => ?_
  have hs₂ := hs₁.of_keepRegs K2 (by decide)
  refine WP.mono (sqStepsM_ok hs₂ ha b₂) fun s₃ ⟨E3, b₃, k₃⟩ => ⟨?_, ?_, ?_⟩
  · -- The words of `[a]` the squares read.
    have wa : ∀ d, (d + 8 ≤ t ∨ t + 24 ≤ d) → d + 8 ≤ size → word s₂.mem base d = word s.mem base d :=
      fun d hd hd' => by rw [O2.word hd (by omega_arith), O1.word (by omega_arith) (by omega_arith)]
    have hS₂ : sqSum s₂.mem base (a + 16) 4 = sqSum s.mem base (a + 16) 4 := by
      simp only [sqSum, Nat.add_assoc, Nat.reduceAdd, wa (a + 16) (by omega_arith) (by omega_arith),
        wa (a + 24) (by omega_arith) (by omega_arith), wa (a + 32) (by omega_arith) (by omega_arith), wa (a + 40) (by omega_arith) (by omega_arith)]
    have w₁ : ∀ d, (d + 8 ≤ t ∨ t + 24 ≤ d) → d + 8 ≤ size → word s₁.mem base d = word s.mem base d :=
      fun d hd hd' => O1.word (by omega_arith) (by omega_arith)
    rw [w₁ a (by omega_arith) (by omega_arith), w₁ (a + 8) (by omega_arith) (by omega_arith)] at E2
    rw [hS₂] at E3
    -- The registers the parts pass on.
    have hZs : regsVal s₂ [.r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] =
        regsVal s₁ [.r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] := regsVal_congr fun q hq => K2.gpr q (by
          intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h hq
          rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            rcases h with h | h | h | h <;> cases h)
    rw [hZs] at E3
    have hY : regsVal s₁ [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] =
        (s₁.gpr .r10).toNat + 2 ^ 64 * regsVal s₁ [.r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] := rfl
    rw [hY] at E1
    have hR : regsVal s₃ [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] =
        (s₂.gpr .r10).toNat + 2 ^ 64 * regsVal s₃ [.r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] := by
      rw [show regsVal s₃ [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] =
        (s₃.gpr .r10).toNat + 2 ^ 64 * regsVal s₃ [.r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] from rfl,
        k₃.1 .r10 (by decide)]
    have hsq : sqSum s.mem base a 6 = (word s.mem base a).toNat * (word s.mem base a).toNat +
        2 ^ 128 * ((word s.mem base (a + 8)).toNat * (word s.mem base (a + 8)).toNat +
        2 ^ 128 * sqSum s.mem base (a + 16) 4) := rfl
    rw [hR, hsq, k₃.2.1, pow64x3 2, pow128 2]
    rw [hsq, pow128 2, pow64x12 2] at hC
    rw [pow128 2] at E1
    rw [show (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 from rfl,
      show (2 : Nat) ^ 256 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 from rfl, pow128 2] at E2
    have p8 : (2 : Nat) ^ (64 * 8) = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 * 2 ^ 64 := by
      rw [show 64 * 8 = 64 + 64 + 64 + 64 + 64 + 64 + 64 + 64 from rfl]; simp only [Nat.pow_add]
    rw [p8] at E3
    have key := dblM_arith E1 E2 E3
    generalize (2 : Nat) ^ 64 = B at hC key ⊢
    generalize B * B * B * B * B * B * B * B * B * B * B * B = Q at hC key
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp b₃ with h0 | h1
    · rw [h0, Nat.mul_zero, Nat.add_zero] at key
      exact key
    · rw [h1, Nat.mul_one] at key
      omega_arith
  · exact ⟨fun r hr => by
      rw [k₃.1 r (not_mem_of hr (by decide)), K2.gpr r (not_mem_of hr (by decide)),
        K1.gpr r (not_mem_of hr (by decide))],
      by rw [k₃.2.2.1, K2.rd, K1.rd], by rw [k₃.2.2.2, K2.wr, K1.wr]⟩
  · rw [k₃.2.1]
    exact (O1.mono (by omega_arith) (by omega_arith)).trans O2

/-! ## The cross products, with or without BMI2 and ADX -/

/-- Row 0 of the cross products, either way. -/
theorem row0'_ok (x : Bool) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a + 48 ≤ size) :
    WP isa (.block (sqrRow0' x a)) s fun s' => regsVal s' [.r8, .r9, .r10, .r11, .r12, .r13] =
          (word s.mem base a).toNat * wordsVal s.mem base (a + 8) 5 ∧
        Keeps [.rdx, .rbp, .rcx, .rax, .r8, .r9, .r10, .r11, .r12, .r13] s s' := by
  cases x
  · exact row0M_ok hs ha
  · exact WP.mono (row0_ok hs ha) fun s' ⟨e, k⟩ => ⟨e, k.mono (by sub_regs)⟩

/-- A row of the cross products, either way: `ts ++ [y] = ts + [d₀] · [d …]`. -/
theorem crossRow_ok (x : Bool) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n d₀ d : Nat}
    {ts : List Reg} {y : Reg} (hd₀ : d₀ + 8 ≤ size) (hd : d + 8 * (n + 1) ≤ size) (hl : ts.length = n + 1)
    (hf : Fresh (ts ++ [y]))
    (hb : regsVal s ts + (word s.mem base d₀).toNat * wordsVal s.mem base d (n + 1) < 2 ^ (64 * (n + 2))) :
    WP isa (.block (crossRow x d₀ ts y d)) s fun s' =>
      regsVal s' (ts ++ [y]) = regsVal s ts + (word s.mem base d₀).toNat * wordsVal s.mem base d (n + 1) ∧
      Keeps (.rdx :: .rbp :: .rcx :: .rax :: y :: ts) s s' := by
  cases x
  · simp only [crossRow, Bool.false_eq_true, ↓reduceIte]
    exact WP.mono (crossRowM_ok hs hd₀ (by rw [hl]; exact hd) hf) fun s' ⟨e, k⟩ => ⟨by rw [e, hl], k⟩
  · obtain ⟨t₀, ts', rfl⟩ : ∃ t₀ ts', ts = t₀ :: ts' := by
      cases ts with
      | nil => simp at hl
      | cons t₀ ts' => exact ⟨t₀, ts', rfl⟩
    have hl' : ts'.length = n := by simpa using hl
    have htk : (ts' ++ [y]).take n = ts' := List.take_left' hl'
    simp only [crossRow, ↓reduceIte, List.cons_append]
    have hb' : regsVal s (t₀ :: (ts' ++ [y]).take n) + (word s.mem base d₀).toNat * wordsVal s.mem base d (n + 1) <
        2 ^ (64 * (n + 2)) := by rw [htk]; exact hb
    refine WP.mono (rowM_ok hs hd₀ hd (x := t₀) (rs := ts' ++ [y]) (by simp [hl']) (by
      rw [← List.cons_append]; exact hf) hb') fun s' ⟨e, k⟩ => ⟨?_, k.mono (by sub_regs)⟩
    rw [htk] at e
    exact e

theorem sqrRowsG_eq (x : Bool) (a : Nat) : sqrRows x a =
    crossRow x (a + 8) [.r10, .r11, .r12, .r13] .r14 (a + 16) ++
    (crossRow x (a + 16) [.r12, .r13, .r14] .r15 (a + 24) ++
    (crossRow x (a + 24) [.r14, .r15] .r8 (a + 32) ++ crossRow x (a + 32) [.r8] .r9 (a + 40))) := by
  simp only [sqrRows, List.append_assoc]

/-- The cross products: words 1 and 2 at `[t + 8]`, words 3 to 10 in `r10–r15`,
`r8`, `r9`. -/
theorem sqCrossG_ok (x : Bool) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t a : Nat}
    (ha : a + 48 ≤ size) (ht : t + 24 ≤ size) (hat : a + 48 ≤ t + 8 ∨ t + 24 ≤ a) :
    WP isa (.block (sqrRow0' x a ++ (stores ([.r8, .r9] : List Reg) (t + 8) ++ sqrRows x a))) s fun s' =>
      wordsVal s'.mem base (t + 8) 2 + 2 ^ 128 * regsVal s' [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9] =
        crossVal s.mem base a ∧
      KeepRegs [.rdx, .rbp, .rcx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' ∧
      Outside base (t + 8) 16 s.mem s'.mem := by
  have hnw := hs.nowrap
  have t₀ := mul_word_le (word s.mem base a).isLt (wordsVal_lt s.mem base (a + 8) 5)
  have t₁ := mul_word_le (word s.mem base (a + 8)).isLt (wordsVal_lt s.mem base (a + 16) 4)
  have t₂ := mul_word_le (word s.mem base (a + 16)).isLt (wordsVal_lt s.mem base (a + 24) 3)
  have t₃ := mul_word_le (word s.mem base (a + 24)).isLt (wordsVal_lt s.mem base (a + 32) 2)
  have t₄ := mul_word_le (word s.mem base (a + 32)).isLt (wordsVal_lt s.mem base (a + 40) 1)
  rw [WP.block_append_iff]
  refine WP.mono (row0'_ok x hs ha) fun s₀ h₀ => ?_
  obtain ⟨e₀, k₀⟩ := h₀
  have hs₀ := hs.of_keeps k₀ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok [.r8, .r9] hs₀ (o := t + 8) (by simp only [List.length_cons, List.length_nil]; omega_arith)
    (by decide)) fun s₁ h₁ => ?_
  obtain ⟨e₁', k₁', O₁⟩ := h₁
  have hs₁ := hs₀.of_keepRegs k₁' (by decide)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at e₁' O₁
  rw [k₀.2.1] at O₁
  -- The words the rows read, unchanged by the store.
  have w₁ : word s₁.mem base (a + 8) = word s.mem base (a + 8) := O₁.word (by omega_arith) (by omega_arith)
  have w₂ : word s₁.mem base (a + 16) = word s.mem base (a + 16) := O₁.word (by omega_arith) (by omega_arith)
  have w₃ : word s₁.mem base (a + 24) = word s.mem base (a + 24) := O₁.word (by omega_arith) (by omega_arith)
  have w₄ : word s₁.mem base (a + 32) = word s.mem base (a + 32) := O₁.word (by omega_arith) (by omega_arith)
  have W₁ : wordsVal s₁.mem base (a + 16) 4 = wordsVal s.mem base (a + 16) 4 := O₁.wordsVal (by omega_arith) (by omega_arith)
  have W₂ : wordsVal s₁.mem base (a + 24) 3 = wordsVal s.mem base (a + 24) 3 := O₁.wordsVal (by omega_arith) (by omega_arith)
  have W₃ : wordsVal s₁.mem base (a + 32) 2 = wordsVal s.mem base (a + 32) 2 := O₁.wordsVal (by omega_arith) (by omega_arith)
  have W₄ : wordsVal s₁.mem base (a + 40) 1 = wordsVal s.mem base (a + 40) 1 := O₁.wordsVal (by omega_arith) (by omega_arith)
  have g₁ : ∀ r, s₁.gpr r = s₀.gpr r := fun r => k₁'.gpr r (by simp)
  rw [sqrRowsG_eq, WP.block_append_iff]
  have hb₁ : regsVal s₁ [.r10, .r11, .r12, .r13] + (word s₁.mem base (a + 8)).toNat *
      wordsVal s₁.mem base (a + 16) 4 < 2 ^ (64 * (3 + 2)) := by
    rw [w₁, W₁]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, g₁] at e₀ ⊢
    have := (s₀.gpr .r8).isLt; have := (s₀.gpr .r9).isLt
    omega_arith
  refine WP.mono (crossRow_ok x hs₁ (n := 3) (ts := [.r10, .r11, .r12, .r13]) (y := .r14) (by omega_arith) (by omega_arith) rfl ⟨by decide, by decide⟩ hb₁) fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂⟩ := h₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [w₁, W₁] at e₂
  rw [WP.block_append_iff]
  have hb₂ : regsVal s₂ [.r12, .r13, .r14] + (word s₂.mem base (a + 16)).toNat *
      wordsVal s₂.mem base (a + 24) 3 < 2 ^ (64 * (2 + 2)) := by
    rw [k₂.2.1, w₂, W₂]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, List.cons_append, List.nil_append, Nat.reduceAdd, g₁] at e₀ e₂ ⊢
    have := (s₀.gpr .r8).isLt; have := (s₀.gpr .r9).isLt
    have := (s₂.gpr .r10).isLt; have := (s₂.gpr .r11).isLt
    omega_arith
  refine WP.mono (crossRow_ok x hs₂ (n := 2) (ts := [.r12, .r13, .r14]) (y := .r15) (by omega_arith) (by omega_arith) rfl ⟨by decide, by decide⟩ hb₂) fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃⟩ := h₃
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [k₂.2.1, w₂, W₂] at e₃
  rw [WP.block_append_iff]
  have hb₃ : regsVal s₃ [.r14, .r15] + (word s₃.mem base (a + 24)).toNat *
      wordsVal s₃.mem base (a + 32) 2 < 2 ^ (64 * (1 + 2)) := by
    rw [k₃.2.1, k₂.2.1, w₃, W₃]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, List.cons_append, List.nil_append, Nat.reduceAdd, g₁] at e₀ e₂ e₃ ⊢
    have := (s₀.gpr .r8).isLt; have := (s₀.gpr .r9).isLt
    have := (s₂.gpr .r10).isLt; have := (s₂.gpr .r11).isLt
    have := (s₃.gpr .r12).isLt; have := (s₃.gpr .r13).isLt
    omega_arith
  refine WP.mono (crossRow_ok x hs₃ (n := 1) (ts := [.r14, .r15]) (y := .r8) (by omega_arith) (by omega_arith) rfl ⟨by decide, by decide⟩ hb₃) fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄⟩ := h₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [k₃.2.1, k₂.2.1, w₃, W₃] at e₄
  have hb₄ : regsVal s₄ [.r8] + (word s₄.mem base (a + 32)).toNat *
      wordsVal s₄.mem base (a + 40) 1 < 2 ^ (64 * (0 + 2)) := by
    rw [k₄.2.1, k₃.2.1, k₂.2.1, w₄, W₄]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero, List.cons_append, List.nil_append, Nat.reduceAdd, g₁] at e₀ e₂ e₃ e₄ ⊢
    have := (s₀.gpr .r8).isLt; have := (s₀.gpr .r9).isLt
    have := (s₂.gpr .r10).isLt; have := (s₂.gpr .r11).isLt
    have := (s₃.gpr .r12).isLt; have := (s₃.gpr .r13).isLt
    have := (s₄.gpr .r14).isLt; have := (s₄.gpr .r15).isLt
    omega_arith
  refine WP.mono (crossRow_ok x hs₄ (n := 0) (ts := [.r8]) (y := .r9) (by omega_arith) (by omega_arith) rfl ⟨by decide, by decide⟩ hb₄) fun s₅ h₅ => ?_
  obtain ⟨e₅, k₅⟩ := h₅
  rw [k₄.2.1, k₃.2.1, k₂.2.1, w₄, W₄] at e₅
  have K : KeepRegs [.rdx, .rbp, .rcx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s₅ := by
    clear t₀ t₁ t₂ t₃ t₄ hb₁ hb₂ hb₃ hb₄ e₀ e₂ e₃ e₄ e₅
    exact ⟨fun r hr => by
        rw [k₅.1 r (not_mem_of hr (by decide)), k₄.1 r (not_mem_of hr (by decide)),
          k₃.1 r (not_mem_of hr (by decide)), k₂.1 r (not_mem_of hr (by decide)), g₁,
          k₀.1 r (not_mem_of hr (by decide))],
      by rw [k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁'.rd, k₀.2.2.1],
      by rw [k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁'.wr, k₀.2.2.2]⟩
  have m₅ : s₅.mem = s₁.mem := by rw [k₅.2.1, k₄.2.1, k₃.2.1, k₂.2.1]
  refine ⟨?_, K, by rw [m₅]; exact O₁⟩
  rw [m₅, e₁']
  simp only [regsVal, Nat.mul_zero, Nat.add_zero, List.cons_append, List.nil_append, g₁] at e₀ e₂ e₃ e₄ e₅ ⊢
  rw [k₅.1 .r10 (by decide), k₄.1 .r10 (by decide), k₃.1 .r10 (by decide),
    k₅.1 .r11 (by decide), k₄.1 .r11 (by decide), k₃.1 .r11 (by decide),
    k₅.1 .r12 (by decide), k₄.1 .r12 (by decide), k₅.1 .r13 (by decide), k₄.1 .r13 (by decide),
    k₅.1 .r14 (by decide), k₅.1 .r15 (by decide)]
  simp only [crossVal]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by rfl]
  exact sqCross_arith e₀ e₂ e₃ e₄ e₅


/-! ## The reductions -/

/-- A round of the reduction on six words, either way. -/
theorem redShort_ok (x : Bool) {s : State} {d0 d1 d2 d3 d4 d5 : Reg} (hf : Fresh [d0, d1, d2, d3, d4, d5]) {m : Nat}
    (hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319) :
    WP isa (.block (redShort x [d0, d1, d2, d3, d4, d5])) s fun s' =>
      (∃ u, u < 2 ^ 64 ∧ 2 ^ 64 * regsVal s' [d1, d2, d3, d4, d5, d0] =
        regsVal s [d0, d1, d2, d3, d4, d5] + u * m) ∧
      Keeps [.rax, .rcx, .rdx, .rbp, d0, d1, d2, d3, d4, d5] s s' := by
  cases x
  · exact redShortM_ok hf hm
  · exact redShortX_ok hf hm


/-- P-384's `p` against `2³⁸⁴`. -/
theorem p384_bounds {m : Nat}
    (hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319) :
    m < 2 ^ (64 * 6) ∧ 2 ^ (64 * 6) ≤ 2 ^ 64 * m := by
  rw [pow_split 2 (64 * 3) (64 * 3) (64 * 6) rfl]
  subst hm; omega_arith

/-- The window of round `i`, word by word. -/
theorem sqWins_eq (i : Nat) : sqWins i = [sqW i 0, sqW i 1, sqW i 2, sqW i 3, sqW i 4, sqW i 5] := rfl

/-- The next round's window: the words rotated by one. -/
theorem sqWins_succ (i : Nat) : sqWins (i + 1) = [sqW i 1, sqW i 2, sqW i 3, sqW i 4, sqW i 5, sqW i 0] := by
  simp only [sqWins_eq, sqW]
  have e : ∀ j, (i + 1 + j) % 6 = (i + (j + 1)) % 6 := fun j => by rw [Nat.add_right_comm, Nat.add_assoc]
  rw [e 0, e 1, e 2, e 3, e 4, show (i + 1 + 5) % 6 = (i + 0) % 6 by omega_arith]

theorem sqW_mod (i j : Nat) : sqW i j = sqW (i % 6) j := by
  unfold sqW; rw [show (i + j) % 6 = (i % 6 + j) % 6 by omega_arith]

theorem sqWins_mod (i : Nat) : sqWins i = sqWins (i % 6) := by
  rw [sqWins_eq, sqWins_eq, sqW_mod i 0, sqW_mod i 1, sqW_mod i 2, sqW_mod i 3, sqW_mod i 4, sqW_mod i 5]

theorem six_cases {k : Nat} (h : k < 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega_arith

theorem fresh_sqWins (i : Nat) : Fresh (sqWins i) := by
  rw [sqWins_mod]
  rcases six_cases (Nat.mod_lt i (by decide : 6 > 0)) with h | h | h | h | h | h <;> rw [h] <;>
    exact ⟨by decide, by decide⟩

/-- Every window is `sqWin6`'s registers. -/
theorem sqWins_sub (i : Nat) : ∀ q ∈ sqWins i, q ∈ sqWin6 := by
  rw [sqWins_mod]
  rcases six_cases (Nat.mod_lt i (by decide : 6 > 0)) with h | h | h | h | h | h <;> rw [h] <;> decide

/-- `k` of P-384's reductions on six words from `sqWin6`, from `T < 2³⁸⁴`:
`2^(64k) T' = T + U p` with `U < 2^(64k)`, and `T' < 2³⁸⁴`. -/
theorem redsShort_ok (x : Bool) {m : Nat}
    (hm : m = 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319) :
    ∀ k {s : State}, regsVal s (sqWins 0) < 2 ^ (64 * 6) →
      WP isa (.block (redsShort x k)) s fun s' =>
        (∃ U, U < 2 ^ (64 * k) ∧ 2 ^ (64 * k) * regsVal s' (sqWins k) = regsVal s (sqWins 0) + U * m) ∧
        regsVal s' (sqWins k) < 2 ^ (64 * 6) ∧
        Keeps (.rax :: .rcx :: .rdx :: .rbp :: sqWin6) s s'
  | 0, s, h0 => WP.block_nil ⟨⟨0, by simp⟩, h0, fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, s, h0 => by
    obtain ⟨hm1, hm2⟩ := p384_bounds hm
    rw [redsShort, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (redsShort_ok x hm k h0) fun s₁ h₁ => ?_
    obtain ⟨⟨U, hU, eU⟩, hT, k₁⟩ := h₁
    have hf := fresh_sqWins k
    rw [sqWins_eq] at hf hT
    rw [sqWins_eq]
    refine WP.mono (redShort_ok x hf hm) fun s₂ h₂ => ?_
    obtain ⟨⟨u, hu, eu⟩, k₂⟩ := h₂
    rw [← sqWins_succ] at eu
    rw [← sqWins_eq] at hT eu
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_, ?_⟩, ?_, k₁.trans (k₂.mono fun q hq => ?_)⟩
    · have : 2 ^ (64 * k) * u ≤ 2 ^ (64 * k) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega_arith)
      rw [Nat.mul_succ, Nat.pow_add]
      rw [Nat.mul_sub_one] at this
      omega_arith
    · calc 2 ^ (64 * (k + 1)) * regsVal s₂ (sqWins (k + 1))
          = 2 ^ (64 * k) * (2 ^ 64 * regsVal s₂ (sqWins (k + 1))) := by
            rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ (64 * k) * regsVal s₁ (sqWins k) + 2 ^ (64 * k) * u * m := by
            rw [eu, Nat.mul_add, Nat.mul_assoc]
        _ = _ := by rw [eU, Nat.add_mul]; omega_arith
    · have hm1' := hm1
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ 64) ?_
      rw [eu]
      generalize (2 : Nat) ^ (64 * 6) = Q at hT hm1' ⊢
      generalize (2 : Nat) ^ 64 = B at hu ⊢
      have h1 : u * m ≤ (B - 1) * Q := Nat.mul_le_mul (by omega_arith) (Nat.le_of_lt hm1')
      have h2 : (B - 1) * Q + Q = B * Q := by
        rw [Nat.sub_one_mul]; have : Q ≤ B * Q := Nat.le_mul_of_pos_left Q (by omega_arith); omega_arith
      omega_arith
    · simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (sqWins_sub k q (by rw [sqWins_eq]; simp only [List.mem_cons]; exact h)))))

/-! ## The squaring -/

/-- The cross products doubled and the squares added, either way. -/
theorem sqrDbl'_ok (x : Bool) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t a : Nat}
    (ha : a + 48 ≤ size) (ht : t + 24 ≤ size) (hat : a + 48 ≤ t ∨ t + 24 ≤ a)
    (hC : 2 * 2 ^ 64 * (wordsVal s.mem base (t + 8) 2 +
      2 ^ 128 * regsVal s [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9]) + sqSum s.mem base a 6 <
      2 ^ (64 * 12)) :
    WP isa (.block (sqrDbl' x t a)) s fun s' =>
      wordsVal s'.mem base t 3 + 2 ^ (64 * 3) * regsVal s' [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] =
        2 * 2 ^ 64 * (wordsVal s.mem base (t + 8) 2 +
          2 ^ 128 * regsVal s [.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9]) + sqSum s.mem base a 6 ∧
      KeepRegs [.rdx, .rcx, .rax, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' ∧
      Outside base t 24 s.mem s'.mem := by
  cases x
  · exact sqrDblM_ok hs ha ht hat hC
  · exact sqrDbl_ok hs ha ht hat hC


/-- The values of `[a]` in memories that agree on its words. -/
theorem vals_congr {m m' : Mem} {base : Addr} {a : Nat}
    (h : ∀ i, i < 6 → word m' base (a + 8 * i) = word m base (a + 8 * i)) :
    crossVal m' base a = crossVal m base a ∧ sqSum m' base a 6 = sqSum m base a 6 ∧
      wordsVal m' base a 6 = wordsVal m base a 6 := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reduceMul] at h0 h1 h2 h3 h4 h5
  simp only [crossVal, sqSum, wordsVal, Nat.add_assoc, Nat.reduceAdd, h0, h1, h2, h3, h4, h5]
  exact ⟨trivial, trivial, trivial⟩

/-- `A² < 2⁷⁶⁸` for `A < 2³⁸⁴`. -/
theorem sq_lt {A : Nat} (h : A < 2 ^ (64 * 6)) : A * A < 2 ^ (64 * 12) := by
  rw [pow_split 2 (64 * 6) (64 * 6) (64 * 12) rfl]
  generalize 2 ^ (64 * 6) = P at h ⊢
  exact Nat.mul_lt_mul'' h h

/-- The end of `sqrS`: `2³⁸⁴ V = L + U p` and `[a]² = L + 2³⁸⁴ H` make
`V ≤ p`, `H < p`, and `(V + H) mod p` the result. -/
theorem final_arith {Q L U V H AA m : Nat} (hQ : 0 < Q) (eV : Q * V = L + U * m) (hU : U < Q)
    (hL : L < Q) (eA : AA = L + Q * H) (hA : AA < m * m) (hm : m < Q) :
    V ≤ m ∧ H < m ∧ (V + H) % m * Q % m = AA % m := by
  have hV : V ≤ m := by
    have : Q * V < Q * (m + 1) := by
      rw [eV, Nat.mul_add, Nat.mul_one]
      have : U * m ≤ Q * m - m := by
        have := Nat.mul_le_mul_right m (Nat.le_pred_of_lt hU)
        rw [Nat.pred_eq_sub_one, Nat.sub_one_mul] at this
        exact this
      have : m ≤ Q * m := Nat.le_mul_of_pos_left m hQ
      omega_arith
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left this)
  have hH : H < m := by
    have : Q * H < Q * m := by
      have : m * m ≤ Q * m := Nat.mul_le_mul_right m (Nat.le_of_lt hm)
      omega_arith
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨hV, hH, ?_⟩
  rw [Nat.mod_mul_mod, Nat.add_mul, Nat.mul_comm V, Nat.mul_comm H, eV, eA, Nat.add_right_comm,
    Nat.add_mul_mod_self_right]

theorem sqrS_eq (M : Mod) (o a : Nat) : sqrS M o a =
    (sqrRow0' M.adx a ++ (stores ([.r8, .r9] : List Reg) (M.tmp + 8) ++ sqrRows M.adx a)) ++ (sqrDbl' M.adx M.tmp a ++
    (stores sqHigh6 o ++ (loads ([.r13, .r14, .r15] : List Reg) M.tmp ++ (redsShort M.adx 6 ++
    (([.mov32 .r8 (.imm 0)] : List Instr) ++ (chain .add .adc sqWin6 o ++
    (([.alu .adc .r8 (.imm 0)] : List Instr) ++ (csub M sqWin6 .r8 ++ stores sqWin6 o)))))))) := by
  simp only [sqrS, sqrSA, List.append_assoc]

theorem sqrSA_eq (M : Mod) (o a : Nat) : sqrSA M o a =
    (sqrRow0' M.adx a ++ (stores ([.r8, .r9] : List Reg) (M.tmp + 8) ++ sqrRows M.adx a)) ++ (sqrDbl' M.adx M.tmp a ++
    (stores sqHigh6 o ++ (loads ([.r13, .r14, .r15] : List Reg) M.tmp ++ (redsShort M.adx 6 ++
    (([.mov32 .r8 (.imm 0)] : List Instr) ++ (chain .add .adc sqWin6 o ++
    ([.alu .adc .r8 (.imm 0)] : List Instr))))))) := by
  simp only [sqrSA, List.append_assoc]

/-- `sqrSA`: `[a]²` with its low half reduced and its high half added, `W < 2p` with
`W R ≡ [a]² (mod p)`, in `sqWin6` and `r8`. -/
theorem sqrSA_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hmP : m =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
    (htmp : M.tmp + 48 ≤ size) {o a : Nat} (ho : o + 48 ≤ size)
    (ha : a + 48 ≤ size) (hoT : o + 48 ≤ M.tmp ∨ M.tmp + 48 ≤ o)
    (haT : a + 48 ≤ M.tmp ∨ M.tmp + 48 ≤ a) (hA : wordsVal s.mem base a 6 < m) :
    WP isa (.block (sqrSA M o a)) s fun s' =>
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) →
        (ofs base x < M.tmp ∨ M.tmp + 48 ≤ ofs base x) → s'.mem x = s.mem x) ∧
      (∀ d, d + 48 ≤ size → (d + 48 ≤ o ∨ o + 48 ≤ d) → (d + 48 ≤ M.tmp ∨ M.tmp + 48 ≤ d) →
        wordsVal s'.mem base d 6 = wordsVal s.mem base d 6) ∧
      regsVal s' sqWin6 + 2 ^ (64 * 6) * (s'.gpr .r8).toNat < 2 * m ∧
      (regsVal s' sqWin6 + 2 ^ (64 * 6) * (s'.gpr .r8).toNat) % m * 2 ^ (64 * 6) % m =
        wordsVal s.mem base a 6 * wordsVal s.mem base a 6 % m := by
  obtain ⟨hm1, -⟩ := p384_bounds hmP
  have hnw := hs.nowrap
  rw [sqrSA_eq]
  -- The cross products, words 1 and 2 at `[tmp + 8]`.
  rw [WP.block_append_iff]
  refine WP.mono (sqCrossG_ok M.adx hs (t := M.tmp) ha (by omega_arith) (by omega_arith)) fun s₁ h₁ => ?_
  obtain ⟨e₁, k₁, O₁⟩ := h₁
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain ⟨hc₁, hq₁, hv₁⟩ := vals_congr (m := s₁.mem) (m' := s.mem) (a := a) (base := base)
    (fun i hi => (O₁.word (d := a + 8 * i) (by omega_arith) (by omega_arith)).symm)
  have hAA := sq_eq s.mem base a
  have hAl := sq_lt (Nat.lt_trans hA hm1)
  -- The square, words 0 to 2 at `[tmp]`.
  rw [WP.block_append_iff]
  refine WP.mono (sqrDbl'_ok M.adx hs₁ (t := M.tmp) ha (by omega_arith) (by omega_arith)
    (by rw [e₁, ← hq₁, ← hAA]; exact hAl)) fun s₂ h₂ => ?_
  obtain ⟨e₂, k₂, O₂⟩ := h₂
  rw [e₁, ← hq₁, ← hAA] at e₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- The high half to `[o]`.
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok sqHigh6 hs₂ (o := o) (by simp only [sqHigh6, List.length_cons, List.length_nil]; omega_arith)
    (by decide)) fun s₃ h₃ => ?_
  obtain ⟨e₃, k₃, O₃⟩ := h₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  simp only [show sqHigh6.length = 6 from rfl, Nat.reduceMul] at e₃ O₃
  -- The low words into the window `sqWin6`.
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok [.r13, .r14, .r15] hs₃ (a := M.tmp) (by simp only [List.length_cons, List.length_nil]; omega_arith)
    ⟨by decide, by decide⟩) fun s₄ h₄ => ?_
  obtain ⟨e₄, k₄⟩ := h₄
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  -- `[a]² = L + 2³⁸⁴ H` for the low half `L` in the window and the high half `H` at `[o]`.
  have hL : regsVal s₄ (sqWins 0) = wordsVal s₂.mem base M.tmp 3 + 2 ^ (64 * 3) *
      regsVal s₂ [.r10, .r11, .r12] := by
    have h3 : regsVal s₄ [.r10, .r11, .r12] = regsVal s₂ [.r10, .r11, .r12] :=
      regsVal_congr fun q hq => by
        rw [k₄.1 q (by
          intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h hq
          rcases hq with rfl | rfl | rfl <;> rcases h with h | h | h <;> cases h), k₃.gpr q (by simp)]
    have hw : regsVal s₄ [.r13, .r14, .r15] = wordsVal s₂.mem base M.tmp 3 := by
      rw [e₄]
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
      exact O₃.wordsVal (by omega_arith) (by omega_arith)
    rw [show sqWins 0 = [.r13, .r14, .r15] ++ [.r10, .r11, .r12] from rfl, regsVal_append, hw, h3,
      show ([Reg.r13, .r14, .r15] : List Reg).length = 3 from rfl]
  have hAH : wordsVal s.mem base a 6 * wordsVal s.mem base a 6 =
      regsVal s₄ (sqWins 0) + 2 ^ (64 * 3) * 2 ^ (64 * 3) * wordsVal s₃.mem base o 6 := by
    rw [← e₂, hL, e₃, show ([.r10, .r11, .r12, .r13, .r14, .r15, .r8, .r9, .rcx] : List Reg) =
      [.r10, .r11, .r12] ++ sqHigh6 from rfl, regsVal_append,
      show ([Reg.r10, .r11, .r12] : List Reg).length = 3 from rfl, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
  rw [← pow_split 2 (64 * 3) (64 * 3) (64 * 6) rfl] at hAH
  have hLt : regsVal s₄ (sqWins 0) < 2 ^ (64 * 6) := by
    have := regsVal_lt s₄ (sqWins 0)
    rw [show (sqWins 0).length = 6 from rfl] at this
    exact this
  -- The reductions.
  rw [WP.block_append_iff]
  refine WP.mono (redsShort_ok M.adx hmP 6 hLt) fun s₆ h₆ => ?_
  obtain ⟨⟨U, hU, eU⟩, -, k₆⟩ := h₆
  have hs₆ := hs₄.of_keeps k₆ (by decide)
  have hAA' := Nat.mul_lt_mul'' hA hA
  generalize hQd : 2 ^ (64 * 6) = Q at eU hU hLt hAH hm1
  have hQ : 0 < Q := by omega_arith
  obtain ⟨hV6, hH, hres⟩ := final_arith hQ eU hU hLt hAH hAA' hm1
  rw [show sqWins 6 = sqWin6 from rfl] at hV6 hres
  -- The carry word.
  rw [WP.block_append_iff]
  refine WP.mono (mov32zero_ok s₆ .r8) fun s₇ h₇ => ?_
  obtain ⟨z₇, -, k₇⟩ := h₇
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  have hlow₇ : regsVal s₇ sqWin6 = regsVal s₆ sqWin6 := regsVal_congr fun q hq => k₇.1 q (by
    intro h; simp only [sqWin6, List.mem_cons, List.not_mem_nil, or_false] at h hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases h)
  -- The high half added.
  rw [WP.block_append_iff]
  refine WP.mono (chainAdd_ok hs₇ (t := .r13) (ts := [.r14, .r15, .r10, .r11, .r12]) (b := o)
    (by simp only [List.length_cons, List.length_nil]; omega_arith) ⟨by decide, by decide⟩) fun s₈ h₈ => ?_
  obtain ⟨c₈, cf₈, e₈, k₈⟩ := h₈
  have hs₈ := hs₇.of_keeps k₈ (by decide)
  rw [show (Reg.r13 :: [.r14, .r15, .r10, .r11, .r12] : List Reg) = sqWin6 from rfl, k₇.2.1, k₆.2.1, m₄,
    hlow₇] at e₈
  simp only [show sqWin6.length = 6 from rfl, hQd] at e₈
  refine WP.mono (adcZero_ok s₈ .r8 cf₈ (by rw [k₈.1 _ (by decide), z₇])) fun s₉ h₉ => ?_
  obtain ⟨e₉, k₉⟩ := h₉
  have hs₉ := hs₈.of_keeps k₉ (by decide)
  have hlow₉ : regsVal s₉ sqWin6 = regsVal s₈ sqWin6 := regsVal_congr fun q hq => k₉.1 q (by
    intro h; simp only [sqWin6, List.mem_cons, List.not_mem_nil, or_false] at h hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases h)
  have m₉ : s₉.mem = s₃.mem := by rw [k₉.2.1, k₈.2.1, k₇.2.1, k₆.2.1, m₄]
  have hW : regsVal s₉ sqWin6 + Q * (s₉.gpr .r8).toNat =
      regsVal s₆ sqWin6 + wordsVal s₃.mem base o 6 := by
    rw [hlow₉, e₉]; omega_arith
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun x hx hx' => ?_, fun d hd hdo hdt => ?_, ?_, ?_⟩
  · rw [k₉.1 r (not_mem_of hr (by decide)),
      k₈.1 r (not_mem_of hr (by decide)), k₇.1 r (not_mem_of hr (by decide)), k₆.1 r (not_mem_of hr (by decide)),
      k₄.1 r (not_mem_of hr (by decide)), k₃.gpr r (by simp),
      k₂.gpr r (not_mem_of hr (by decide)), k₁.gpr r (not_mem_of hr (by decide))]
  · rw [k₉.2.2.1, k₈.2.2.1, k₇.2.2.1, k₆.2.2.1, k₄.2.2.1, k₃.rd, k₂.rd, k₁.rd]
  · rw [k₉.2.2.2, k₈.2.2.2, k₇.2.2.2, k₆.2.2.2, k₄.2.2.2, k₃.wr, k₂.wr, k₁.wr]
  · rw [m₉, O₃ x (by omega_arith), O₂ x (by omega_arith), O₁ x (by omega_arith)]
  · rw [m₉, O₃.wordsVal (by omega_arith) (by omega_arith), O₂.wordsVal (by omega_arith) (by omega_arith),
      O₁.wordsVal (by omega_arith) (by omega_arith)]
  · rw [hW]; omega_arith
  · rw [hW]; exact hres

/-- `[o] = [a]² R⁻¹ mod p` for P-384's `p`, with BMI2 and ADX or without. -/
theorem sqrS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOk M size m s.mem base) (hsp : M.sparse = true) {o a : Nat} (ho : o + 48 ≤ size)
    (ha : a + 48 ≤ size) (hoT : o + 48 ≤ M.tmp ∨ M.tmp + 48 ≤ o)
    (haT : a + 48 ≤ M.tmp ∨ M.tmp + 48 ≤ a) (hoM : o + 48 ≤ M.mo ∨ M.mo + 48 ≤ o)
    (hA : wordsVal s.mem base a 6 < m) :
    WP isa (.block (sqrS M o a)) s fun s' =>
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' ∧
      (∀ x, (ofs base x < o ∨ o + 48 ≤ ofs base x) →
        (ofs base x < M.tmp ∨ M.tmp + 48 ≤ ofs base x) → s'.mem x = s.mem x) ∧
      wordsVal s'.mem base o 6 < m ∧
      wordsVal s'.mem base o 6 * 2 ^ (64 * 6) % m = wordsVal s.mem base a 6 * wordsVal s.mem base a 6 % m := by
  obtain ⟨hn, hmP⟩ := Mod.ok_sparse hM.red hsp
  have hnw := hs.nowrap
  have htmp : M.tmp + 48 ≤ size := by have := hM.tmp; rw [hn] at this; exact this
  have hmo : M.mo + 48 ≤ size := by have := hM.mo; rw [hn] at this; exact this
  have hsep : M.mo + 48 ≤ M.tmp ∨ M.tmp + 48 ≤ M.mo := by have := hM.sep; rw [hn] at this; exact this
  rw [sqrS, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sqrSA_ok hs hmP htmp ho ha hoT haT hA) fun s₉ ⟨k₉, O₉, W₉, hlt₉, hres₉⟩ => ?_
  have hs₉ := hs.of_keepRegs k₉ (by decide)
  have hmo₉ : wordsVal s₉.mem base M.mo M.n = m := by
    rw [hn, W₉ M.mo hmo hoM.symm hsep, ← hn]; exact hM.val
  rw [WP.block_append_iff]
  refine WP.mono (csub_ok hs₉ (ts := sqWin6) (top := .r8) (by rw [hn]; rfl) (by rw [hn]; decide)
    ⟨by decide, by decide⟩ hM.mo hM.tmp hM.sep (Mod.ok_sparse hM.red) hmo₉
    (by rw [hn]; exact hlt₉)) fun s₁₀ h₁₀ => ?_
  obtain ⟨e₁₀, k₁₀, O₁₀⟩ := h₁₀
  have hs₁₀ := hs₉.of_keepRegs k₁₀ (by decide)
  refine WP.mono (stores_ok sqWin6 hs₁₀ (o := o) (by simp only [sqWin6, List.length_cons, List.length_nil]; omega_arith)
    (by decide)) fun s₁₁ h₁₁ => ?_
  obtain ⟨e₁₁, k₁₁, O₁₁⟩ := h₁₁
  simp only [show sqWin6.length = 6 from rfl, Nat.reduceMul] at e₁₁ O₁₁
  rw [hn] at e₁₀ O₁₀
  have hval : wordsVal s₁₁.mem base o 6 =
      (regsVal s₉ sqWin6 + 2 ^ (64 * 6) * (s₉.gpr .r8).toNat) % m := by rw [e₁₁, e₁₀]
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun x hx hx' => ?_, ?_, ?_⟩
  · rw [k₁₁.gpr r (by simp), k₁₀.gpr r (not_mem_of hr (by decide)), k₉.gpr r hr]
  · rw [k₁₁.rd, k₁₀.rd, k₉.rd]
  · rw [k₁₁.wr, k₁₀.wr, k₉.wr]
  · rw [O₁₁ x (by omega_arith), O₁₀ x (by omega_arith), O₉ x hx hx']
  · rw [hval]; exact Nat.mod_lt _ (by omega_arith)
  · rw [hval]; exact hres₉

end VG.Proof.Mont.X86_64
