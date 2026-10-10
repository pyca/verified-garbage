import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes: the rounds of three sets

As `Rounds.lean`, for `last3`'s three sets: the third in `ymm8 … ymm11`
(words `32 … 47` of a lane), the masks of the rotations by 16 and 8 in
`ymm14`, `ymm15`, and the rotations by 12 and 7 through `ymm12` (first and
third set) or `ymm13` (second). A double round on the words is `innerBlock`
on each set, by comparing terms (`cols3_check`, `diags3_check`).
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word innerBlock)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (xidx xidx_lt xidx_inj sel2 sel2_eq sel2_lt)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (W HI hstep setRow setRow_row blk HE hstepE Rel Rel.foldl RelS
  rel_vars relS_vars colsE diagsE colsE_other diagsE_other RelS.cols RelS.diags RelS.congr innerBlock_eq
  vars halfH rotH)

/-- The scratch register of a rotation by shifts of `d`, in three sets. -/
def tmp3 (d : XReg) : XReg := if xidx d < 4 then .xmm12 else if xidx d < 8 then .xmm13 else .xmm12

/-- An instruction of the rounds of three sets, as AVX2 instructions. -/
def ymmOf3 : HI → List Instr
  | .add d a b => [v .vpaddd d a b]
  | .xor d a b => [v .vpxor d a b]
  | .rol d _ n =>
    if n = 16 then [v .vpshufb d d .xmm14] else if n = 8 then [v .vpshufb d d .xmm15]
    else rotS d (tmp3 d) n.toNat
  | .shuf d a o => [.vop (.vpshufd .l256 d a o)]

/-- One half of the quarter round on the columns of the three sets. -/
def half3H (r₁ r₂ : BitVec 8) : List HI :=
  [.add .xmm0 .xmm0 .xmm1, .add .xmm4 .xmm4 .xmm5, .add .xmm8 .xmm8 .xmm9,
   .xor .xmm3 .xmm3 .xmm0, .xor .xmm7 .xmm7 .xmm4, .xor .xmm11 .xmm11 .xmm8,
   .rol .xmm3 .xmm3 r₁, .rol .xmm7 .xmm7 r₁, .rol .xmm11 .xmm11 r₁,
   .add .xmm2 .xmm2 .xmm3, .add .xmm6 .xmm6 .xmm7, .add .xmm10 .xmm10 .xmm11,
   .xor .xmm1 .xmm1 .xmm2, .xor .xmm5 .xmm5 .xmm6, .xor .xmm9 .xmm9 .xmm10,
   .rol .xmm1 .xmm1 r₂, .rol .xmm5 .xmm5 r₂, .rol .xmm9 .xmm9 r₂]

def cols3H : List HI := half3H 16 12 ++ half3H 8 7
def diags3H : List HI :=
  (rotH .xmm1 .xmm2 .xmm3 0x39 0x4e 0x93 ++ rotH .xmm5 .xmm6 .xmm7 0x39 0x4e 0x93 ++
    rotH .xmm9 .xmm10 .xmm11 0x39 0x4e 0x93) ++ cols3H ++
  (rotH .xmm1 .xmm2 .xmm3 0x93 0x4e 0x39 ++ rotH .xmm5 .xmm6 .xmm7 0x93 0x4e 0x39 ++
    rotH .xmm9 .xmm10 .xmm11 0x93 0x4e 0x39)

theorem doubleRound3_eq : doubleRound3 = (cols3H ++ diags3H).flatMap ymmOf3 := by decide +kernel

/-- The registers of the three sets hold the words of the two lanes. -/
def HY3 (ws : Nat → W) (s : State) : Prop :=
  ∀ r l q, xidx r < 12 → l < 2 → q < 4 → dword (s.lane r l) q = ws l (4 * xidx r + q)

/-- The masks of the rotations by 16 and 8 in both lanes of `ymm14`, `ymm15`. -/
def YM3 (s : State) : Prop := ∀ l, s.lane .xmm14 l = rot16Mask ∧ s.lane .xmm15 l = rot8Mask

def hiOk3 : HI → Bool
  | .add d a b | .xor d a b => xidx d < 12 && xidx a < 12 && xidx b < 12
  | .rol d a n => xidx d < 12 && d == a && (n == 16 || n == 8 || n == 12 || n == 7)
  | .shuf d a _ => xidx d < 12 && xidx a < 12

theorem xidx12 (r : XReg) : xidx r < 12 ↔ r ≠ .xmm12 ∧ r ≠ .xmm13 ∧ r ≠ .xmm14 ∧ r ≠ .xmm15 := by
  cases r <;> simp [xidx]

theorem tmp3_ne {d : XReg} (hd : xidx d < 12) : tmp3 d ≠ d ∧ tmp3 d ≠ .xmm14 ∧ tmp3 d ≠ .xmm15 ∧
    ∀ r, xidx r < 12 → r ≠ tmp3 d := by
  have : tmp3 d = .xmm12 ∨ tmp3 d = .xmm13 := by unfold tmp3; split <;> (try split) <;> simp
  have hd' := (xidx12 d).1 hd
  rcases this with e | e <;> rw [e] <;>
    exact ⟨by first | exact Ne.symm hd'.1 | exact Ne.symm hd'.2.1, by decide, by decide,
      fun r hr => by have := (xidx12 r).1 hr; first | exact this.1 | exact this.2.1⟩

/-- One instruction of the rounds of three sets, on both lanes. -/
theorem step3_ok (i : HI) (hi : hiOk3 i = true) {ws : Nat → W} {s : State} (h : HY3 ws s) (hm : YM3 s) :
    WP isa (.block (ymmOf3 i)) s fun s' => HY3 (fun l => hstep (ws l) i) s' ∧ YM3 s' ∧ Frame' s s' := by
  cases i with
  | add d a b =>
    simp only [hiOk3, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hd, ha⟩, hb⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOf3, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · simp only [VBinOp.sse, dword_paddd _ _ hq]; rw [h a l q ha hl hq, h b l q hb hl hq]
      · exact h r l q hr hl hq
    · have := (xidx12 d).1 hd
      simp only [lane_vbin256, Ne.symm this.2.2.1, Ne.symm this.2.2.2, ite_false]; exact hm l
  | xor d a b =>
    simp only [hiOk3, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hd, ha⟩, hb⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOf3, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · simp only [VBinOp.sse, dword_pxor]; rw [h a l q ha hl hq, h b l q hb hl hq]
      · exact h r l q hr hl hq
    · have := (xidx12 d).1 hd
      simp only [lane_vbin256, Ne.symm this.2.2.1, Ne.symm this.2.2.2, ite_false]; exact hm l
  | shuf d a o =>
    simp only [hiOk3, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨hd, ha⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOf3, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vpshufd256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rw [dword_shufDwords _ _ hq, sel2_eq, h a l _ ha hl (sel2_lt _ _)]
      · exact h r l q hr hl hq
    · have := (xidx12 d).1 hd
      simp only [lane_vpshufd256, Ne.symm this.2.2.1, Ne.symm this.2.2.2, ite_false]; exact hm l
  | rol d a n =>
    simp only [hiOk3, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at hi
    obtain ⟨⟨hd, rfl⟩, hn⟩ := hi
    have dd := (xidx12 d).1 hd
    rcases hn with ((rfl | rfl) | rfl) | rfl
    · apply WP.of_runBlock
      simp only [ymmOf3, v, ite_true, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
        exists_eq_left']
      refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
      · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
        split
        · rename_i e; subst e
          simp only [VBinOp.sse, (hm l).1, dword_pshufb_rot16 _ hq]; rw [h r l q hr hl hq]; rfl
        · exact h r l q hr hl hq
      · simp only [lane_vbin256, Ne.symm dd.2.2.1, Ne.symm dd.2.2.2, ite_false]; exact hm l
    · apply WP.of_runBlock
      simp only [ymmOf3, v, show (8 : BitVec 8) ≠ 16 by decide, ite_true, ite_false, runBlock_cons,
        runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
      refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
      · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
        split
        · rename_i e; subst e
          simp only [VBinOp.sse, (hm l).2, dword_pshufb_rot8 _ hq]; rw [h r l q hr hl hq]; rfl
        · exact h r l q hr hl hq
      · simp only [lane_vbin256, Ne.symm dd.2.2.1, Ne.symm dd.2.2.2, ite_false]; exact hm l
    · show WP isa (.block (rotS d (tmp3 d) 12)) s _
      obtain ⟨t1, t2, t3, t4⟩ := tmp3_ne hd
      refine WP.mono (rotS_ok d (tmp3 d) (by decide) t1 s) fun s' ⟨r₁, r₂, fr⟩ => ⟨fun r l q hr hl hq => ?_,
        fun l => ⟨by rw [r₂ _ _ (Ne.symm dd.2.2.1) (Ne.symm t2)]; exact (hm l).1,
          by rw [r₂ _ _ (Ne.symm dd.2.2.2) (Ne.symm t3)]; exact (hm l).2⟩, fr⟩
      simp only [hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rename_i e; subst e
        rw [r₁ l q hq, h r l q hr hl hq]; rfl
      · rename_i e
        rw [r₂ _ _ e (t4 r hr)]; exact h r l q hr hl hq
    · show WP isa (.block (rotS d (tmp3 d) 7)) s _
      obtain ⟨t1, t2, t3, t4⟩ := tmp3_ne hd
      refine WP.mono (rotS_ok d (tmp3 d) (by decide) t1 s) fun s' ⟨r₁, r₂, fr⟩ => ⟨fun r l q hr hl hq => ?_,
        fun l => ⟨by rw [r₂ _ _ (Ne.symm dd.2.2.1) (Ne.symm t2)]; exact (hm l).1,
          by rw [r₂ _ _ (Ne.symm dd.2.2.2) (Ne.symm t3)]; exact (hm l).2⟩, fr⟩
      simp only [hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rename_i e; subst e
        rw [r₁ l q hq, h r l q hr hl hq]; rfl
      · rename_i e
        rw [r₂ _ _ e (t4 r hr)]; exact h r l q hr hl hq

theorem block3_ok : ∀ (is : List HI), is.all hiOk3 = true → ∀ {ws : Nat → W} {s : State}, HY3 ws s → YM3 s →
    WP isa (.block (is.flatMap ymmOf3)) s fun s' =>
      HY3 (fun l => is.foldl hstep (ws l)) s' ∧ YM3 s' ∧ Frame' s s'
  | [], _, _, _, h, hm => WP.block_nil ⟨h, hm, rfl, rfl, rfl, rfl⟩
  | i :: is, hok, _, _, h, hm => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rw [List.flatMap_cons]
    exact WP.block_append (WP.mono (step3_ok i hok.1 h hm) fun s' ⟨h', hm', f'⟩ =>
      WP.mono (block3_ok is hok.2 h' hm') fun s'' ⟨h'', hm'', f''⟩ => ⟨h'', hm'', f'.trans f''⟩)

/-! ## The double round on the words of three sets -/

/-- Two term states agree on the words of the three sets. -/
def eq48 (f g : Nat → HE) : Bool := (List.range 48).all fun k => f k == g k

theorem RelS.of_rel48 {w₀ : W} {f g : Nat → HE} {w : W} (h : Rel w₀ f w) (e : eq48 f g = true)
    {k : Nat} (hk : k < 3) {v : CState} (hg : RelS w₀ g k v) : blk w k = v := by
  simp only [eq48, List.all_eq_true, List.mem_range, beq_iff_eq] at e
  apply Vector.ext; intro i hi
  simp only [blk, Vector.getElem_ofFn]
  rw [← h, e _ (by omega)]
  exact hg i hi

theorem cols3_check : eq48 (cols3H.foldl hstepE vars) (colsE (colsE (colsE vars 0) 1) 2) = true := by
  decide +kernel
theorem diags3_check : eq48 (diags3H.foldl hstepE vars) (diagsE (diagsE (diagsE vars 0) 1) 2) = true := by
  decide +kernel

theorem dr3_words (w : W) {k : Nat} (hk : k < 3) :
    blk ((cols3H ++ diags3H).foldl hstep w) k = innerBlock (blk w k) := by
  rw [List.foldl_append]
  have c0 : RelS w (colsE (colsE (colsE vars 0) 1) 2) 0 _ :=
    (relS_vars w 0).cols.congr fun i hi => by
      rw [colsE_other _ (by omega), colsE_other _ (by omega)]
  have c1 : RelS w (colsE (colsE (colsE vars 0) 1) 2) 1 _ :=
    (((relS_vars w 1).congr fun i hi => colsE_other _ (by omega)).cols).congr fun i hi =>
      colsE_other _ (by omega)
  have c2 : RelS w (colsE (colsE (colsE vars 0) 1) 2) 2 _ :=
    ((relS_vars w 2).congr fun i hi => by
      rw [colsE_other _ (by omega), colsE_other _ (by omega)]).cols
  let w' := cols3H.foldl hstep w
  have d0 : RelS w' (diagsE (diagsE (diagsE vars 0) 1) 2) 0 _ :=
    (relS_vars w' 0).diags.congr fun i hi => by
      rw [diagsE_other _ (by omega), diagsE_other _ (by omega)]
  have d1 : RelS w' (diagsE (diagsE (diagsE vars 0) 1) 2) 1 _ :=
    (((relS_vars w' 1).congr fun i hi => diagsE_other _ (by omega)).diags).congr fun i hi =>
      diagsE_other _ (by omega)
  have d2 : RelS w' (diagsE (diagsE (diagsE vars 0) 1) 2) 2 _ :=
    ((relS_vars w' 2).congr fun i hi => by
      rw [diagsE_other _ (by omega), diagsE_other _ (by omega)]).diags
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
  · rw [RelS.of_rel48 ((rel_vars w').foldl diags3H) diags3_check (by decide) d0,
      RelS.of_rel48 ((rel_vars w).foldl cols3H) cols3_check (by decide) c0, innerBlock_eq]
  · rw [RelS.of_rel48 ((rel_vars w').foldl diags3H) diags3_check (by decide) d1,
      RelS.of_rel48 ((rel_vars w).foldl cols3H) cols3_check (by decide) c1, innerBlock_eq]
  · rw [RelS.of_rel48 ((rel_vars w').foldl diags3H) diags3_check (by decide) d2,
      RelS.of_rel48 ((rel_vars w).foldl cols3H) cols3_check (by decide) c2, innerBlock_eq]

/-! ## The rounds on the registers -/

open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx512 (zreg_xidx xidx_zreg)

theorem hy3_wordsOf (s : State) : HY3 (wordsOf s) s := fun r l q _ _ hq => by
  simp only [wordsOf, show (4 * xidx r + q) / 4 = xidx r by omega,
    show (4 * xidx r + q) % 4 = q by omega, zreg_xidx]

theorem hb_of3 {S : Nat} {ws : Nat → W} {s : State} (h : HY3 ws s) {vs : Nat → CState}
    (hv : ∀ k < S, ∀ l < 2, blk (ws l) k = vs (2 * k + l)) (hS : S ≤ 3) : HB S vs s := by
  intro k hk l hl i hi
  rw [h _ l _ (by rw [xidx_zreg _ (by omega)]; omega) hl (Nat.mod_lt _ (by decide)),
    xidx_zreg _ (by omega), ← hv k hk l hl]
  simp only [blk, Vector.getElem_ofFn]
  congr 1; omega

theorem doubleRound3_ok {vs : Nat → CState} {s : State} (h : HB 3 vs s) (hm : YM3 s) :
    WP isa (.block doubleRound3) s fun s' =>
      HB 3 (fun j => innerBlock (vs j)) s' ∧ YM3 s' ∧ Frame' s s' := by
  rw [doubleRound3_eq]
  refine WP.mono (block3_ok _ (by decide) (hy3_wordsOf s) hm) fun s' ⟨h', hm', f⟩ =>
    ⟨hb_of3 h' (fun k hk l hl => ?_) (by decide), hm', f⟩
  rw [dr3_words _ hk, blk_wordsOf h hk hl]

theorem rounds3_ok {vs : Nat → CState} {s₀ : State} (h : HB 3 vs s₀) (hm : YM3 s₀) :
    ∀ n, WP isa (rounds3 n) s₀ fun s =>
      HB 3 (fun j => Nat.repeat innerBlock n (vs j)) s ∧ YM3 s ∧ Frame' s₀ s
  | 0 => WP.block_nil ⟨h, hm, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds3_ok h hm n) fun _ ⟨h₁, hm₁, f₁⟩ =>
      WP.mono (doubleRound3_ok h₁ hm₁) fun _ ⟨h₂, hm₂, f₂⟩ => ⟨h₂, hm₂, f₁.trans f₂⟩)

end VG.Proof.ChaCha20.X86_64.Avx2Tail
