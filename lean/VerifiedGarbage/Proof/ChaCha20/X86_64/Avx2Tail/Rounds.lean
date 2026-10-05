import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx512Tail.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Impl.ChaCha20.X86_64.Avx2Tail

/-!
# ChaCha20 on x86-64 with AVX2, the last bytes: the rounds

Lane `l` (128 bits, `l < 2`) of the registers `ymm0 … ymm7` holds the words
of block `l` of each set, row `r` of the first set's in `ymm r` and of the
second's in `ymm (4 + r)`: as for AVX-512 (`Avx512Tail/Rounds.lean`), whose
instructions of the rounds (`HI`) and whose proof that a double round on
the words is `innerBlock` on each set this reuses. Here an instruction of
the rounds is one or three AVX2 instructions (`ymmOf`): a rotation by 16 or
8 a `vpshufb` with the mask in `ymm8` or `ymm9`, one by 12 or 7 two shifts
and a `vpor` through `ymm10` (first set) or `ymm11` (second).
-/

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word innerBlock)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (xidx xidx_lt xidx_inj sel2 sel2_eq sel2_lt Same Same.trans)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (W HI hstep setRow setRow_row blk colsH diagsH cols2H diags2H
  dr1_words dr2_words)

/-- The scratch register of a rotation by shifts of `d`. -/
def tmp (d : XReg) : XReg := if xidx d < 4 then .xmm10 else .xmm11

/-- An instruction of the rounds, as AVX2 instructions. -/
def ymmOf : HI → List Instr
  | .add d a b => [v .vpaddd d a b]
  | .xor d a b => [v .vpxor d a b]
  | .rol d _ n =>
    if n = 16 then [v .vpshufb d d .xmm8] else if n = 8 then [v .vpshufb d d .xmm9]
    else rotS d (tmp d) n.toNat
  | .shuf d a o => [.vop (.vpshufd .l256 d a o)]

theorem doubleRound1_eq : doubleRound1 = (colsH ++ diagsH).flatMap ymmOf := by decide +kernel
theorem doubleRound2_eq : doubleRound2 = (cols2H ++ diags2H).flatMap ymmOf := by decide +kernel

/-- The registers of the sets hold the words of the two lanes `ws 0, ws 1`. -/
def HY (ws : Nat → W) (s : State) : Prop :=
  ∀ r l q, xidx r < 8 → l < 2 → q < 4 → dword (s.lane r l) q = ws l (4 * xidx r + q)

/-- The masks of the rotations by 16 and 8 in both lanes of `ymm8`, `ymm9`. -/
def YM (s : State) : Prop := ∀ l, s.lane .xmm8 l = rot16Mask ∧ s.lane .xmm9 l = rot8Mask

/-- What an instruction of the rounds needs: its registers in the sets, a
rotation of a register by itself, by 16, 8, 12 or 7. -/
def hiOk : HI → Bool
  | .add d a b | .xor d a b => xidx d < 8 && xidx a < 8 && xidx b < 8
  | .rol d a n => xidx d < 8 && d == a && (n == 16 || n == 8 || n == 12 || n == 7)
  | .shuf d a _ => xidx d < 8 && xidx a < 8

theorem xidx8 (r : XReg) : xidx r < 8 ↔ r ≠ .xmm8 ∧ r ≠ .xmm9 ∧ r ≠ .xmm10 ∧ r ≠ .xmm11 ∧
    r ≠ .xmm12 ∧ r ≠ .xmm13 ∧ r ≠ .xmm14 ∧ r ≠ .xmm15 := by
  cases r <;> simp [xidx]

theorem rot12' (x : Word) : x >>> 20 ||| x <<< 12 = x.rotateLeft 12 := shr_or_shl x (k := 12) (by decide) (by decide)
theorem rot7' (x : Word) : x >>> 25 ||| x <<< 7 = x.rotateLeft 7 := shr_or_shl x (k := 7) (by decide) (by decide)

/-- The frame of an instruction of the rounds: the other registers of the
sets and the masks, and everything but the vector registers. -/
structure Frame' (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- A rotation by 12 or 7, through `t`. -/
theorem rotS_ok (d t : XReg) {n : Nat} (hn : n = 12 ∨ n = 7) (htd : t ≠ d) (s : State) :
    WP isa (.block (rotS d t n)) s fun s' =>
      (∀ l q, q < 4 → dword (s'.lane d l) q = (dword (s.lane d l) q).rotateLeft n) ∧
      (∀ r l, r ≠ d → r ≠ t → s'.lane r l = s.lane r l) ∧ Frame' s s' := by
  apply WP.of_runBlock
  simp only [rotS, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l q hq => ?_, fun r l h₁ h₂ => ?_, by simp, by simp, by simp, by simp⟩
  · simp only [lane_vbin256, lane_vshift256, ite_true, htd, Ne.symm htd, ite_false, VBinOp.sse, dword_por]
    rcases hn with rfl | rfl
    · rw [dword_psrld _ _ (by decide) hq, dword_pslld _ _ (by decide) hq]; exact rot12' _
    · rw [dword_psrld _ _ (by decide) hq, dword_pslld _ _ (by decide) hq]; exact rot7' _
  · simp only [lane_vbin256, lane_vshift256, h₁, h₂, ite_false]

theorem tmp_ne {d : XReg} (hd : xidx d < 8) : tmp d ≠ d ∧ tmp d ≠ .xmm8 ∧ tmp d ≠ .xmm9 ∧
    ∀ r, xidx r < 8 → r ≠ tmp d := by
  have : tmp d = .xmm10 ∨ tmp d = .xmm11 := by unfold tmp; split <;> simp
  have hd' := (xidx8 d).1 hd
  rcases this with e | e <;> rw [e] <;>
    exact ⟨by first | exact Ne.symm hd'.2.2.1 | exact Ne.symm hd'.2.2.2.1, by decide, by decide,
      fun r hr => by have := (xidx8 r).1 hr; first | exact this.2.2.1 | exact this.2.2.2.1⟩

/-- One instruction of the rounds, on both lanes. -/
theorem step_ok (i : HI) (hi : hiOk i = true) {ws : Nat → W} {s : State} (h : HY ws s) (hm : YM s) :
    WP isa (.block (ymmOf i)) s fun s' => HY (fun l => hstep (ws l) i) s' ∧ YM s' ∧ Frame' s s' := by
  cases i with
  | add d a b =>
    simp only [hiOk, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hd, ha⟩, hb⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOf, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · simp only [VBinOp.sse, dword_paddd _ _ hq]; rw [h a l q ha hl hq, h b l q hb hl hq]
      · exact h r l q hr hl hq
    · have := (xidx8 d).1 hd
      simp only [lane_vbin256, Ne.symm this.1, Ne.symm this.2.1, ite_false]; exact hm l
  | xor d a b =>
    simp only [hiOk, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hd, ha⟩, hb⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOf, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · simp only [VBinOp.sse, dword_pxor]; rw [h a l q ha hl hq, h b l q hb hl hq]
      · exact h r l q hr hl hq
    · have := (xidx8 d).1 hd
      simp only [lane_vbin256, Ne.symm this.1, Ne.symm this.2.1, ite_false]; exact hm l
  | shuf d a o =>
    simp only [hiOk, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨hd, ha⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOf, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vpshufd256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rw [dword_shufDwords _ _ hq, sel2_eq, h a l _ ha hl (sel2_lt _ _)]
      · exact h r l q hr hl hq
    · have := (xidx8 d).1 hd
      simp only [lane_vpshufd256, Ne.symm this.1, Ne.symm this.2.1, ite_false]; exact hm l
  | rol d a n =>
    simp only [hiOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at hi
    obtain ⟨⟨hd, rfl⟩, hn⟩ := hi
    have dd := (xidx8 d).1 hd
    rcases hn with ((rfl | rfl) | rfl) | rfl
    · apply WP.of_runBlock
      simp only [ymmOf, v, ite_true, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
        exists_eq_left']
      refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
      · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
        split
        · rename_i e; subst e
          simp only [VBinOp.sse, (hm l).1, dword_pshufb_rot16 _ hq]; rw [h r l q hr hl hq]; rfl
        · exact h r l q hr hl hq
      · simp only [lane_vbin256, Ne.symm dd.1, Ne.symm dd.2.1, ite_false]; exact hm l
    · apply WP.of_runBlock
      simp only [ymmOf, v, show (8 : BitVec 8) ≠ 16 by decide, ite_true, ite_false, runBlock_cons,
        runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
      refine ⟨fun r l q hr hl hq => ?_, fun l => ?_, by simp, by simp, by simp, by simp⟩
      · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
        split
        · rename_i e; subst e
          simp only [VBinOp.sse, (hm l).2, dword_pshufb_rot8 _ hq]; rw [h r l q hr hl hq]; rfl
        · exact h r l q hr hl hq
      · simp only [lane_vbin256, Ne.symm dd.1, Ne.symm dd.2.1, ite_false]; exact hm l
    · show WP isa (.block (rotS d (tmp d) 12)) s _
      obtain ⟨t1, t2, t3, t4⟩ := tmp_ne hd
      refine WP.mono (rotS_ok d (tmp d) (by decide) t1 s) fun s' ⟨r₁, r₂, fr⟩ => ⟨fun r l q hr hl hq => ?_,
        fun l => ⟨by rw [r₂ _ _ (Ne.symm dd.1) (Ne.symm t2)]; exact (hm l).1,
          by rw [r₂ _ _ (Ne.symm dd.2.1) (Ne.symm t3)]; exact (hm l).2⟩, fr⟩
      simp only [hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rename_i e; subst e
        rw [r₁ l q hq, h r l q hr hl hq]; rfl
      · rename_i e
        rw [r₂ _ _ e (t4 r hr)]; exact h r l q hr hl hq
    · show WP isa (.block (rotS d (tmp d) 7)) s _
      obtain ⟨t1, t2, t3, t4⟩ := tmp_ne hd
      refine WP.mono (rotS_ok d (tmp d) (by decide) t1 s) fun s' ⟨r₁, r₂, fr⟩ => ⟨fun r l q hr hl hq => ?_,
        fun l => ⟨by rw [r₂ _ _ (Ne.symm dd.1) (Ne.symm t2)]; exact (hm l).1,
          by rw [r₂ _ _ (Ne.symm dd.2.1) (Ne.symm t3)]; exact (hm l).2⟩, fr⟩
      simp only [hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rename_i e; subst e
        rw [r₁ l q hq, h r l q hr hl hq]; rfl
      · rename_i e
        rw [r₂ _ _ e (t4 r hr)]; exact h r l q hr hl hq

theorem Frame'.trans {s₀ s₁ s₂ : State} (h₁ : Frame' s₀ s₁) (h₂ : Frame' s₁ s₂) : Frame' s₀ s₂ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

/-- Instructions of the rounds, in sequence, on both lanes. -/
theorem block_ok : ∀ (is : List HI), is.all hiOk = true → ∀ {ws : Nat → W} {s : State}, HY ws s → YM s →
    WP isa (.block (is.flatMap ymmOf)) s fun s' =>
      HY (fun l => is.foldl hstep (ws l)) s' ∧ YM s' ∧ Frame' s s'
  | [], _, _, _, h, hm => WP.block_nil ⟨h, hm, rfl, rfl, rfl, rfl⟩
  | i :: is, hok, _, _, h, hm => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rw [List.flatMap_cons]
    exact WP.block_append (WP.mono (step_ok i hok.1 h hm) fun s' ⟨h', hm', f'⟩ =>
      WP.mono (block_ok is hok.2 h' hm') fun s'' ⟨h'', hm'', f''⟩ => ⟨h'', hm'', f'.trans f''⟩)

open VG.Impl.ChaCha20.X86_64.Avx512 (zreg)
open VG.Proof.ChaCha20.X86_64.Avx512 (zreg_xidx xidx_zreg)

/-- The states of `S` sets of two blocks are in the registers: word `i` of
block `l` of set `k` (block `2 k + l`) in doubleword `i % 4` of lane `l` of
`ymm (4 k + i / 4)`. -/
def HB (S : Nat) (vs : Nat → CState) (s : State) : Prop :=
  ∀ k < S, ∀ l < 2, ∀ i (hi : i < 16), dword (s.lane (zreg (4 * k + i / 4)) l) (i % 4) = (vs (2 * k + l))[i]

/-- The words of the lanes of the registers. -/
def wordsOf (s : State) (l : Nat) : W := fun n => dword (s.lane (zreg (n / 4)) l) (n % 4)

theorem hy_wordsOf (s : State) : HY (wordsOf s) s := fun r l q _ _ hq => by
  simp only [wordsOf, show (4 * xidx r + q) / 4 = xidx r by omega,
    show (4 * xidx r + q) % 4 = q by omega, zreg_xidx]

theorem blk_wordsOf {S : Nat} {vs : Nat → CState} {s : State} (h : HB S vs s) {k l : Nat} (hk : k < S)
    (hl : l < 2) : blk (wordsOf s l) k = vs (2 * k + l) := by
  apply Vector.ext; intro i hi
  simp only [blk, Vector.getElem_ofFn, wordsOf]
  rw [show (16 * k + i) / 4 = 4 * k + i / 4 by omega, show (16 * k + i) % 4 = i % 4 by omega]
  exact h k hk l hl i hi

theorem hb_of {S : Nat} {ws : Nat → W} {s : State} (h : HY ws s) {vs : Nat → CState}
    (hv : ∀ k < S, ∀ l < 2, blk (ws l) k = vs (2 * k + l)) (hS : S ≤ 2) : HB S vs s := by
  intro k hk l hl i hi
  rw [h _ l _ (by rw [xidx_zreg _ (by omega)]; omega) hl (Nat.mod_lt _ (by decide)),
    xidx_zreg _ (by omega), ← hv k hk l hl]
  simp only [blk, Vector.getElem_ofFn]
  congr 1; omega

theorem doubleRound1_ok {vs : Nat → CState} {s : State} (h : HB 1 vs s) (hm : YM s) :
    WP isa (.block doubleRound1) s fun s' =>
      HB 1 (fun j => innerBlock (vs j)) s' ∧ YM s' ∧ Frame' s s' := by
  rw [doubleRound1_eq]
  refine WP.mono (block_ok _ (by decide) (hy_wordsOf s) hm) fun s' ⟨h', hm', f⟩ =>
    ⟨hb_of h' (fun k hk l hl => ?_) (by decide), hm', f⟩
  obtain rfl : k = 0 := by omega
  rw [dr1_words, blk_wordsOf h hk hl]

theorem doubleRound2_ok {vs : Nat → CState} {s : State} (h : HB 2 vs s) (hm : YM s) :
    WP isa (.block doubleRound2) s fun s' =>
      HB 2 (fun j => innerBlock (vs j)) s' ∧ YM s' ∧ Frame' s s' := by
  rw [doubleRound2_eq]
  refine WP.mono (block_ok _ (by decide) (hy_wordsOf s) hm) fun s' ⟨h', hm', f⟩ =>
    ⟨hb_of h' (fun k hk l hl => ?_) (by decide), hm', f⟩
  rw [dr2_words _ hk, blk_wordsOf h hk hl]

theorem rounds1_ok {vs : Nat → CState} {s₀ : State} (h : HB 1 vs s₀) (hm : YM s₀) :
    ∀ n, WP isa (rounds1 n) s₀ fun s =>
      HB 1 (fun j => Nat.repeat innerBlock n (vs j)) s ∧ YM s ∧ Frame' s₀ s
  | 0 => WP.block_nil ⟨h, hm, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds1_ok h hm n) fun _ ⟨h₁, hm₁, f₁⟩ =>
      WP.mono (doubleRound1_ok h₁ hm₁) fun _ ⟨h₂, hm₂, f₂⟩ => ⟨h₂, hm₂, f₁.trans f₂⟩)

theorem rounds2_ok {vs : Nat → CState} {s₀ : State} (h : HB 2 vs s₀) (hm : YM s₀) :
    ∀ n, WP isa (rounds2 n) s₀ fun s =>
      HB 2 (fun j => Nat.repeat innerBlock n (vs j)) s ∧ YM s ∧ Frame' s₀ s
  | 0 => WP.block_nil ⟨h, hm, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds2_ok h hm n) fun _ ⟨h₁, hm₁, f₁⟩ =>
      WP.mono (doubleRound2_ok h₁ hm₁) fun _ ⟨h₂, hm₂, f₂⟩ => ⟨h₂, hm₂, f₁.trans f₂⟩)

end VG.Proof.ChaCha20.X86_64.Avx2Tail
