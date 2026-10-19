module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds3
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# ChaCha20 on x86-64 with AVX2 and AVX-512VL, the last bytes: the rounds with `vprold`

The rounds of one, two or three sets with each rotation one `vprold`
(`ymmOfV`), for the same instructions of the rounds (`HI`) as the AVX2 code's
(`Rounds.lean`, `Rounds3.lean`): they write only the registers of the sets,
so they keep the masks too, and `roundsS_ok` (one or two sets) and
`roundsS3_ok` (three) hold with `vprold` or without.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2Tail

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2Tail
open VG.Spec.ChaCha20 (Word innerBlock)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx512 (xidx xidx_lt xidx_inj sel2 sel2_eq sel2_lt)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (W HI hstep setRow setRow_row blk colsH diagsH cols2H diags2H
  dr1_words dr2_words)

theorem lane_vprold256 (d a : XReg) (n : BitVec 8) (s : State) (r : XReg) (l : Nat) :
    ((VOp.vprold .l256 d a n).exec s).lane r l =
      if r = d then rolDwords (s.lane a l) n else s.lane r l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : r = d <;> by_cases hl : l = 0 <;> simp [h, hl]

/-- An instruction of the rounds, with `vprold` for a rotation. -/
def ymmOfV : HI → List Instr
  | .add d a b => [v .vpaddd d a b]
  | .xor d a b => [v .vpxor d a b]
  | .rol d a n => [.vop (.vprold .l256 d a n)]
  | .shuf d a o => [.vop (.vpshufd .l256 d a o)]

theorem doubleRound1V_eq : doubleRound1V = (colsH ++ diagsH).flatMap ymmOfV := by decide +kernel
theorem doubleRound2V_eq : doubleRound2V = (cols2H ++ diags2H).flatMap ymmOfV := by decide +kernel
theorem doubleRound3V_eq : doubleRound3V = (cols3H ++ diags3H).flatMap ymmOfV := by decide +kernel

/-- The registers `r` with `xidx r < B` hold the words of the two lanes. -/
def HYB (B : Nat) (ws : Nat → W) (s : State) : Prop :=
  ∀ r l q, xidx r < B → l < 2 → q < 4 → dword (s.lane r l) q = ws l (4 * xidx r + q)

/-- What an instruction of the rounds needs with `vprold`: its registers among
the first `B`. -/
def hiOkV (B : Nat) : HI → Bool
  | .add d a b | .xor d a b => xidx d < B && xidx a < B && xidx b < B
  | .rol d a _ | .shuf d a _ => xidx d < B && xidx a < B

/-- One instruction of the rounds with `vprold`, on both lanes; the other
registers are kept. -/
theorem stepV_ok {B : Nat} (i : HI) (hi : hiOkV B i = true) {ws : Nat → W} {s : State}
    (h : HYB B ws s) :
    WP isa (.block (ymmOfV i)) s fun s' => HYB B (fun l => hstep (ws l) i) s' ∧
      (∀ r l, B ≤ xidx r → s'.lane r l = s.lane r l) ∧ Frame' s s' := by
  have ne : ∀ {d r : XReg}, xidx d < B → B ≤ xidx r → r ≠ d := fun hd hr e => by subst e; omega
  cases i with
  | add d a b =>
    simp only [hiOkV, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hd, ha⟩, hb⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOfV, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
      exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun r l hr => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · simp only [VBinOp.sse, dword_paddd _ _ hq]; rw [h a l q ha hl hq, h b l q hb hl hq]
      · exact h r l q hr hl hq
    · simp only [lane_vbin256, ne hd hr, ite_false]
  | xor d a b =>
    simp only [hiOkV, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hd, ha⟩, hb⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOfV, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
      exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun r l hr => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vbin256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · simp only [VBinOp.sse, dword_pxor]; rw [h a l q ha hl hq, h b l q hb hl hq]
      · exact h r l q hr hl hq
    · simp only [lane_vbin256, ne hd hr, ite_false]
  | rol d a n =>
    simp only [hiOkV, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨hd, ha⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOfV, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
      exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun r l hr => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vprold256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rw [dword_rolDwords _ _ hq, h a l q ha hl hq]
      · exact h r l q hr hl hq
    · simp only [lane_vprold256, ne hd hr, ite_false]
  | shuf d a o =>
    simp only [hiOkV, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨hd, ha⟩ := hi
    apply WP.of_runBlock
    simp only [ymmOfV, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
      exists_eq_left']
    refine ⟨fun r l q hr hl hq => ?_, fun r l hr => ?_, by simp, by simp, by simp, by simp⟩
    · simp only [lane_vpshufd256, hstep, setRow_row _ _ _ _ hq, xidx_inj]
      split
      · rw [dword_shufDwords _ _ hq, sel2_eq, h a l _ ha hl (sel2_lt _ _)]
      · exact h r l q hr hl hq
    · simp only [lane_vpshufd256, ne hd hr, ite_false]

/-- Instructions of the rounds with `vprold`, in sequence, on both lanes. -/
theorem blockV_ok {B : Nat} : ∀ (is : List HI), is.all (hiOkV B) = true → ∀ {ws : Nat → W} {s : State},
    HYB B ws s → WP isa (.block (is.flatMap ymmOfV)) s fun s' =>
      HYB B (fun l => is.foldl hstep (ws l)) s' ∧ (∀ r l, B ≤ xidx r → s'.lane r l = s.lane r l) ∧
        Frame' s s'
  | [], _, _, _, h => WP.block_nil ⟨h, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | i :: is, hok, _, _, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rw [List.flatMap_cons]
    exact WP.block_append (WP.mono (stepV_ok i hok.1 h) fun s' ⟨h', k', f'⟩ =>
      WP.mono (blockV_ok is hok.2 h') fun s'' ⟨h'', k'', f''⟩ =>
        ⟨h'', fun r l hr => (k'' r l hr).trans (k' r l hr), f'.trans f''⟩)

theorem ym_keep {s s' : State} (hm : YM s) (k : ∀ r l, 8 ≤ xidx r → s'.lane r l = s.lane r l) : YM s' :=
  fun l => by rw [k _ _ (by decide), k _ _ (by decide)]; exact hm l

theorem ym3_keep {s s' : State} (hm : YM3 s) (k : ∀ r l, 12 ≤ xidx r → s'.lane r l = s.lane r l) :
    YM3 s' :=
  fun l => by rw [k _ _ (by decide), k _ _ (by decide)]; exact hm l

theorem doubleRound1V_ok {vs : Nat → CState} {s : State} (h : HB 1 vs s) (hm : YM s) :
    WP isa (.block doubleRound1V) s fun s' =>
      HB 1 (fun j => innerBlock (vs j)) s' ∧ YM s' ∧ Frame' s s' := by
  rw [doubleRound1V_eq]
  refine WP.mono (blockV_ok (B := 8) _ (by decide) (hy_wordsOf s)) fun s' ⟨h', k', f⟩ =>
    ⟨hb_of h' (fun k hk l hl => ?_) (by decide), ym_keep hm k', f⟩
  obtain rfl : k = 0 := by omega
  rw [dr1_words, blk_wordsOf h hk hl]

theorem doubleRound2V_ok {vs : Nat → CState} {s : State} (h : HB 2 vs s) (hm : YM s) :
    WP isa (.block doubleRound2V) s fun s' =>
      HB 2 (fun j => innerBlock (vs j)) s' ∧ YM s' ∧ Frame' s s' := by
  rw [doubleRound2V_eq]
  refine WP.mono (blockV_ok (B := 8) _ (by decide) (hy_wordsOf s)) fun s' ⟨h', k', f⟩ =>
    ⟨hb_of h' (fun k hk l hl => ?_) (by decide), ym_keep hm k', f⟩
  rw [dr2_words _ hk, blk_wordsOf h hk hl]

theorem doubleRound3V_ok {vs : Nat → CState} {s : State} (h : HB 3 vs s) (hm : YM3 s) :
    WP isa (.block doubleRound3V) s fun s' =>
      HB 3 (fun j => innerBlock (vs j)) s' ∧ YM3 s' ∧ Frame' s s' := by
  rw [doubleRound3V_eq]
  refine WP.mono (blockV_ok (B := 12) _ (by decide) (hy3_wordsOf s)) fun s' ⟨h', k', f⟩ =>
    ⟨hb_of3 h' (fun k hk l hl => ?_) (by decide), ym3_keep hm k', f⟩
  rw [dr3_words _ hk, blk_wordsOf h hk hl]

/-- The rounds of one or two sets, with `vprold` or without. -/
theorem roundsS_ok (vl : Bool) {S : Nat} (hS : S = 1 ∨ S = 2) {vs : Nat → CState} {s₀ : State}
    (h : HB S vs s₀) (hm : YM s₀) :
    ∀ n, WP isa (roundsS vl S n) s₀ fun s =>
      HB S (fun j => Nat.repeat innerBlock n (vs j)) s ∧ YM s ∧ Frame' s₀ s
  | 0 => WP.block_nil ⟨h, hm, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (roundsS_ok vl hS h hm n) fun _ ⟨h₁, hm₁, f₁⟩ => by
      rcases hS with rfl | rfl <;> cases vl
      · exact WP.mono (doubleRound1_ok h₁ hm₁) fun _ ⟨h₂, hm₂, f₂⟩ => ⟨h₂, hm₂, f₁.trans f₂⟩
      · exact WP.mono (doubleRound1V_ok h₁ hm₁) fun _ ⟨h₂, hm₂, f₂⟩ => ⟨h₂, hm₂, f₁.trans f₂⟩
      · exact WP.mono (doubleRound2_ok h₁ hm₁) fun _ ⟨h₂, hm₂, f₂⟩ => ⟨h₂, hm₂, f₁.trans f₂⟩
      · exact WP.mono (doubleRound2V_ok h₁ hm₁) fun _ ⟨h₂, hm₂, f₂⟩ => ⟨h₂, hm₂, f₁.trans f₂⟩)

/-- The rounds of three sets, with `vprold` or without. -/
theorem roundsS3_ok (vl : Bool) {vs : Nat → CState} {s₀ : State} (h : HB 3 vs s₀) (hm : YM3 s₀) :
    ∀ n, WP isa (roundsS vl 3 n) s₀ fun s =>
      HB 3 (fun j => Nat.repeat innerBlock n (vs j)) s ∧ YM3 s ∧ Frame' s₀ s
  | 0 => WP.block_nil ⟨h, hm, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (roundsS3_ok vl h hm n) fun _ ⟨h₁, hm₁, f₁⟩ => by
      cases vl
      · exact WP.mono (doubleRound3_ok h₁ hm₁) fun _ ⟨h₂, hm₂, f₂⟩ => ⟨h₂, hm₂, f₁.trans f₂⟩
      · exact WP.mono (doubleRound3V_ok h₁ hm₁) fun _ ⟨h₂, hm₂, f₂⟩ => ⟨h₂, hm₂, f₁.trans f₂⟩)

end VG.Proof.ChaCha20.X86_64.Avx2Tail
