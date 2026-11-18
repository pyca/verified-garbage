module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.Finish
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds3

/-! ### `ChaCha20.X86_64.Avx2Tail.RoundsVL`, which this module and modules that import it used -/

section

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
  have ne : ∀ {d r : XReg}, xidx d < B → B ≤ xidx r → r ≠ d := fun hd hr e => by subst e; omega_using [hr, hd]
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
  obtain rfl : k = 0 := by omega_using [hk]
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

end

end

/-!
# ChaCha20 on x86-64 with AVX2 and AVX-512VL: the rounds with `vprold`

`roundsVL n` loads words 10 and 11 from their slots into `ymm14`, `ymm15`
(`loadV_ok`), runs `n` double rounds with every word in its register
(`roundsV_ok`, the invariant `HoldsV`), and stores them back, with the mask
of the rotation by 16 loaded into `ymm15` again (`storeV_ok`): it ends as
`rounds n` does, in the rounds invariant `RI` (`roundsVL_ok`, and
`roundsFor_ok` for either).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86_64.Avx2Tail (lane_vprold256)

theorem rol16 : (16 : BitVec 8).toNat % 32 = 16 := by decide
theorem rol12 : (12 : BitVec 8).toNat % 32 = 12 := by decide
theorem rol8 : (8 : BitVec 8).toNat % 32 = 8 := by decide
theorem rol7 : (7 : BitVec 8).toNat % 32 = 7 := by decide

theorem qrV_ok {a b c d : XReg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (s : State) :
    WP isa (.block (qrV a b c d)) s fun s' =>
      (∀ l i, i < 4 →
        vw s' a l i = (quarterRound (vw s a l i) (vw s b l i) (vw s c l i) (vw s d l i)).1 ∧
        vw s' b l i = (quarterRound (vw s a l i) (vw s b l i) (vw s c l i) (vw s d l i)).2.1 ∧
        vw s' c l i = (quarterRound (vw s a l i) (vw s b l i) (vw s c l i) (vw s d l i)).2.2.1 ∧
        vw s' d l i = (quarterRound (vw s a l i) (vw s b l i) (vw s c l i) (vw s d l i)).2.2.2) ∧
      (∀ r l, r ≠ a → r ≠ b → r ≠ c → r ≠ d → s'.lane r l = s.lane r l) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [qrV, v, runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun l i hi => ?_, fun r l h₁ h₂ h₃ h₄ => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [↓reduceIte, vw, lane_vbin256, lane_vprold256, VBinOp.sse, hab, hac, had, hbc, hbd,
      hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
    simp only [dword_paddd _ _ hi, dword_pxor, dword_rolDwords _ _ hi, quarterRound,
      rol16, rol12, rol8, rol7, and_self]
  · simp only [↓reduceIte, lane_vbin256, lane_vprold256, h₁, h₂, h₃, h₄]
  all_goals simp

/-- The eight states `vs 0, …, vs 7` are in the registers `vregV`: word `k` of
state `4 l + q` in doubleword `q` of lane `l`. -/
def HoldsV (vs : Nat → CState) (s : State) : Prop :=
  ∀ k (hk : k < 16) l q, l < 2 → q < 4 → vw s (vregV k) l q = (vs (4 * l + q))[k]

theorem vregV_inj : ∀ j < 16, ∀ k < 16, vregV j = vregV k → j = k := by decide

theorem vregV_of {k : Nat} (h10 : k ≠ 10) (h11 : k ≠ 11) : vregV k = vreg k := by
  unfold vregV; split <;> simp_all

theorem quarterV_ok {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hq : [x, y, z, w].Nodup) {vs : Nat → CState} {s : State} (h : HoldsV vs s) :
    WP isa (quarterV x y z w) s fun s' =>
      HoldsV (fun j => qround (vs j) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s' ∧ s'.gpr = s.gpr ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have nd' : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using hq
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd'
  have ne : ∀ {j k}, j < 16 → k < 16 → j ≠ k → vregV j ≠ vregV k :=
    fun hj hk e h => e (vregV_inj _ hj _ hk h)
  refine WP.mono (qrV_ok (ne hx hy nxy) (ne hx hz nxz) (ne hx hw nxw) (ne hy hz nyz)
    (ne hy hw nyw) (ne hz hw nzw) s)
    fun s' ⟨hv, hr, hg, hmem, hrd, hwr⟩ => ⟨fun k hk l q hl hq => ?_, hg, hmem, hrd, hwr⟩
  have gx := h x hx l q hl hq; have gy := h y hy l q hl hq
  have gz := h z hz l q hl hq; have gw := h w hw l q hl hq
  obtain ⟨ha, hb, hc, hd⟩ := hv l q hq
  rw [gx, gy, gz, gw] at ha hb hc hd
  simp only [qround_get _ _ _ _ _ k hk]
  by_cases ew : w = k
  · subst ew; simp only [ite_true]; exact hd
  by_cases ez : z = k
  · subst ez; simp only [ite_true, ew, ite_false]; exact hc
  by_cases ey : y = k
  · subst ey; simp only [ite_true, ew, ez, ite_false]; exact hb
  by_cases ex : x = k
  · subst ex; simp only [ite_true, ew, ez, ey, ite_false]; exact ha
  simp only [ew, ez, ey, ex, ite_false]
  simp only [vw] at h ⊢
  rw [hr _ l (ne hk hx (Ne.symm ex)) (ne hk hy (Ne.symm ey)) (ne hk hz (Ne.symm ez))
    (ne hk hw (Ne.symm ew))]
  exact h k hk l q hl hq

/-- The invariant of `roundsV`, relative to the state `s₁` at their start. -/
def RV (vs : Nat → CState) (s₁ s : State) : Prop :=
  HoldsV vs s ∧ s.gpr = s₁.gpr ∧ s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr

theorem quarterV_step {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hq : [x, y, z, w].Nodup) {vs : Nat → CState} {s₁ s : State} (h : RV vs s₁ s) :
    WP isa (quarterV x y z w) s (RV (fun j => qround (vs j) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₁) :=
  WP.mono (quarterV_ok hx hy hz hw hq h.1) fun _ ⟨hh, hg, hm, hrd, hwr⟩ =>
    ⟨hh, hg.trans h.2.1, hm.trans h.2.2.1, hrd.trans h.2.2.2.1, hwr.trans h.2.2.2.2⟩

theorem doubleRoundV_ok {vs : Nat → CState} {s₁ s : State} (h : RV vs s₁ s) :
    WP isa doubleRoundV s (RV (fun j => innerBlock (vs j)) s₁) := by
  unfold doubleRoundV
  refine WP.seq (WP.mono (quarterV_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarterV_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarterV_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarterV_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarterV_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarterV_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (quarterV_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₇) fun s₈ h₈ => ?_)
  exact WP.mono (quarterV_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₈) fun _ h => h

theorem roundsV_ok {vs : Nat → CState} {s₁ : State} (h : HoldsV vs s₁) :
    ∀ n, WP isa (roundsV n) s₁ (RV (fun j => Nat.repeat innerBlock n (vs j)) s₁)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (roundsV_ok h n) fun _ h' => doubleRoundV_ok h')

/-! ## Into and out of the registers -/

theorem inReg_false {k : Nat} (h10 : k ≠ 10) (h11 : k ≠ 11) : inReg false k = true := by
  simp only [inReg]; split <;> simp_all

theorem inReg10 : inReg false 10 = false := rfl
theorem inReg11 : inReg false 11 = false := rfl

theorem loadV_ok {buf : Addr} {vs : Nat → CState} {s : State} (h : Holds buf false vs s)
    (hrcx : s.gpr .rcx = buf) (hw : bufR buf ∈ s.wr) :
    WP isa (.block [.vmovdquLoad .l256 .xmm14 (at_ .rcx (slotOff 10)),
      .vmovdquLoad .l256 .xmm15 (at_ .rcx (slotOff 11))]) s fun s' =>
      HoldsV vs s' ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 := in_buf (rs := s.rd) hw (d := slotOff 10) (n := 32) (by lit_omega)
  have i2 := in_buf (rs := s.rd) hw (d := slotOff 11) (n := 32) (by lit_omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hrcx, State.load256, i1, i2,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', State.setV_gpr, State.setV_mem,
    State.setV_rd, State.setV_wr]
  refine ⟨fun k hk l q hl hq => ?_, trivial, trivial, trivial, trivial⟩
  have old := h k hk l q hl hq
  rcases (by omega_using [] : k = 10 ∨ k = 11 ∨ (k ≠ 10 ∧ k ≠ 11)) with rfl | rfl | ⟨h10, h11⟩
  · simp only [inReg, Bool.not_false] at old
    simp only [vw, vregV, State.lane_setV256, show (XReg.xmm14 = .xmm15) = False by decide,
      ite_false, ite_true]
    rw [dword_load256 _ _ hl hq, add_ofNat]; exact old
  · simp only [inReg, Bool.not_false] at old
    simp only [vw, vregV, State.lane_setV256, ite_true]
    rw [dword_load256 _ _ hl hq, add_ofNat]; exact old
  · simp only [inReg_false h10 h11, ite_true] at old
    simp only [vw, vregV_of h10 h11, State.lane_setV256, vreg_ne14, vreg_ne15, ite_false] at old ⊢
    exact old

/-- The mask of the rotation by 16, in both halves of `buf[128, 160)`. -/
def M16 (m : Mem) (buf : Addr) : Prop :=
  (m.readW (buf + BitVec.ofNat 64 128) 256).extractLsb' 0 128 = rot16Mask ∧
  (m.readW (buf + BitVec.ofNat 64 128) 256).extractLsb' 128 128 = rot16Mask

theorem slots_m16 (buf : Addr) :
    (⟨buf + BitVec.ofNat 64 128, 256 / 8⟩ : Region).Disjoint (slotsR buf) :=
  Offset.disjoint_base buf (by lit_omega) (by lit_omega)

theorem ymm_withMem (s : State) (m : Mem) (r : XReg) : ({ s with mem := m } : State).ymm r = s.ymm r :=
  rfl

theorem storeV_ok {buf : Addr} {vs : Nat → CState} {s₀ s : State} (h : RV vs s₀ s)
    (hrcx : s₀.gpr .rcx = buf) (hw : bufR buf ∈ s₀.wr) (h16 : M16 s₀.mem buf) :
    WP isa (.block [.vmovdquStore .l256 (at_ .rcx (slotOff 10)) .xmm14,
      .vmovdquStore .l256 (at_ .rcx (slotOff 11)) .xmm15,
      .vmovdquLoad .l256 .xmm15 (at_ .rcx rot16Off)]) s (RI buf false vs s₀) := by
  obtain ⟨hh, hg, hm, hrd, hwr⟩ := h
  have hr : s.gpr .rcx = buf := by rw [hg, hrcx]
  have hw' : bufR buf ∈ s.wr := hwr ▸ hw
  have o1 := out_buf hw' (d := slotOff 10) (n := 32) (by lit_omega)
  have o2 := out_buf hw' (d := slotOff 10 + 32) (n := 32) (by lit_omega)
  have i3 := in_buf (rs := s.rd) hw' (d := rot16Off) (n := 32) (by lit_omega)
  have e11 : slotOff 11 = slotOff 10 + 32 := rfl
  have fr : Frame [slotsR buf] s₀.mem (W2 s.mem buf 10 (s.ymm .xmm14) (s.ymm .xmm15)) :=
    W2_frame buf (by decide) _ _ (hm ▸ Frame.refl _ _)
  have e16 : (W2 s.mem buf 10 (s.ymm .xmm14) (s.ymm .xmm15)).readW (buf + BitVec.ofNat 64 128) 256 =
      s₀.mem.readW (buf + BitVec.ofNat 64 128) 256 :=
    fr.readW (w := 256) (Region.contains_self _ _) (by simpa using slots_m16 buf) (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hr, e11, State.store256,
    State.load256, o1, o2, i3, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    ymm_withMem]
  refine ⟨fun k hk l q hl hq => ?_, fun l => ?_, fr, hg, hrd, hwr⟩
  · have x := hh k hk l q hl hq
    have hx : 16 * l + 4 * q + 4 ≤ 32 := by omega_using [hl, hq]
    rcases (by omega_using [] : k = 10 ∨ k = 11 ∨ (k ≠ 10 ∧ k ≠ 11)) with rfl | rfl | ⟨h10, h11⟩
    · simp only [inReg10, Bool.false_eq_true, ite_false, State.setV_mem]
      rw [W2_first _ _ (by decide) _ _ hx, extract_ymm s _ hl hq]; exact x
    · simp only [inReg11, Bool.false_eq_true, ite_false, e11, State.setV_mem]
      rw [W2_second _ _ _ _ _ hx, extract_ymm s _ hl hq]; exact x
    · simp only [inReg_false h10 h11, ite_true]
      simp only [vw, vregV_of h10 h11, State.lane_setV256, vreg_ne15, ite_false] at x ⊢
      exact x
  · simp only [State.lane_setV256, ite_true, rot16Off, e16]
    split
    · exact h16.1
    · exact h16.2

theorem roundsVL_ok {buf : Addr} {vs : Nat → CState} {s₀ : State} (h : Holds buf false vs s₀)
    (hrcx : s₀.gpr .rcx = buf) (hb : bufR buf ∈ s₀.wr) (h16 : M16 s₀.mem buf) (n : Nat) :
    WP isa (roundsVL n) s₀ (RI buf false (fun j => Nat.repeat innerBlock n (vs j)) s₀) := by
  unfold roundsVL
  refine WP.seq (WP.mono (loadV_ok h hrcx hb) fun s₁ ⟨h₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  refine WP.seq (WP.mono (roundsV_ok h₁ n) fun s₂ ⟨h₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  exact storeV_ok ⟨h₂, g₂.trans g₁, m₂.trans m₁, rd₂.trans rd₁, wr₂.trans wr₁⟩ hrcx hb h16

/-- The kernel's rounds, with `vprold` or without. -/
theorem roundsFor_ok (vl : Bool) {buf : Addr} {vs : Nat → CState} {s₀ : State}
    (h : Holds buf false vs s₀) (h15 : ∀ l, s₀.lane .xmm15 l = rot16Mask) (hrcx : s₀.gpr .rcx = buf)
    (hb : bufR buf ∈ s₀.wr) (h8 : M8 s₀.mem buf) (h16 : M16 s₀.mem buf) :
    WP isa (roundsFor vl) s₀ (RI buf false (fun j => Nat.repeat innerBlock 10 (vs j)) s₀) := by
  cases vl
  · exact rounds_ok h h15 hrcx hb h8 10
  · exact roundsVL_ok h hrcx hb h16 10

end VG.Proof.ChaCha20.X86_64.Avx2
