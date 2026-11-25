module

public import VerifiedGarbage.Impl.Mont.AArch64.P521
public import VerifiedGarbage.Proof.Mont.AArch64.Ops
import VerifiedGarbage.Proof.Mont.AArch64.P521.Kernel
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.P521.Prime
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# P-521's field arithmetic on AArch64

`mulR_ok`, `sqrR_ok`, `add_ok` and `sub_ok`: the products, sums and
differences of `Impl/Mont/AArch64/P521.lean` on the machine, from their
kernels (`P521/Kernel.lean`) and the same checker's account of the reduction
of the bits above `2^521` (`tail_kernel`) and of the linear operations.
-/

@[expose] public section

set_option exponentiation.threshold 1024

namespace VG.Proof.Mont.AArch64.P521

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521
open VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

/-! ## Sequences whose functional is a sum of fields -/

/-- The fields but those of registers that are zero. -/
private def nonzero (B : Bd) : List Seg → List Seg
  | [] => []
  | q :: qs => if Nat.ble q.l 28 && Nat.beq (B.ub.getD q.l 1) 0 then nonzero B qs else q :: nonzero B qs

private theorem nonzero_ok {B : Bd} {inp : Nat → Nat → Nat} {s : St} (hB : B.Ok s) :
    ∀ l, sumL inp s l = sumL inp s (nonzero B l)
  | [] => rfl
  | q :: qs => by
    rw [nonzero]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at h
      have hz : q.ev inp s = 0 := by
        cases hn : nr q.l with
        | none =>
          exfalso
          have : ∀ x ≤ 28, nr x ≠ none := by decide
          exact this q.l h.1 hn
        | some r =>
          have e := nr_eq hn
          have hu := hB.ub r
          rw [← e] at hu
          have hz : s.g r = 0 := by
            have h2 := h.2
            simp only [List.getD_eq_getElem?_getD] at h2 hu
            cases hx : B.ub[q.l]? with
            | none => rw [hx] at h2; exact absurd h2 (by simp)
            | some x => rw [hx] at h2 hu; simp only [Option.getD_some] at h2 hu; omega_using [h2, hu]
          rw [Seg.ev, e, lv_reg, hz, Nat.zero_mod, Nat.zero_div, Nat.mul_zero]
      rw [sumL, hz, Nat.zero_add]
      exact nonzero_ok hB qs
    · rw [sumL, sumL, nonzero_ok hB qs]

private def Seg.key (q : Seg) : Nat := 128 * q.l + q.lo

private def insL (g : Seg) : List Seg → List Seg
  | [] => [g]
  | q :: qs => if Nat.ble g.key q.key then g :: q :: qs else q :: insL g qs

private theorem insL_ok (inp : Nat → Nat → Nat) (s : St) (g : Seg) : ∀ l, sumL inp s (insL g l) = g.ev inp s + sumL inp s l
  | [] => rfl
  | q :: qs => by
    rw [insL]
    split
    · rfl
    · rw [sumL, insL_ok inp s g qs, sumL]; omega_using []

private def sortL : List Seg → List Seg
  | [] => []
  | q :: qs => insL q (sortL qs)

private theorem sortL_ok (inp : Nat → Nat → Nat) (s : St) : ∀ l, sumL inp s (sortL l) = sumL inp s l
  | [] => rfl
  | q :: qs => by rw [sortL, insL_ok, sortL_ok inp s qs, sumL]

private def eqL : List Seg → List Seg → Bool
  | [], [] => true
  | q :: qs, r :: rs => Nat.beq q.l r.l && Nat.beq q.lo r.lo && Nat.beq q.hi r.hi && Nat.beq q.w r.w && eqL qs rs
  | _, _ => false

private theorem eqL_eq : ∀ {l r : List Seg}, eqL l r = true → l = r
  | [], [], _ => rfl
  | q :: qs, r :: rs, h => by
    simp only [eqL, Bool.and_eq_true, Nat.beq_eq] at h
    rw [eqL_eq h.2]
    cases q; cases r
    simp only at h
    simp only [h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2]
  | [], _ :: _, h => absurd h (by simp [eqL])
  | _ :: _, [], h => absurd h (by simp [eqL])

/-- The functional `F` after the sequence is the constant `k` and the fields `E` before it. -/
private def chkL (m : Nat) (os : List Op) (B : Bd) (F : Fn) (k : Nat) (f : Nat) (E : List Seg) : Bool :=
  match backs m inB os B F with
  | none => false
  | some G => B.wf && Nat.beq G.k k && Nat.beq G.f f && G.p.isEmpty && eqL (sortL (nonzero B G.l)) (sortL E)

private theorem chkL_ok {m : Nat} (hm : 0 < m) {os : List Op} {B : Bd} {F : Fn} {k f : Nat} {E : List Seg}
    (h : chkL m os B F k f E = true) {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) (hB : B.Ok s) :
    Cg m (F.ev inp (run inp os s)) (k + f * s.c + sumL inp s E) := by
  unfold chkL at h
  split at h
  · exact absurd h (by simp)
  · rename_i G hG
    simp only [Bool.and_eq_true, Nat.beq_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
    refine (backs_ok hm hi.w hi.b os h0 hs hB hG).trans (Cg.of_eq ?_)
    simp only [Fn.ev, h1, h2, h3, sumP, Nat.add_zero]
    rw [nonzero_ok hB, ← sortL_ok inp s (nonzero B G.l), eqL_eq h4, sortL_ok]

/-! ## The bits above 2^521 -/

/-- Any registers, but `x7` zero and the number's top word at most 512. -/
private def tailB (w : List Reg) : Bd := (anyB.set (w.getD 8 .x8) 0 512 1).set .x7 0 0 1

private def tailE (w : List Reg) : List Seg :=
  (List.range 8).map (fun k => full (w.getD k .x8) (pw k)) ++
    [⟨rn (w.getD 8 .x8), 0, 9, pw 8⟩, ⟨rn (w.getD 8 .x8), 9, 64, 1⟩]

/-- The number `S` becomes `S mod 2^521 + S / 2^521`. -/
private theorem tail_kernel {w : List Reg} (h : chkL (pw 10) (tailOps w) (tailB w) (outFn (pw 10) 0 w 9) 0 0 (tailE w) = true)
    {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) (h7 : s.g .x7 = 0) (h8 : s.g (w.getD 8 .x8) ≤ 512) :
    num (fun k => (run inp (tailOps w) s).g (w.getD k .x8)) 9 =
      num (fun k => s.g (w.getD k .x8)) 9 % 2 ^ 521 + num (fun k => s.g (w.getD k .x8)) 9 / 2 ^ 521 := by
  have hag : Agree (w.getD 8 .x8) s s := fun _ _ => rfl
  have hag7 : Agree .x7 s s := fun _ _ => rfl
  have hB : (tailB w).Ok s := by
    refine Bd.Ok.set (Bd.wf_set anyB_wf _ _ _ _) ?_ hag7 (Nat.zero_le _) (Nat.le_of_eq h7) hs.c
    exact Bd.Ok.set anyB_wf (anyB_ok hs) hag (Nat.zero_le _) h8 hs.c
  have hO := run_Ok (inp := inp) hi.w (tailOps w) hs
  have e := chkL_ok (pw_pos 10) h hi hs hB
  have eo := (outFn_ev (m := pw 10) (sh := 0) (out := w) (inp := inp) hO 9).symm.trans e
  rw [pw_zero, Nat.one_mul, Nat.zero_mul, Nat.zero_add, tailE, sumL_append] at eo
  have hw : ∀ k, s.g (w.getD k .x8) < 2 ^ 64 := fun k => hs.g _
  have e8 : ∀ n, sumL inp s ((List.range n).map fun k => full (w.getD k .x8) (pw k)) = num (fun k => s.g (w.getD k .x8)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, sumL_append, ih, num_succ, List.map_cons, List.map_nil, sumL, sumL,
        Nat.add_zero, full_ev hs]
  rw [e8 8] at eo
  rw [num_succ (fun k => s.g (w.getD k .x8)) 8]
  have hl := num_lt (n := 8) fun i _ => hw i
  have hlo := num_lt (n := 9) (f := fun k => (run inp (tailOps w) s).g (w.getD k .x8)) fun i _ => hO.g _
  simp only [sumL, Seg.ev, lv_reg, Nat.pow_zero, Nat.div_one, Nat.add_zero, Nat.one_mul, Nat.mod_eq_of_lt (hw 8)] at eo
  generalize num (fun k => (run inp (tailOps w) s).g (w.getD k .x8)) 9 = V at eo hlo ⊢
  generalize num (fun k => s.g (w.getD k .x8)) 8 = L at eo hl ⊢
  generalize s.g (w.getD 8 .x8) = t at eo h8 ⊢
  unfold Cg at eo
  simp only [pw, Nat.reduceMul] at eo hl hlo ⊢
  rw [Nat.mod_eq_of_lt (by omega_using [hlo]), Nat.mod_eq_of_lt (by omega_using [hl, h8])] at eo
  rw [eo]
  omega_using [hl, h8]

private theorem prime_prime : Nat.Prime prime := by
  rw [show prime = 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151 by decide +kernel]
  exact VG.Proof.P521.prime_6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151

/-- The reduction: from a number `S` that is `A B` modulo `p`, times `2^-576`,
below `2^521 + 2^512`, and zero where `A` or `B` is. -/
private theorem red_ok {A B S V : Nat} (hA : A < prime) (hB : B < prime) (hS : S < 2 ^ 521 + 2 ^ 512)
    (he : Cg prime (pw 9 * S) (A * B)) (hz : A = 0 ∨ B = 0 → S = 0) (hV : V = S % 2 ^ 521 + S / 2 ^ 521) :
    V < prime ∧ V * pw 9 % prime = A * B % prime := by
  have hp : prime = 2 ^ 521 - 1 := rfl
  have hc : Cg prime V S := by
    unfold Cg
    rw [hV, hp]
    have hS' := Nat.div_add_mod S (2 ^ 521)
    omega_using [hS']
  refine ⟨?_, ?_⟩
  · have hle : V ≤ prime := by rw [hV, hp]; omega_using [hS]
    refine Nat.lt_of_le_of_ne hle fun hVp => ?_
    have hSp : S = prime := by rw [hV, hp] at hVp; rw [hp]; omega_using [hS, hVp]
    have hd : prime ∣ A * B := by
      refine Nat.dvd_of_mod_eq_zero ?_
      rw [← he, hSp, Nat.mul_mod_left]
    have hAB : A = 0 ∨ B = 0 := by
      rcases (Nat.Prime.dvd_mul prime_prime).mp hd with h | h
      · exact .inl (Nat.eq_zero_of_dvd_of_lt h hA)
      · exact .inr (Nat.eq_zero_of_dvd_of_lt h hB)
    have := hz hAB
    rw [hSp] at this
    exact absurd this (by decide +kernel)
  · rw [Nat.mul_comm V]
    refine (Nat.mul_mod _ _ _).trans ?_
    rw [show V % prime = S % prime from hc, ← Nat.mul_mod]
    exact he

/-! ## Products, abstractly -/

private theorem run_append (inp : Nat → Nat → Nat) : ∀ (l r : List Op) (s : St), run inp (l ++ r) s = run inp r (run inp l s)
  | [], _, _ => rfl
  | o :: os, r, s => run_append inp os r (step inp o s)

/-- `x7` is zero after a sequence. -/
private def chk7 (os : List Op) : Bool := Nat.beq ((fwds inB os anyB).u .x7) 0

private theorem chk7_ok {os : List Op} (h : chk7 os = true) {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) :
    (run inp os s).g .x7 = 0 :=
  Nat.eq_zero_of_le_zero (Nat.le_trans ((fwds_ok hi.w hi.b os anyB_wf hs (anyB_ok hs)).1.ub _)
    (Nat.le_of_eq (Nat.eq_of_beq_eq_true h)))

private theorem top_bound {f : Nat → Nat} (hw : ∀ i, f i < 2 ^ 64) (h8 : f 8 ≤ 512) : num f 9 < 2 ^ 521 + 2 ^ 512 := by
  have hl := num_lt (n := 8) fun i _ => hw i
  rw [num_succ]
  generalize num f 8 = L at hl ⊢
  simp only [pw] at hl ⊢
  omega_using [hl, h8]

private theorem mul_run {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s)
    (hA : num (inp 0) 9 < prime) (hB : num (inp 1) 9 < prime) (hz : ∀ k i, 9 ≤ i → inp k i = 0) :
    num (fun k => (run inp (mulOps ++ tailOps mulOut) s).g (mulOut.getD k .x8)) 9 < prime ∧
      num (fun k => (run inp (mulOps ++ tailOps mulOut) s).g (mulOut.getD k .x8)) 9 * pw 9 % prime =
        num (inp 0) 9 * num (inp 1) 9 % prime := by
  have hO := run_Ok (inp := inp) hi.w mulOps hs
  rw [run_append]
  refine red_ok hA hB (top_bound (f := fun k => (run inp mulOps s).g (mulOut.getD k .x8)) (fun i => hO.g _) (mul_top hi hs)) (mul_kernel hi hs) (fun h => mul_zero hi hs ?_)
    (tail_kernel (by decide +kernel) hi hO (chk7_ok (by decide +kernel) hi hs) (mul_top hi hs))
  exact h.imp (fun h i => if hi : i < 9 then num_zero h i hi else hz 0 i (Nat.le_of_not_lt hi))
    (fun h i => if hi : i < 9 then num_zero h i hi else hz 1 i (Nat.le_of_not_lt hi))

private theorem sqr_run {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s)
    (hA : num (inp 0) 9 < prime) (hz : ∀ k i, 9 ≤ i → inp k i = 0) :
    num (fun k => (run inp (sqrOps ++ tailOps sqrOut) s).g (sqrOut.getD k .x8)) 9 < prime ∧
      num (fun k => (run inp (sqrOps ++ tailOps sqrOut) s).g (sqrOut.getD k .x8)) 9 * pw 9 % prime =
        num (inp 0) 9 * num (inp 0) 9 % prime := by
  have hO := run_Ok (inp := inp) hi.w sqrOps hs
  rw [run_append]
  refine red_ok hA hA (top_bound (f := fun k => (run inp sqrOps s).g (sqrOut.getD k .x8)) (fun i => hO.g _) (sqr_top hi hs)) (sqr_kernel hi hs) (fun h => sqr_zero hi hs ?_)
    (tail_kernel (by decide +kernel) hi hO (chk7_ok (by decide +kernel) hi hs) (sqr_top hi hs))
  exact fun i => if hi : i < 9 then num_zero (h.elim id id) i hi else hz 0 i (Nat.le_of_not_lt hi)

/-! ## Sums and differences, abstractly -/

private def inpE (k : Nat) (w : Nat → Nat) : List Seg := (List.range 9).map fun i => ⟨inpLoc k i, 0, 64, w i⟩

private theorem inpE_ev {inp : Nat → Nat → Nat} (hi : InB inp) (s : St) (k : Nat) (w : Nat → Nat) :
    sumL inp s (inpE k w) = sumTo (fun i => w i * inp k i) 9 := by
  have h : ∀ n ≤ 9, sumL inp s ((List.range n).map fun i => ⟨inpLoc k i, 0, 64, w i⟩) = sumTo (fun i => w i * inp k i) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, sumL_append, ih (by omega_using [hn]), sumTo]
      simp only [List.map_cons, List.map_nil, sumL, Seg.ev, Nat.add_zero, Nat.pow_zero, Nat.div_one]
      rw [lv_inp inp s (by omega_using [hn]), Nat.mod_eq_of_lt (hi.w k n)]
  exact h 9 (Nat.le_refl _)

/-- The output's words and `2^576` times the carry. -/
private def outC : Fn := { outFn (pw 10) 0 linOut 9 with f := pw 9 }

private theorem outC_ev {inp : Nat → Nat → Nat} {s : St} (hs : Ok s) :
    Cg (pw 10) (outC.ev inp s) (num (fun k => s.g (linOut.getD k .x8)) 9 + pw 9 * s.c) := by
  have h := outFn_ev (m := pw 10) (sh := 0) (out := linOut) (inp := inp) hs 9
  rw [pw_zero, Nat.one_mul] at h
  refine Cg.trans (Cg.of_eq ?_) (h.add (Cg.refl _ (pw 9 * s.c)))
  simp only [Fn.ev, outC, outFn, Nat.zero_mul, Nat.zero_add]
  omega_using []

private theorem neg_sum {inp : Nat → Nat → Nat} (k : Nat) : ∀ n, n ≤ 9 →
    sumTo (fun i => (pw 10 - pw i) * inp k i) n + num (inp k) n = pw 10 * sumTo (inp k) n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [sumTo, num_succ, sumTo, Nat.mul_add, ← neg_sum k n (by omega_using [hn])]
    have hle : pw n ≤ pw 10 := Nat.pow_le_pow_right (by decide) (by omega_using [hn])
    have e : (pw 10 - pw n) * inp k n + pw n * inp k n = pw 10 * inp k n := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hle]
    omega_using [e]

/-- `[a] - [b]`, and the borrow. -/
private theorem subChain_kernel {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) :
    num (fun k => (run inp subChain s).g (linOut.getD k .x8)) 9 + pw 9 * (run inp subChain s).c + num (inp 1) 9 =
      pw 9 + num (inp 0) 9 := by
  have hO := run_Ok (inp := inp) hi.w subChain hs
  have e := chkL_ok (m := pw 10) (os := subChain) (B := anyB) (F := outC) (k := pw 9) (f := 0)
    (E := inpE 0 pw ++ inpE 1 fun i => pw 10 - pw i) (pw_pos 10) (by decide +kernel) hi hs (anyB_ok hs)
  have e2 := (outC_ev (inp := inp) hO).symm.trans e
  rw [Nat.zero_mul, Nat.add_zero, sumL_append, inpE_ev hi, inpE_ev hi,
    show sumTo (fun i => pw i * inp 0 i) 9 = num (inp 0) 9 from rfl] at e2
  have e3 := e2.add (Cg.refl (pw 10) (num (inp 1) 9))
  rw [show pw 9 + (num (inp 0) 9 + sumTo (fun i => (pw 10 - pw i) * inp 1 i) 9) + num (inp 1) 9 =
    pw 10 * sumTo (inp 1) 9 + (pw 9 + num (inp 0) 9) by rw [← neg_sum 1 9 (Nat.le_refl _)]; omega_using []] at e3
  have hD := num_lt (n := 9) (f := fun k => (run inp subChain s).g (linOut.getD k .x8)) fun i _ => hO.g _
  have h0 := num_lt (n := 9) (f := inp 0) fun i _ => hi.w 0 i
  have h1 := num_lt (n := 9) (f := inp 1) fun i _ => hi.w 1 i
  have hc := hO.c
  have hcc : pw 9 * (run inp subChain s).c ≤ pw 9 := by
    have := Nat.mul_le_mul_left (pw 9) hc; rwa [Nat.mul_one] at this
  unfold Cg at e3
  rw [Nat.mul_add_mod_self_left] at e3
  have hp : 4 * pw 9 ≤ pw 10 := by rw [pw_succ 9]; exact Nat.mul_le_mul_right _ (by decide)
  rw [Nat.mod_eq_of_lt (by omega_using [hD, h1, hcc, hp]), Nat.mod_eq_of_lt (by omega_using [h0, hp])] at e3
  exact e3

/-- `[a] + [b]`. -/
private theorem addChain_kernel {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) :
    num (fun k => (run inp addChain s).g (linOut.getD k .x8)) 9 + pw 9 * (run inp addChain s).c =
      num (inp 0) 9 + num (inp 1) 9 := by
  have hO := run_Ok (inp := inp) hi.w addChain hs
  have e := chkL_ok (m := pw 10) (os := addChain) (B := anyB) (F := outC) (k := 0) (f := 0)
    (E := inpE 0 pw ++ inpE 1 pw) (pw_pos 10) (by decide +kernel) hi hs (anyB_ok hs)
  have e2 := (outC_ev (inp := inp) hO).symm.trans e
  rw [Nat.zero_mul, Nat.add_zero, sumL_append, inpE_ev hi, inpE_ev hi] at e2
  have e3 : Cg (pw 10) _ (0 + (num (inp 0) 9 + num (inp 1) 9)) := e2
  have hD := num_lt (n := 9) (f := fun k => (run inp addChain s).g (linOut.getD k .x8)) fun i _ => hO.g _
  have h0 := num_lt (n := 9) (f := inp 0) fun i _ => hi.w 0 i
  have h1 := num_lt (n := 9) (f := inp 1) fun i _ => hi.w 1 i
  have hcc : pw 9 * (run inp addChain s).c ≤ pw 9 := by
    have := Nat.mul_le_mul_left (pw 9) hO.c; rwa [Nat.mul_one] at this
  unfold Cg at e3
  have hp : 4 * pw 9 ≤ pw 10 := by rw [pw_succ 9]; exact Nat.mul_le_mul_right _ (by decide)
  have hp1 : 2 ≤ pw 9 := by decide +kernel
  rw [Nat.mod_eq_of_lt (by omega_using [hD, hcc, hp]), Nat.mod_eq_of_lt (by omega_using [h0, h1, hp, hp1])] at e3
  omega_using [e3]

/-- One less where the carry is clear, modulo `2^521`. -/
private theorem dec_kernel {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) (h7 : s.g .x7 = 0) :
    num (fun k => (run inp decOps s).g (linOut.getD k .x8)) 9 =
      (num (fun k => s.g (linOut.getD k .x8)) 9 + (2 ^ 521 - 1) + s.c) % 2 ^ 521 := by
  have hO := run_Ok (inp := inp) hi.w decOps hs
  have hB : (anyB.set .x7 0 0 1).Ok s :=
    Bd.Ok.set anyB_wf (anyB_ok hs) (fun _ _ => rfl) (Nat.zero_le _) (Nat.le_of_eq h7) hs.c
  have e := chkL_ok (m := 2 ^ 521) (os := decOps) (B := anyB.set .x7 0 0 1) (F := outFn (2 ^ 521) 0 linOut 9)
    (k := 2 ^ 521 - 1) (f := 1) (E := (List.range 9).map fun k => full (linOut.getD k .x8) (pw k)) (by decide +kernel)
    (by decide +kernel) hi hs hB
  have e2 := (outFn_ev (m := 2 ^ 521) (sh := 0) (out := linOut) (inp := inp) hO 9).symm.trans e
  have e9 : sumL inp s ((List.range 9).map fun k => full (linOut.getD k .x8) (pw k)) = num (fun k => s.g (linOut.getD k .x8)) 9 := by
    have h : ∀ n, sumL inp s ((List.range n).map fun k => full (linOut.getD k .x8) (pw k)) = num (fun k => s.g (linOut.getD k .x8)) n := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [List.range_succ, List.map_append, sumL_append, ih, num_succ, List.map_cons, List.map_nil, sumL, sumL,
          Nat.add_zero, full_ev hs]
    exact h 9
  rw [pw_zero, Nat.one_mul, e9, Nat.one_mul] at e2
  have ht : (run inp decOps s).g (linOut.getD 8 .x8) ≤ 511 :=
    Nat.le_trans ((fwds_ok hi.w hi.b decOps anyB_wf hs (anyB_ok hs)).1.ub _) (by
      exact Nat.le_of_ble_eq_true (by decide +kernel))
  have hl := num_lt (n := 8) (f := fun k => (run inp decOps s).g (linOut.getD k .x8)) fun i _ => hO.g _
  have hlt : num (fun k => (run inp decOps s).g (linOut.getD k .x8)) 9 < 2 ^ 521 := by
    rw [num_succ]
    generalize num (fun k => (run inp decOps s).g (linOut.getD k .x8)) 8 = L at hl ⊢
    simp only [pw] at hl ⊢
    omega_using [hl, ht]
  rw [← Nat.mod_eq_of_lt hlt]
  refine Eq.trans e2 ?_
  congr 1
  omega_using []

private theorem sub_run {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s)
    (hA : num (inp 0) 9 < prime) (hB : num (inp 1) 9 < prime) :
    num (fun k => (run inp subOps s).g (linOut.getD k .x8)) 9 = (num (inp 0) 9 + prime - num (inp 1) 9) % prime := by
  have hO := run_Ok (inp := inp) hi.w subChain hs
  rw [subOps, run_append, dec_kernel hi hO (chk7_ok (by decide +kernel) hi hs)]
  have h := subChain_kernel hi hs
  have hc := hO.c
  have hD := num_lt (n := 9) (f := fun k => (run inp subChain s).g (linOut.getD k .x8)) fun i _ => hO.g _
  generalize num (fun k => (run inp subChain s).g (linOut.getD k .x8)) 9 = D at h hD ⊢
  generalize (run inp subChain s).c = c at h hc ⊢
  generalize num (inp 0) 9 = A at h hA ⊢
  generalize num (inp 1) 9 = B at h hB ⊢
  rw [show prime = 2 ^ 521 - 1 from rfl] at hA hB ⊢
  simp only [pw] at h hD
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;> omega_using [h, hD, hA, hB]

private theorem prime_run {inp : Nat → Nat → Nat} {s : St} (h7 : s.g .x7 = 0) :
    (∀ k < 9, (run inp primeOps s).g (linOut.getD k .x8) = s.g (linOut.getD k .x8)) ∧ (run inp primeOps s).g .x7 = 0 ∧
      (run inp primeOps s).g .x1 = 2 ^ 64 - 1 ∧ (run inp primeOps s).g .x2 = 511 := by
  refine ⟨fun k hk => ?_, ?_, ?_, ?_⟩
  · have : ∀ k < 9, linOut.getD k .x8 ≠ .x2 ∧ linOut.getD k .x8 ≠ .x1 := by decide
    have hk' := this k hk
    simp only [primeOps, run, step, St.set, St.setc, hk'.1, hk'.2, ite_false]
  · simp only [primeOps, run, step, St.set, St.setc, reduceCtorEq, ite_false]
    exact h7
  · simp only [primeOps, run, step, St.set, St.setc, reduceCtorEq, ite_false, ite_true, h7]
    decide
  · simp only [primeOps, run, step, St.set, St.setc, reduceCtorEq, ite_false, ite_true]

private theorem mask_run {inp : Nat → Nat → Nat} {s : St} (hs : Ok s) (h7 : s.g .x7 = 0) (h2 : s.g .x2 = 511) :
    (∀ k < 9, (run inp maskOps s).g (linOut.getD k .x8) = s.g (linOut.getD k .x8)) ∧
      (run inp maskOps s).g .x1 = (2 ^ 64 - 1) * (1 - s.c) ∧ (run inp maskOps s).g .x2 = 511 * (1 - s.c) := by
  have hc := hs.c
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · have : ∀ k < 9, linOut.getD k .x8 ≠ .x2 ∧ linOut.getD k .x8 ≠ .x1 := by decide
    have hk' := this k hk
    simp only [maskOps, run, step, St.set, St.setc, hk'.1, hk'.2, ite_false]
  · show (s.g .x7 + (2 ^ 64 - 1 - s.g .x7) + s.c) % 2 ^ 64 = _
    rw [h7]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> rw [h] <;> decide
  · show (s.g .x7 + (2 ^ 64 - 1 - s.g .x7) + s.c) % 2 ^ 64 &&& s.g .x2 = _
    rw [h7, h2]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h | h <;> rw [h] <;> decide

private theorem sub7 {inp : Nat → Nat → Nat} {s : St} (h : s.g .x7 = 0) : (run inp subPrime s).g .x7 = 0 := h

private theorem sub2 {inp : Nat → Nat → Nat} {s : St} (h : s.g .x2 = 511) : (run inp subPrime s).g .x2 = 511 := h

private theorem lin_ev {inp : Nat → Nat → Nat} {s : St} (hs : Ok s) :
    sumL inp s ((List.range 9).map fun k => full (linOut.getD k .x8) (pw k)) = num (fun k => s.g (linOut.getD k .x8)) 9 := by
  have h : ∀ n, sumL inp s ((List.range n).map fun k => full (linOut.getD k .x8) (pw k)) = num (fun k => s.g (linOut.getD k .x8)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.map_append, sumL_append, ih, num_succ, List.map_cons, List.map_nil, sumL, sumL,
        Nat.add_zero, full_ev hs]
  exact h 9

/-- The weight of `x1` in the number in `x1` and `x2`. -/
private def lowW : Nat := (List.range 8).foldl (fun w k => w + pw k) 0

private theorem pWord_sum : lowW * (2 ^ 64 - 1) + pw 8 * 511 = prime := by decide +kernel

/-- The number subtracted, and the borrow. -/
private theorem subPrime_kernel {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s)
    (h1 : s.g .x1 = 2 ^ 64 - 1) (h2 : s.g .x2 = 511) (hA : num (fun k => s.g (linOut.getD k .x8)) 9 < 2 * prime) :
    num (fun k => (run inp subPrime s).g (linOut.getD k .x8)) 9 + pw 9 * (run inp subPrime s).c + prime =
      pw 9 + num (fun k => s.g (linOut.getD k .x8)) 9 := by
  have hO := run_Ok (inp := inp) hi.w subPrime hs
  have e := chkL_ok (m := pw 10) (os := subPrime) (B := anyB) (F := outC) (k := pw 9) (f := 0)
    (E := ((List.range 9).map fun k => full (linOut.getD k .x8) (pw k)) ++
      [full .x1 (pw 10 - lowW), full .x2 (pw 10 - pw 8)]) (pw_pos 10) (by decide +kernel) hi hs (anyB_ok hs)
  have e2 := (outC_ev (inp := inp) hO).symm.trans e
  rw [Nat.zero_mul, Nat.add_zero, sumL_append, lin_ev hs] at e2
  simp only [sumL, full_ev hs, h1, h2, Nat.add_zero] at e2
  have e3 := e2.add (Cg.refl (pw 10) prime)
  have hp : (pw 10 - lowW) * (2 ^ 64 - 1) + (pw 10 - pw 8) * 511 + prime = pw 10 * (2 ^ 64 - 1 + 511) := by decide +kernel
  generalize num (fun k => s.g (linOut.getD k .x8)) 9 = A at e3 hA ⊢
  have hD := num_lt (n := 9) (f := fun k => (run inp subPrime s).g (linOut.getD k .x8)) fun i _ => hO.g _
  have hcc : pw 9 * (run inp subPrime s).c ≤ pw 9 := by
    have := Nat.mul_le_mul_left (pw 9) hO.c; rwa [Nat.mul_one] at this
  have hb : 4 * pw 9 ≤ pw 10 := by rw [pw_succ 9]; exact Nat.mul_le_mul_right _ (by decide)
  have hb2 : 2 * prime ≤ pw 9 := by decide +kernel
  rw [show pw 9 + (A + ((pw 10 - lowW) * (2 ^ 64 - 1) + (pw 10 - pw 8) * 511)) + prime =
    pw 10 * (2 ^ 64 - 1 + 511) + (pw 9 + A) by rw [← hp]; omega_using []] at e3
  unfold Cg at e3
  rw [Nat.mul_add_mod_self_left] at e3
  rw [Nat.mod_eq_of_lt (by omega_using [hD, hcc, hb, hb2, hA]), Nat.mod_eq_of_lt (by omega_using [hA, hb, hb2])] at e3
  exact e3

/-- The masked number added. -/
private theorem addBack_kernel {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s) {c : Nat}
    (h1 : s.g .x1 = (2 ^ 64 - 1) * (1 - c)) (h2 : s.g .x2 = 511 * (1 - c)) :
    num (fun k => (run inp addBack s).g (linOut.getD k .x8)) 9 =
      (num (fun k => s.g (linOut.getD k .x8)) 9 + prime * (1 - c)) % pw 9 := by
  have hO := run_Ok (inp := inp) hi.w addBack hs
  have e := chkL_ok (m := pw 9) (os := addBack) (B := anyB) (F := outFn (pw 9) 0 linOut 9) (k := 0) (f := 0)
    (E := ((List.range 9).map fun k => full (linOut.getD k .x8) (pw k)) ++ [full .x1 lowW, full .x2 (pw 8)])
    (pw_pos 9) (by decide +kernel) hi hs (anyB_ok hs)
  have e2 := (outFn_ev (m := pw 9) (sh := 0) (out := linOut) (inp := inp) hO 9).symm.trans e
  rw [pw_zero, Nat.one_mul, Nat.zero_mul, Nat.zero_add, sumL_append, lin_ev hs] at e2
  simp only [sumL, full_ev hs, h1, h2, Nat.add_zero] at e2
  have hw : lowW * ((2 ^ 64 - 1) * (1 - c)) + pw 8 * (511 * (1 - c)) = prime * (1 - c) := by
    have h := congrArg (· * (1 - c)) pWord_sum
    generalize prime = p at h ⊢
    generalize lowW = l at h ⊢
    generalize pw 8 = q at h ⊢
    generalize 1 - c = d at h ⊢
    generalize 2 ^ 64 - 1 = e at h ⊢
    generalize 511 = f at h ⊢
    rw [← h, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  have hD := num_lt (n := 9) (f := fun k => (run inp addBack s).g (linOut.getD k .x8)) fun i _ => hO.g _
  generalize num (fun k => (run inp addBack s).g (linOut.getD k .x8)) 9 = D at e2 hD ⊢
  rw [hw] at e2
  exact (Nat.mod_eq_of_lt hD).symm.trans e2

private theorem add_run {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s)
    (hAB : num (inp 0) 9 + num (inp 1) 9 < 2 * prime) :
    num (fun k => (run inp addOps s).g (linOut.getD k .x8)) 9 = (num (inp 0) 9 + num (inp 1) 9) % prime := by
  have hb2 : 2 * prime ≤ pw 9 := by decide +kernel
  have o1 := run_Ok (inp := inp) hi.w addChain hs
  have o2 := run_Ok (inp := inp) hi.w primeOps o1
  have o3 := run_Ok (inp := inp) hi.w subPrime o2
  have o4 := run_Ok (inp := inp) hi.w maskOps o3
  obtain ⟨p1, p7, px1, px2⟩ := prime_run (inp := inp) (s := run inp addChain s) (chk7_ok (by decide +kernel) hi hs)
  have h := addChain_kernel hi hs
  have hc := o1.c
  have hN : num (fun k => (run inp addChain s).g (linOut.getD k .x8)) 9 = num (inp 0) 9 + num (inp 1) 9 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with h' | h' <;> rw [h'] at h <;> omega_using [h, hAB, hb2]
  have eP : num (fun k => (run inp primeOps (run inp addChain s)).g (linOut.getD k .x8)) 9 =
      num (inp 0) 9 + num (inp 1) 9 := (sumTo_congr fun i hi => congrArg (pw i * ·) (p1 i hi)).trans hN
  have hS := subPrime_kernel hi o2 px1 px2 (by rw [eP]; exact hAB)
  rw [eP] at hS
  obtain ⟨q1, qx1, qx2⟩ := mask_run (inp := inp) o3 (sub7 (inp := inp) p7) (sub2 (inp := inp) px2)
  have hF := addBack_kernel hi o4 qx1 qx2
  rw [show num (fun k => (run inp maskOps (run inp subPrime (run inp primeOps (run inp addChain s)))).g (linOut.getD k .x8)) 9 =
    num (fun k => (run inp subPrime (run inp primeOps (run inp addChain s))).g (linOut.getD k .x8)) 9 from
      sumTo_congr fun i hi => congrArg (pw i * ·) (q1 i hi)] at hF
  rw [addOps, run_append, run_append, run_append, run_append, hF]
  have hD := num_lt (n := 9)
    (f := fun k => (run inp subPrime (run inp primeOps (run inp addChain s))).g (linOut.getD k .x8)) fun i _ => o3.g _
  have hc3 := o3.c
  have hp0 : 0 < prime := prime_pos
  generalize num (fun k => (run inp subPrime (run inp primeOps (run inp addChain s))).g (linOut.getD k .x8)) 9 = D at hS hD ⊢
  generalize (run inp subPrime (run inp primeOps (run inp addChain s))).c = c at hS hc3 ⊢
  generalize num (inp 0) 9 + num (inp 1) 9 = N at hS hAB ⊢
  clear hF hN eP h
  generalize prime = p at *
  generalize pw 9 = w at *
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc3 with rfl | rfl
  · have e : D + p = w + N := by omega_using [hS]
    rw [Nat.sub_zero, Nat.mul_one, e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega_using [e, hD, hAB, hb2]),
      Nat.mod_eq_of_lt (by omega_using [e, hD])]
  · have e : N = D + p := by omega_using [hS]
    rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hD, e, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_using [e, hAB])]

/-! ## Multiples by powers of two, abstractly -/

private def shlE (k : Nat) : List Seg :=
  ((List.range 8).flatMap fun j => [⟨inpLoc 0 j, 0, 64 - k, pw j * 2 ^ k⟩, ⟨inpLoc 0 j, 64 - k, 64, pw (j + 1)⟩]) ++
    [⟨inpLoc 0 8, 0, 9 - k, pw 8 * 2 ^ k⟩, ⟨inpLoc 0 8, 9 - k, 9, 1⟩]

private theorem shlE_ev {inp : Nat → Nat → Nat} (hi : InB inp) (s : St) {k : Nat} (hk : k ≤ 8) :
    Cg prime (sumL inp s (shlE k)) (2 ^ k * num (inp 0) 9) := by
  have h : ∀ n ≤ 8, sumL inp s ((List.range n).flatMap fun j =>
      [⟨inpLoc 0 j, 0, 64 - k, pw j * 2 ^ k⟩, ⟨inpLoc 0 j, 64 - k, 64, pw (j + 1)⟩]) = 2 ^ k * num (inp 0) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, sumL_append, ih (by omega_using [hn]), num_succ, Nat.mul_add]
      congr 1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, sumL, Seg.ev, Nat.add_zero, Nat.pow_zero, Nat.div_one]
      rw [lv_inp inp s (by omega_using [hn]), Nat.mod_eq_of_lt (hi.w 0 n), pw_succ]
      have e : (2 : Nat) ^ 64 = 2 ^ k * 2 ^ (64 - k) := by rw [← Nat.pow_add]; congr 1; omega_using [hk]
      rw [e]
      generalize 2 ^ (64 - k) = Q
      generalize 2 ^ k = K
      rw [show K * Q * pw n * (inp 0 n / Q) = pw n * K * (Q * (inp 0 n / Q)) by ac_rfl, ← Nat.mul_add, Nat.mod_add_div]
      ac_rfl
  rw [shlE, sumL_append, h 8 (Nat.le_refl _), num_succ _ 8, Nat.mul_add]
  refine (Cg.refl _ _).add ?_
  have h8 := hi.b 0 8
  rw [show inB 0 8 = 511 from rfl] at h8
  simp only [sumL, Seg.ev, Nat.add_zero, Nat.pow_zero, Nat.div_one, Nat.one_mul]
  rw [lv_inp inp s (by decide), Nat.mod_eq_of_lt (a := inp 0 8) (b := 2 ^ 9) (by omega_using [h8])]
  have e9 : (2 : Nat) ^ 9 = 2 ^ k * 2 ^ (9 - k) := by rw [← Nat.pow_add]; congr 1; omega_using [hk]
  have hone : Cg prime (pw 8 * 2 ^ k * 2 ^ (9 - k)) 1 := by
    rw [Nat.mul_assoc, ← e9]; show _ % _ = _ % _; decide +kernel
  have hone' := (hone.mul (inp 0 8 / 2 ^ (9 - k))).symm
  rw [Nat.one_mul] at hone'
  refine ((Cg.refl _ _).add hone').trans (Cg.of_eq ?_)
  rw [Nat.mul_assoc (pw 8 * 2 ^ k), ← Nat.mul_add, Nat.mod_add_div]
  ac_rfl

private theorem shl_run {k : Nat} (hk : k ≤ 8)
    (hc : chkL prime (shlOps k) anyB (outFn prime 0 linOut 9) 0 0 (shlE k) = true)
    (ht : Nat.ble ((fwds inB (shlOps k) anyB).u (linOut.getD 8 .x8)) 511 = true)
    (hz : chkZero (zeroB 0) (shlOps k) linOut = true) {inp : Nat → Nat → Nat} (hi : InB inp) {s : St} (hs : Ok s)
    (hA : num (inp 0) 9 < prime) (h9 : ∀ i, 9 ≤ i → inp 0 i = 0) :
    num (fun j => (run inp (shlOps k) s).g (linOut.getD j .x8)) 9 = 2 ^ k * num (inp 0) 9 % prime := by
  have hO := run_Ok (inp := inp) hi.w (shlOps k) hs
  have e := ((outFn_ev (m := prime) (sh := 0) (out := linOut) (inp := inp) hO 9).symm.trans
    (chkL_ok prime_pos hc hi hs (anyB_ok hs))).trans (Cg.trans (Cg.of_eq (by rw [Nat.zero_mul, Nat.zero_add]))
      (shlE_ev hi s hk))
  rw [pw_zero, Nat.one_mul] at e
  have htop : (run inp (shlOps k) s).g (linOut.getD 8 .x8) ≤ 511 :=
    Nat.le_trans ((fwds_ok hi.w hi.b (shlOps k) anyB_wf hs (anyB_ok hs)).1.ub _) (Nat.le_of_ble_eq_true ht)
  have hl := num_lt (n := 8) (f := fun j => (run inp (shlOps k) s).g (linOut.getD j .x8)) fun i _ => hO.g _
  have hle : num (fun j => (run inp (shlOps k) s).g (linOut.getD j .x8)) 9 ≤ prime := by
    rw [num_succ, show prime = 2 ^ 521 - 1 from rfl]
    generalize num (fun j => (run inp (shlOps k) s).g (linOut.getD j .x8)) 8 = L at hl ⊢
    simp only [pw, Nat.reduceMul] at hl ⊢
    omega_using [hl, htop]
  have hne : num (fun j => (run inp (shlOps k) s).g (linOut.getD j .x8)) 9 ≠ prime := by
    intro hp
    have hz0 : num (inp 0) 9 = 0 := by
      have hd : prime ∣ 2 ^ k * num (inp 0) 9 := Nat.dvd_of_mod_eq_zero (by rw [← e, hp, Nat.mod_self])
      rcases (Nat.Prime.dvd_mul prime_prime).mp hd with h | h
      · have hlt : 2 ^ k < prime := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hk) (by decide +kernel)
        exact absurd (Nat.eq_zero_of_dvd_of_lt h hlt) (Nat.ne_of_gt (Nat.two_pow_pos k))
      · exact Nat.eq_zero_of_dvd_of_lt h hA
    have hr := chkZero_ok hz hi.w (zeroB_le hi fun i => if h : i < 9 then num_zero hz0 i h else h9 i (Nat.le_of_not_lt h)) hs
    rw [hr] at hp
    exact absurd hp (by decide +kernel)
  rw [← Nat.mod_eq_of_lt (Nat.lt_of_le_of_ne hle hne)]
  exact e

/-! ## On the machine -/

private theorem num_cons (f : Nat → Nat) (n : Nat) : num f (n + 1) = f 0 + 2 ^ 64 * num (fun i => f (i + 1)) n := by
  have h := num_split f n 0
  simp only [Nat.zero_add] at h
  rw [h]
  congr 3
  funext j
  rw [Nat.add_comm]

private theorem wordsVal_num (m : Mem) (base : Addr) : ∀ (n d : Nat),
    wordsVal m base d n = num (fun i => (word m base (d + 8 * i)).toNat) n
  | 0, _ => rfl
  | n + 1, d => by
    have e : (fun i => (word m base (d + 8 * (i + 1))).toNat) = fun i => (word m base (d + 8 + 8 * i)).toNat :=
      funext fun i => by rw [show d + 8 * (i + 1) = d + 8 + 8 * i by omega_using []]
    rw [wordsVal, num_cons, wordsVal_num m base n (d + 8), e, show d + 8 * 0 = d from rfl]

private theorem regsVal_num (s : State) : ∀ rs : List Reg,
    regsVal s rs = num (fun k => (s.gpr (rs.getD k .x8)).toNat) rs.length
  | [] => rfl
  | r :: rs => by
    rw [regsVal, List.length_cons, num_cons, regsVal_num s rs]
    rfl

/-- The words of the operands. -/
private def inps (m : Mem) (pa pb : Addr) (a b : Nat) (k i : Nat) : Nat :=
  if i < 9 then (if k = 0 then (word m pa (a + 8 * i)).toNat else (word m pb (b + 8 * i)).toNat) else 0

private theorem inps_num0 (m : Mem) (pa pb : Addr) (a b : Nat) : num (inps m pa pb a b 0) 9 = wordsVal m pa a 9 := by
  rw [wordsVal_num]
  exact sumTo_congr fun i hi => by rw [inps, ite_eq_left hi, ite_eq_left rfl]

private theorem inps_num1 (m : Mem) (pa pb : Addr) (a b : Nat) : num (inps m pa pb a b 1) 9 = wordsVal m pb b 9 := by
  rw [wordsVal_num]
  exact sumTo_congr fun i hi => by rw [inps, ite_eq_left hi, ite_eq_right (by decide)]

private theorem top_word {m : Mem} {p : Addr} {d : Nat} (h : wordsVal m p d 9 < prime) : (word m p (d + 8 * 8)).toNat ≤ 511 := by
  rw [wordsVal_num, num_succ] at h
  generalize (word m p (d + 8 * 8)).toNat = t at h ⊢
  generalize num (fun i => (word m p (d + 8 * i)).toNat) 8 = L at h
  rw [show prime = 2 ^ 521 - 1 from rfl] at h
  simp only [pw, Nat.reduceMul] at h
  omega_using [h]

private theorem inps_ok {m : Mem} {pa pb : Addr} {a b : Nat} (hA : wordsVal m pa a 9 < prime)
    (hB : wordsVal m pb b 9 < prime) : InB (inps m pa pb a b) := by
  have hw : ∀ k i, inps m pa pb a b k i < 2 ^ 64 := fun k i => by
    unfold inps
    split
    · split <;> exact BitVec.isLt _
    · decide
  refine ⟨hw, fun k i => ?_⟩
  unfold inB
  cases hb : Nat.ble i 7 with
  | true => have := hw k i; show _ ≤ 2 ^ 64 - 1; omega_using [this]
  | false =>
    rw [ite_eq_right (by decide)]
    by_cases h9 : i < 9
    · have h7 : ¬i ≤ 7 := fun h => by rw [Nat.ble_eq_true_of_le h] at hb; cases hb
      obtain rfl : i = 8 := by omega_using [h7, h9]
      rw [inps, ite_eq_left h9]
      split
      · exact top_word hA
      · exact top_word hB
    · rw [inps, ite_eq_right h9]; exact Nat.zero_le _

/-- The shifts of a sequence and the words it loads can be encoded, and it
writes only registers that an operation may. -/
private def encB (k9 : Nat) (os : List Op) : Bool :=
  os.all fun o => decide (o.dst ∈ clob 9) && match o with
    | .ld k i _ => Nat.blt k k9 && Nat.blt i 9
    | .lsl _ _ k | .lsr _ _ k | .extr _ _ _ k => Nat.blt k 64
    | _ => true

private theorem encB_ok {k9 : Nat} {os : List Op} (h : encB k9 os = true) {ra rb : Reg} {a b : Nat} (hra : ra ∉ clob 9)
    (hrb : rb ∉ clob 9) : (∀ o ∈ os, Enc (fun k => if k = 0 then (ra, a) else (rb, b)) (fun k i => k < k9 ∧ i < 9) o) ∧
      ∀ r ∈ dsts os, r ∈ clob 9 := by
  have hp : ∀ o ∈ os, o.dst ∈ clob 9 := fun o ho => by
    have := List.all_eq_true.mp h o ho
    rw [Bool.and_eq_true] at this
    exact of_decide_eq_true this.1
  have hq : ∀ o ∈ os, ∀ q : Nat, (if q = 0 then (ra, a) else (rb, b)).1 ≠ o.dst := fun o ho q e => by
    have hd := hp o ho
    rw [← e] at hd
    split at hd
    · exact hra hd
    · exact hrb hd
  refine ⟨fun o ho => ?_, fun r hr => ?_⟩
  · have h1 := List.all_eq_true.mp h o ho
    rw [Bool.and_eq_true] at h1
    have h2 := h1.2
    have h3 := hq o ho
    cases o with
    | ld k i d =>
      rw [Bool.and_eq_true] at h2
      exact ⟨⟨Nat.blt_eq.mp h2.1, Nat.blt_eq.mp h2.2⟩, h3⟩
    | lsl d n k => exact ⟨Nat.blt_eq.mp h2, h3⟩
    | lsr d n k => exact ⟨Nat.blt_eq.mp h2, h3⟩
    | extr d n m k => exact ⟨Nat.blt_eq.mp h2, h3⟩
    | _ => exact h3
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hr
    exact hp o ho

/-- A sequence on operands in memory, its result stored. -/
private theorem op_ok {k9 : Nat} {os : List Op} {out : List Reg} (he : encB k9 os = true) (hk : k9 ≤ 2) (hl : out.length = 9)
    (hn : out.Nodup) {s : State} {ra rb ro : Reg} {pa pb po : Addr} {sa sb so : Nat} (hpa : Ptr s ra pa sa)
    (hpb : Ptr s rb pb sb) (hpo : PtrW s ro po so) (hra : ra ∉ clob 9) (hrb : rb ∉ clob 9) (hro : ro ∉ clob 9) {o a b : Nat}
    (ho : o + 72 ≤ so) (ha : a + 72 ≤ sa) (hb : b + 72 ≤ sb) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0) :
    WP isa (.block (code ra rb a b os ++ storesR ro out o)) s fun t => OpKeepR 9 po o s t ∧
      wordsVal t.mem po o 9 = num (fun k => (run (inps s.mem pa pb a b) os (ofState s)).g (out.getD k .x8)) 9 := by
  obtain ⟨e1, e2⟩ := encB_ok he (a := a) (b := b) hra hrb
  have hi : InOk (fun k => if k = 0 then (ra, a) else (rb, b)) (fun k i => k < k9 ∧ i < 9) (inps s.mem pa pb a b) s := by
    refine ⟨fun k i hki => ?_, fun k i hki => ?_, fun k i hki => ?_⟩
    · split
      · rw [hpa.reg]; exact hpa.ld _ (by omega_using [ha, hki.2])
      · rw [hpb.reg]; exact hpb.ld _ (by omega_using [hb, hki.2])
    · have := hpa.enc
      have := hpb.enc
      split <;> dsimp only <;> omega_arith
    · rw [inps, ite_eq_left hki.2]
      split
      · rw [hpa.reg]
      · rw [hpb.reg]
  rw [WP.block_append_iff]
  refine WP.mono (run_ok os hi e1) fun u ⟨hr, hku, _⟩ => ?_
  have hku := hku.mono e2
  refine WP.mono (storesR_ok out (hpo.of_keepRegs (Keeps.regs hku) hro) (o := o) (by rw [hl]; exact ho) ho8 hn)
    fun t ⟨v, kt, O⟩ => ?_
  rw [hl] at v O
  rw [hku.mem] at O
  refine ⟨⟨fun r h => (kt.gpr r (by simp)).trans (hku.gpr r h), kt.rd.trans hku.rd, kt.wr.trans hku.wr, kt.sp.trans hku.sp, O⟩, ?_⟩
  rw [v, regsVal_num, hl, ← hr]
  rfl

/-- `[ro + o] = [ra + a] [rb + b] R⁻¹ mod p`. -/
theorem mulR_ok {s : State} {ra rb ro : Reg} {pa pb po : Addr} {sa sb so : Nat} (hpa : Ptr s ra pa sa)
    (hpb : Ptr s rb pb sb) (hpo : PtrW s ro po so) (hra : ra ∉ clob 9) (hrb : rb ∉ clob 9) (hro : ro ∉ clob 9) {o a b : Nat}
    (ho : o + 72 ≤ so) (ha : a + 72 ≤ sa) (hb : b + 72 ≤ sb) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hA : wordsVal s.mem pa a 9 < prime) (hB : wordsVal s.mem pb b 9 < prime) :
    WP isa (.block (mulR ra rb ro o a b)) s fun t => OpKeepR 9 po o s t ∧ wordsVal t.mem po o 9 < prime ∧
      wordsVal t.mem po o 9 * 2 ^ (64 * 9) % prime = wordsVal s.mem pa a 9 * wordsVal s.mem pb b 9 % prime := by
  refine WP.mono (op_ok (k9 := 2) (by decide +kernel) (by decide) rfl (by decide) hpa hpb hpo hra hrb hro ho ha hb ho8 ha8 hb8)
    fun t ⟨k, v⟩ => ⟨k, ?_⟩
  have h := mul_run (inps_ok hA hB) (ofState_ok s) (by rw [inps_num0]; exact hA) (by rw [inps_num1]; exact hB)
    fun k i h => by rw [inps, ite_eq_right (Nat.not_lt_of_le h)]
  rw [← v, inps_num0, inps_num1] at h
  exact h

/-- `[ro + o] = [ra + a]^2 R⁻¹ mod p`. -/
theorem sqrR_ok {s : State} {ra ro : Reg} {pa po : Addr} {sa so : Nat} (hpa : Ptr s ra pa sa)
    (hpo : PtrW s ro po so) (hra : ra ∉ clob 9) (hro : ro ∉ clob 9) {o a : Nat}
    (ho : o + 72 ≤ so) (ha : a + 72 ≤ sa) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hA : wordsVal s.mem pa a 9 < prime) :
    WP isa (.block (sqrR ra ro o a)) s fun t => OpKeepR 9 po o s t ∧ wordsVal t.mem po o 9 < prime ∧
      wordsVal t.mem po o 9 * 2 ^ (64 * 9) % prime = wordsVal s.mem pa a 9 * wordsVal s.mem pa a 9 % prime := by
  refine WP.mono (op_ok (k9 := 1) (by decide +kernel) (by decide) rfl (by decide) hpa hpa hpo hra hra hro ho ha ha ho8 ha8 ha8)
    fun t ⟨k, v⟩ => ⟨k, ?_⟩
  have h := sqr_run (inps_ok hA hA) (ofState_ok s) (by rw [inps_num0]; exact hA)
    fun k i h => by rw [inps, ite_eq_right (Nat.not_lt_of_le h)]
  rw [← v, inps_num0] at h
  exact h

private theorem linKeep {M : Mod} {base : Addr} {o : Nat} {s t : State} (hn : M.n = 9) (k : OpKeepR 9 base o s t) :
    OpKeep M base o s t :=
  ⟨fun r hr => k.gpr r (by rwa [hn] at hr), k.rd, k.wr, k.sp, fun x hx _ => k.mem x (by rwa [hn] at hx)⟩

theorem toOpKeep {M : Mod} {base : Addr} {o : Nat} {s t : State} (hn : M.n = 9) (k : OpKeepR 9 base o s t) :
    OpKeep M base o s t := linKeep hn k

/-- `[o] = [a] + [b] mod p`. -/
theorem add_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o a b : Nat} (ho : o + 72 ≤ size)
    (ha : a + 72 ≤ size) (hb : b + 72 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hA : wordsVal s.mem base a 9 < prime) (hB : wordsVal s.mem base b 9 < prime) :
    WP isa (.block (add o a b)) s fun t => OpKeepR 9 base o s t ∧
      wordsVal t.mem base o 9 = (wordsVal s.mem base a 9 + wordsVal s.mem base b 9) % prime := by
  refine WP.mono (op_ok (k9 := 2) (by decide +kernel) (by decide) rfl (by decide) hs.ptr hs.ptr hs.ptrW (by decide) (by decide)
    (by decide) ho ha hb ho8 ha8 hb8) fun t ⟨k, v⟩ => ⟨k, ?_⟩
  have h := add_run (inps_ok hA hB) (ofState_ok s) (by rw [inps_num0, inps_num1]; omega_using [hA, hB])
  rw [← v, inps_num0, inps_num1] at h
  exact h

/-- `[o] = [a] - [b] mod p`. -/
theorem sub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o a b : Nat} (ho : o + 72 ≤ size)
    (ha : a + 72 ≤ size) (hb : b + 72 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hb8 : b % 8 = 0)
    (hA : wordsVal s.mem base a 9 < prime) (hB : wordsVal s.mem base b 9 < prime) :
    WP isa (.block (sub o a b)) s fun t => OpKeepR 9 base o s t ∧
      wordsVal t.mem base o 9 = (wordsVal s.mem base a 9 + prime - wordsVal s.mem base b 9) % prime := by
  refine WP.mono (op_ok (k9 := 2) (by decide +kernel) (by decide) rfl (by decide) hs.ptr hs.ptr hs.ptrW (by decide) (by decide)
    (by decide) ho ha hb ho8 ha8 hb8) fun t ⟨k, v⟩ => ⟨k, ?_⟩
  have h := sub_run (inps_ok hA hB) (ofState_ok s) (by rw [inps_num0]; exact hA) (by rw [inps_num1]; exact hB)
  rw [← v, inps_num0, inps_num1] at h
  exact h

/-- `[o] = 2^k [a] mod p`. -/
theorem shl_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {k o a : Nat} (hk : k = 1 ∨ k = 2 ∨ k = 3)
    (ho : o + 72 ≤ size) (ha : a + 72 ≤ size) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0) (hA : wordsVal s.mem base a 9 < prime) :
    WP isa (.block (shl k o a)) s fun t => OpKeepR 9 base o s t ∧
      wordsVal t.mem base o 9 = 2 ^ k * wordsVal s.mem base a 9 % prime := by
  have key : encB 1 (shlOps k) = true ∧ chkL prime (shlOps k) anyB (outFn prime 0 linOut 9) 0 0 (shlE k) = true ∧
      Nat.ble ((fwds inB (shlOps k) anyB).u (linOut.getD 8 .x8)) 511 = true ∧ chkZero (zeroB 0) (shlOps k) linOut = true := by
    rcases hk with rfl | rfl | rfl <;> decide +kernel
  refine WP.mono (op_ok (k9 := 1) key.1 (by decide) rfl (by decide) hs.ptr hs.ptr hs.ptrW (by decide) (by decide)
    (by decide) ho ha ha ho8 ha8 ha8) fun t ⟨kk, v⟩ => ⟨kk, ?_⟩
  have h := shl_run (by rcases hk with rfl | rfl | rfl <;> decide) key.2.1 key.2.2.1 key.2.2.2 (inps_ok hA hA) (ofState_ok s)
    (by rw [inps_num0]; exact hA) fun i h => by rw [inps, ite_eq_right (Nat.not_lt_of_le h)]
  rw [← v, inps_num0] at h
  exact h

end VG.Proof.Mont.AArch64.P521
