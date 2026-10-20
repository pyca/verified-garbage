module

public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.Omega

/-! Separate each sampling trace from its following signing-result marker. -/
@[expose] public section
namespace VG.Proof.Dsa
open VG.Spec.Dsa

def randomSamplingTrace (trace : List Nat) : List Nat := trace.takeWhile (· < 5)
def randomSigningTrace (trace : List Nat) : List Nat := trace.dropWhile (· < 5)

theorem random_sample_trace_small (q fuel : Nat) (rand : List VG.Byte) :
    ∀ x ∈ (VG.Spec.Dsa.Random.sample q fuel rand).trace, x < 5 := by
  induction fuel generalizing rand with
  | zero => intro x hx; simp only [VG.Spec.Dsa.Random.sample, List.mem_singleton] at hx; omega
  | succ fuel ih =>
    rw [VG.Spec.Dsa.Random.sample]
    split
    · intro x hx; simp only [List.mem_singleton] at hx; omega
    · dsimp only
      split
      · intro x hx; simp only [List.mem_singleton] at hx; omega
      · split
        · intro x hx; simp only [List.mem_singleton] at hx; omega
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · decide
          · exact ih _ x hx

private theorem take_small (xs : List Nat) (h : ∀ x ∈ xs, x < 5) : randomSamplingTrace xs = xs := by
  have hh := List.takeWhile_append_of_pos (p := fun x => decide (x < 5)) (l₂ := [])
    (fun x hx => decide_eq_true (h x hx))
  unfold randomSamplingTrace
  simpa only [List.append_nil, List.takeWhile_nil] using hh

private theorem take_marker (xs ys : List Nat) (marker : Nat) (hm : 5 ≤ marker)
    (h : ∀ x ∈ xs, x < 5) : randomSamplingTrace (xs ++ marker :: ys) = xs := by
  unfold randomSamplingTrace
  rw [List.takeWhile_append_of_pos (fun x hx => decide_eq_true (h x hx)),
    List.takeWhile_cons_of_neg (by simp only [decide_eq_true_eq]; omega), List.append_nil]

private theorem drop_marker (xs ys : List Nat) (marker : Nat) (hm : 5 ≤ marker)
    (h : ∀ x ∈ xs, x < 5) : randomSigningTrace (xs ++ marker :: ys) = marker :: ys := by
  unfold randomSigningTrace
  rw [List.dropWhile_append_of_pos (fun x hx => decide_eq_true (h x hx)),
    List.dropWhile_cons_of_neg (by simp only [decide_eq_true_eq]; omega)]

theorem random_sign_trace_draw (p : RandomSignInput) (used fuel : Nat) :
    randomSamplingTrace (randomSignRemaining p used (fuel + 1)).trace = (randomSignDraw p used).trace := by
  unfold randomSignRemaining
  rw [randomSignLoop]
  cases hd : (randomSignDraw p used).scalar with
  | none =>
    change randomSamplingTrace ((match (randomSignDraw p used).scalar with
      | none => _ | some k => _ : RandomSignResult).trace) = _
    simp only [hd]
    exact take_small _ (random_sample_trace_small _ _ _)
  | some k =>
    change randomSamplingTrace ((match (randomSignDraw p used).scalar with
      | none => _ | some k => _ : RandomSignResult).trace) = _
    simp only [hd]
    split
    · exact take_marker _ [] 5 (by decide) (random_sample_trace_small _ _ _)
    · simp only [List.append_assoc, List.cons_append, List.nil_append]
      exact take_marker (randomSignDraw p used).trace _ 6 (by decide) (random_sample_trace_small _ _ _)

theorem random_sign_trace_none (p : RandomSignInput) (used fuel : Nat)
    (hd : (randomSignDraw p used).scalar = none) :
    randomSigningTrace (randomSignRemaining p used (fuel + 1)).trace = [] := by
  unfold randomSignRemaining
  rw [randomSignLoop]
  change randomSigningTrace ((match (randomSignDraw p used).scalar with
    | none => _ | some k => _ : RandomSignResult).trace) = _
  simp only [hd]
  have hh := List.dropWhile_append_of_pos (p := fun x => decide (x < 5)) (l₂ := [])
    (l₁ := (randomSignDraw p used).trace)
    (fun x hx => decide_eq_true (random_sample_trace_small _ _ _ x hx))
  unfold randomSigningTrace
  simp only [List.append_nil, List.dropWhile_nil] at hh
  exact hh

theorem random_sign_trace_success (p : RandomSignInput) (used fuel k : Nat) {sig : List VG.Byte}
    (hd : (randomSignDraw p used).scalar = some k)
    (hs : signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest = some sig) :
    randomSigningTrace (randomSignRemaining p used (fuel + 1)).trace = [5] := by
  unfold randomSignRemaining
  rw [randomSignLoop_step_success _ _ _ _ _ _ _ _ hd hs]
  exact drop_marker _ [] 5 (by decide) (random_sample_trace_small _ _ _)

theorem random_sign_trace_retry (p : RandomSignInput) (used fuel k : Nat)
    (hd : (randomSignDraw p used).scalar = some k)
    (hs : signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest = none) :
    randomSigningTrace (randomSignRemaining p used (fuel + 1)).trace =
      6 :: (randomSignRemaining p (used + (randomSignDraw p used).used) fuel).trace := by
  rw [randomSignRemaining_retry p used fuel k hd hs]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  exact drop_marker _ _ 6 (by decide) (random_sample_trace_small _ _ _)

theorem random_sign_trace_call {p r : RandomSignInput} {used fuel k l : Nat}
    (htrace : (randomSignRemaining p used (fuel + 1)).trace = (randomSignRemaining r used (fuel + 1)).trace)
    (hp : (randomSignDraw p used).scalar = some k) (hr : (randomSignDraw r used).scalar = some l) :
    (signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest).isSome =
      (signBytes r.pLen r.qLen r.key (encodeBE r.qLen l) r.digest).isSome := by
  have hh := congrArg randomSigningTrace htrace
  cases hs : signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest with
  | none =>
    cases ht : signBytes r.pLen r.qLen r.key (encodeBE r.qLen l) r.digest with
    | none => rfl
    | some sig =>
      rw [random_sign_trace_retry p used fuel k hp hs, random_sign_trace_success r used fuel l hr ht] at hh
      cases hh
  | some sig =>
    cases ht : signBytes r.pLen r.qLen r.key (encodeBE r.qLen l) r.digest with
    | some sig' => rfl
    | none =>
      rw [random_sign_trace_success p used fuel k hp hs, random_sign_trace_retry r used fuel l hr ht] at hh
      cases hh

theorem random_sign_trace_next {p r : RandomSignInput} {used fuel k l : Nat}
    (htrace : (randomSignRemaining p used (fuel + 1)).trace = (randomSignRemaining r used (fuel + 1)).trace)
    (hp : (randomSignDraw p used).scalar = some k) (hr : (randomSignDraw r used).scalar = some l)
    (hs : signBytes p.pLen p.qLen p.key (encodeBE p.qLen k) p.digest = none)
    (ht : signBytes r.pLen r.qLen r.key (encodeBE r.qLen l) r.digest = none) :
    (randomSignRemaining p (used + (randomSignDraw p used).used) fuel).trace =
      (randomSignRemaining r (used + (randomSignDraw r used).used) fuel).trace := by
  have hh := congrArg randomSigningTrace htrace
  rw [random_sign_trace_retry p used fuel k hp hs, random_sign_trace_retry r used fuel l hr ht] at hh
  exact List.cons.inj hh |>.2

end VG.Proof.Dsa
