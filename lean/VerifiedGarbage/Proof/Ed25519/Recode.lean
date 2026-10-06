/-!
# Signed sliding-window digits

Verification recodes each scalar `K < 2 ^ n` into signed digits (`step`), from its lowest bit,
with a carry `c ∈ {0, 1}`: at bit `i`, a bit equal to `c` gives a zero digit and keeps `c`;
otherwise the `w` bits from `i` plus `c` make an odd `W ≤ 2 ^ w`, and the digit is `W` (carry
0) if `W < 2 ^ (w - 1)`, else `W - 2 ^ w` (carry 1), followed by `w - 1` zero digits. After the
last bit the carry, if any, is the digit 1 (`fin`). A digit `d` is kept as the byte `u = d` if
positive and `u = 1 - d` if negative (`dec` reads it back), so `u - 1` is its entry in a table
whose entries `2m` and `2m + 1` are `[2m + 1]` and `-[2m + 1]` of a point.

`digits_sum`: the digits, weighted by powers of two (`hsum`), sum to `K`; `digits_le`: each byte
is at most `2 ^ (w - 1)`; `digits_zero`: they are zero from bit `n + w` on.
-/

namespace VG.Proof.Ed25519.Recode

/-- A digit's value from its byte: `u` if odd, `1 - u` if even, `0` for `0`. -/
def dec (u : Nat) : Int := if u = 0 then 0 else if u % 2 = 1 then u else 1 - u

/-- `∑ j < n, f (p + j) 2 ^ j`. -/
def hsum (f : Nat → Int) : Nat → Nat → Int
  | _, 0 => 0
  | p, n + 1 => f p + 2 * hsum f (p + 1) n

theorem hsum_zero (f : Nat → Int) (p : Nat) : hsum f p 0 = 0 := rfl

theorem hsum_succ (f : Nat → Int) (p n : Nat) : hsum f p (n + 1) = f p + 2 * hsum f (p + 1) n := rfl

theorem hsum_add (f : Nat → Int) (p a b : Nat) :
    hsum f p (a + b) = hsum f p a + 2 ^ a * hsum f (p + a) b := by
  induction a generalizing p with
  | zero => simp [hsum]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, hsum_succ, ih, hsum_succ,
      show p + 1 + a = p + (a + 1) by omega, Int.pow_succ]
    grind

theorem hsum_one (f : Nat → Int) (p : Nat) : hsum f p 1 = f p := by simp [hsum]

theorem hsum_snoc (f : Nat → Int) (p n : Nat) : hsum f p (n + 1) = hsum f p n + 2 ^ n * f (p + n) := by
  rw [hsum_add, hsum_one]

theorem hsum_congr {f g : Nat → Int} {p n : Nat} (h : ∀ j, p ≤ j → j < p + n → f j = g j) :
    hsum f p n = hsum g p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [hsum_succ, hsum_succ, h p (by omega) (by omega), ih fun j h1 h2 => h j (by omega) (by omega)]

theorem hsum_eq_zero {f : Nat → Int} {p n : Nat} (h : ∀ j, p ≤ j → j < p + n → f j = 0) :
    hsum f p n = 0 := by
  rw [hsum_congr (g := fun _ => 0) h]
  clear h
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [hsum_succ, ih]; rfl

/-- The recoding's state: the bit `i`, the carry `c` and the digits' bytes so far. -/
structure St where
  i : Nat
  c : Nat
  u : Nat → Nat

/-- `u` with `v` at `i`. -/
def upd (u : Nat → Nat) (i v : Nat) (j : Nat) : Nat := if j = i then v else u j

theorem upd_self (u : Nat → Nat) (i v : Nat) : upd u i v i = v := by simp [upd]

theorem upd_ne (u : Nat → Nat) {i j : Nat} (v : Nat) (h : j ≠ i) : upd u i v j = u j := by simp [upd, h]

/-- The start: bit 0, no carry, no digits. -/
def init : St := ⟨0, 0, fun _ => 0⟩

/-- One step from bit `i` (see the module's description). -/
def step (w K : Nat) (s : St) : St :=
  if K / 2 ^ s.i % 2 = s.c then ⟨s.i + 1, s.c, s.u⟩
  else if K / 2 ^ s.i % 2 ^ w + s.c < 2 ^ (w - 1) then
    ⟨s.i + w, 0, upd s.u s.i (K / 2 ^ s.i % 2 ^ w + s.c)⟩
  else ⟨s.i + w, 1, upd s.u s.i (2 ^ w + 1 - (K / 2 ^ s.i % 2 ^ w + s.c))⟩

/-- The steps while the bit is below `n`, at most `f` of them. -/
def run (w K n : Nat) : Nat → St → St
  | 0, s => s
  | f + 1, s => if s.i < n then run w K n f (step w K s) else s

/-- The digits' bytes after the steps, with the last carry as the digit 1 at its bit. -/
def fin (s : St) (j : Nat) : Nat := if s.c ≠ 0 ∧ j = s.i then 1 else s.u j

/-- The digits' bytes of `K < 2 ^ n`. -/
def digits (w K n : Nat) : Nat → Nat := fin (run w K n n init)

/-- What every state of the recoding satisfies. -/
structure Good (w K : Nat) (s : St) : Prop where
  c : s.c ≤ 1
  above : ∀ j, s.i ≤ j → s.u j = 0
  le : ∀ j, s.u j ≤ 2 ^ (w - 1)
  sum : hsum (fun j => dec (s.u j)) 0 s.i + s.c * 2 ^ s.i = (K % 2 ^ s.i : Nat)

theorem init_good (w K : Nat) : Good w K init :=
  ⟨Nat.zero_le _, fun _ _ => rfl, fun _ => Nat.zero_le _, by simp [init, hsum]⟩

theorem dec_odd {W : Nat} (h : W % 2 = 1) : dec W = W := by
  simp only [dec, h, ite_true]
  rw [ite_eq_right_iff.mpr (by omega)]

theorem dec_even {u : Nat} (h0 : u ≠ 0) (h : u % 2 = 0) : dec u = 1 - u := by
  simp only [dec, h0, ite_false]
  rw [ite_eq_right_iff.mpr (by omega)]

theorem step_good {w K : Nat} (hw : 2 ≤ w) {s : St} (h : Good w K s) : Good w K (step w K s) := by
  obtain ⟨hc, habove, hle, hsum'⟩ := h
  have hpw : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [show 2 ^ w = 2 ^ ((w - 1) + 1) by congr 1; omega, Nat.pow_succ']
  have hpw1 : 2 ^ (w - 1) = 2 * 2 ^ (w - 2) := by
    rw [show 2 ^ (w - 1) = 2 ^ ((w - 2) + 1) by congr 1; omega, Nat.pow_succ']
  have hp2 : 0 < 2 ^ (w - 2) := Nat.two_pow_pos _
  have hKw : K % 2 ^ (s.i + w) = K % 2 ^ s.i + 2 ^ s.i * (K / 2 ^ s.i % 2 ^ w) := by
    rw [Nat.pow_add, Nat.mod_mul]
  have hK1 : K % 2 ^ (s.i + 1) = K % 2 ^ s.i + 2 ^ s.i * (K / 2 ^ s.i % 2) := Nat.mod_pow_succ
  have hmod2 : K / 2 ^ s.i % 2 ^ w % 2 = K / 2 ^ s.i % 2 := by rw [hpw, Nat.mod_mul_right_mod]
  have hlt : K / 2 ^ s.i % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hb : K / 2 ^ s.i % 2 < 2 := Nat.mod_lt _ (by decide)
  have hsplit : ∀ (v : Nat → Nat), (∀ j, j ≠ s.i → v j = s.u j) →
      hsum (fun j => dec (v j)) 0 (s.i + w) =
        hsum (fun j => dec (s.u j)) 0 s.i + 2 ^ s.i * dec (v s.i) := by
    intro v hv
    have e1 := hsum_add (fun j => dec (v j)) 0 s.i w
    have e2 := hsum_add (fun j => dec (v j)) s.i 1 (w - 1)
    rw [show 1 + (w - 1) = w by omega] at e2
    have e3 : hsum (fun j => dec (v j)) (s.i + 1) (w - 1) = 0 :=
      hsum_eq_zero (fun j h1 h2 => by rw [hv j (by omega), habove j (by omega)]; rfl)
    have e4 : hsum (fun j => dec (v j)) 0 s.i = hsum (fun j => dec (s.u j)) 0 s.i :=
      hsum_congr (fun j _ h2 => by rw [hv j (by omega)])
    simp only [Nat.zero_add, hsum] at e1 e2
    rw [e1, e2, e3, e4]
    grind
  have hsplit1 : hsum (fun j => dec (s.u j)) 0 (s.i + 1) = hsum (fun j => dec (s.u j)) 0 s.i := by
    rw [hsum_add, Nat.zero_add, hsum_succ, hsum_zero, habove s.i (Nat.le_refl _)]
    simp [dec]
  have hP : ((2 ^ s.i : Nat) : Int) = (2 : Int) ^ s.i := Int.natCast_pow _ _
  unfold step
  generalize K / 2 ^ s.i % 2 ^ w = Wm at *
  generalize K / 2 ^ s.i % 2 = b at *
  generalize K % 2 ^ s.i = Q at *
  split
  · rename_i heq
    refine ⟨hc, fun j hj => habove j (by dsimp only at hj; omega), hle, ?_⟩
    dsimp only
    rw [hsplit1, hK1, Int.pow_succ]
    push_cast
    rw [heq]
    grind
  · rename_i hne
    have hbc : b + s.c = 1 := by omega
    have hodd : (Wm + s.c) % 2 = 1 := by omega
    split
    · rename_i hW
      refine ⟨Nat.zero_le _, fun j hj => ?_, fun j => ?_, ?_⟩
      · dsimp only at hj ⊢
        rw [upd_ne _ _ (show j ≠ s.i by omega)]; exact habove j (by omega)
      · dsimp only
        by_cases hj : j = s.i
        · rw [hj, upd_self]; omega
        · rw [upd_ne _ _ hj]; exact hle j
      · dsimp only
        rw [hsplit _ (fun j hj => upd_ne _ _ hj), upd_self, dec_odd hodd, hKw]
        push_cast
        grind
    · rename_i hW
      refine ⟨Nat.le_refl _, fun j hj => ?_, fun j => ?_, ?_⟩
      · dsimp only at hj ⊢
        rw [upd_ne _ _ (show j ≠ s.i by omega)]; exact habove j (by omega)
      · dsimp only
        by_cases hj : j = s.i
        · rw [hj, upd_self]; omega
        · rw [upd_ne _ _ hj]; exact hle j
      · dsimp only
        rw [hsplit _ (fun j hj => upd_ne _ _ hj), upd_self,
          dec_even (by omega) (by omega), hKw, Int.ofNat_sub (by omega), Int.pow_add]
        push_cast
        grind

theorem step_i {w K : Nat} (hw : 1 ≤ w) (s : St) : s.i + 1 ≤ (step w K s).i ∧ (step w K s).i ≤ s.i + w := by
  unfold step; split
  · exact ⟨Nat.le_refl _, by simp only; omega⟩
  · split <;> exact ⟨by simp only; omega, Nat.le_refl _⟩

theorem run_succ {w K n f : Nat} {s : St} (h : s.i < n) : run w K n (f + 1) s = run w K n f (step w K s) := by
  simp only [run, h, ↓reduceIte]

theorem run_stop {w K n f : Nat} {s : St} (h : n ≤ s.i) : run w K n f s = s := by
  cases f <;> simp only [run, show ¬ s.i < n by omega, ↓reduceIte]

theorem run_good {w K n : Nat} (hw : 2 ≤ w) (f : Nat) {s : St} (h : Good w K s) :
    Good w K (run w K n f s) := by
  induction f generalizing s with
  | zero => exact h
  | succ f ih =>
    by_cases hi : s.i < n
    · rw [run_succ hi]; exact ih (step_good hw h)
    · rw [run_stop (by omega)]; exact h

/-- Enough fuel ends past bit `n`. -/
theorem run_end {w K n : Nat} (hw : 1 ≤ w) (f : Nat) {s : St} (hf : n - s.i ≤ f) :
    n ≤ (run w K n f s).i := by
  induction f generalizing s with
  | zero => rw [run_stop (by omega)]; omega
  | succ f ih =>
    by_cases hi : s.i < n
    · rw [run_succ hi]; exact ih (by have := (step_i hw (K := K) s).1; omega)
    · rw [run_stop (by omega)]; omega

/-- The steps end before bit `n + w`. -/
theorem run_lt {w K n : Nat} (hw : 1 ≤ w) (f : Nat) {s : St} (hs : s.i < n + w) :
    (run w K n f s).i < n + w := by
  induction f generalizing s with
  | zero => exact hs
  | succ f ih =>
    by_cases hi : s.i < n
    · rw [run_succ hi]; exact ih (by have := (step_i hw (K := K) s).2; omega)
    · rw [run_stop (by omega)]; exact hs

/-- Enough fuel, however much, gives the same end. -/
theorem run_fuel {w K n : Nat} (hw : 1 ≤ w) (f g : Nat) {s : St} (hf : n - s.i ≤ f) (hg : n - s.i ≤ g) :
    run w K n f s = run w K n g s := by
  induction f generalizing s g with
  | zero => rw [run_stop (by omega), run_stop (by omega)]
  | succ f ih =>
    by_cases hi : s.i < n
    · obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      rw [run_succ hi, run_succ hi]
      have := (step_i hw (K := K) s).1
      exact ih g (by omega) (by omega)
    · rw [run_stop (by omega), run_stop (by omega)]

/-- A state the recoding reaches, from which it ends at `run w K n n init`. -/
def Reach (w K n : Nat) (s : St) : Prop := run w K n (n - s.i) s = run w K n n init

theorem reach_init (w K n : Nat) : Reach w K n init := by
  simp only [Reach, init, Nat.sub_zero]

theorem reach_step {w K n : Nat} (hw : 1 ≤ w) {s : St} (h : Reach w K n s) (hi : s.i < n) :
    Reach w K n (step w K s) := by
  unfold Reach at *
  rw [← h, show n - s.i = (n - s.i - 1) + 1 by omega, run_succ hi]
  have := (step_i hw (K := K) s).1
  exact run_fuel hw _ _ (by omega) (by omega)

theorem reach_end {w K n : Nat} {s : St} (h : Reach w K n s) (hi : n ≤ s.i) :
    s = run w K n n init := by
  unfold Reach at h
  rw [← h, run_stop hi]

theorem fin_ne (s : St) {j : Nat} (h : j ≠ s.i) : fin s j = s.u j := by simp [fin, h]

/-- The digits' bytes are at most `2 ^ (w - 1)`. -/
theorem digits_le {w K n : Nat} (hw : 2 ≤ w) (j : Nat) : digits w K n j ≤ 2 ^ (w - 1) := by
  unfold digits fin
  split
  · exact Nat.one_le_two_pow
  · exact (run_good hw n (init_good w K)).le j

/-- The digits are zero from bit `n + w` on. -/
theorem digits_zero {w K n : Nat} (hw : 2 ≤ w) {j : Nat} (hj : n + w ≤ j) : digits w K n j = 0 := by
  have hl : (run w K n n init).i < n + w := run_lt (by omega) n (by simp only [init]; omega)
  have hg : Good w K (run w K n n init) := run_good hw n (init_good w K)
  unfold digits
  generalize run w K n n init = F at *
  rw [fin_ne _ (by omega)]
  exact hg.above j (by omega)

/-- The digits sum to `K`. -/
theorem digits_sum {w K n : Nat} (hw : 2 ≤ w) (hK : K < 2 ^ n) {N : Nat} (hN : n + w ≤ N) :
    hsum (fun j => dec (digits w K n j)) 0 N = K := by
  have hg : Good w K (run w K n n init) := run_good hw n (init_good w K)
  have he : n ≤ (run w K n n init).i := run_end (by omega) n (by simp only [init]; omega)
  have hl : (run w K n n init).i < n + w := run_lt (by omega) n (by simp only [init]; omega)
  unfold digits
  generalize run w K n n init = F at *
  have e1 := hsum_add (fun j => dec (fin F j)) 0 (F.i + 1) (N - F.i - 1)
  rw [show F.i + 1 + (N - F.i - 1) = N by omega, Nat.zero_add] at e1
  have e2 : hsum (fun j => dec (fin F j)) (F.i + 1) (N - F.i - 1) = 0 :=
    hsum_eq_zero fun j h1 _ => by rw [fin_ne _ (by omega), hg.above j (by omega)]; rfl
  have e3 := hsum_snoc (fun j => dec (fin F j)) 0 F.i
  have e4 : hsum (fun j => dec (fin F j)) 0 F.i = hsum (fun j => dec (F.u j)) 0 F.i :=
    hsum_congr fun j _ h2 => by rw [fin_ne _ (by omega)]
  have hK' : K % 2 ^ F.i = K := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hK (Nat.pow_le_pow_right (by decide) he))
  have hs := hg.sum
  rw [hK'] at hs
  have hc : dec (fin F F.i) = F.c := by
    unfold fin
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hg.c with h0 | h1
    · simp only [h0, ne_eq, not_true_eq_false, false_and, ↓reduceIte, hg.above F.i (Nat.le_refl _)]; rfl
    · simp only [h1, ne_eq, Nat.one_ne_zero, not_false_eq_true, and_self, ↓reduceIte]; rfl
  rw [Nat.zero_add] at e3
  rw [e1, e2, e3, e4, hc]
  grind

end VG.Proof.Ed25519.Recode
