import VerifiedGarbage.Impl.Weierstrass.Slots
import VerifiedGarbage.Proof.Weierstrass.Rcb
import Mathlib.Logic.Function.Basic

/-!
# Field programs on slots, as functions on environments

A slot holding `x` stands for `x R⁻¹ mod m` (`toM`, Montgomery's form,
`R = 2^(64 n)`), an element of `Fin m`, and the results of each target's
Montgomery multiplication, addition and subtraction stand for the product,
sum and difference of what their operands stand for (`toM_mul`, `toM_add`,
`toM_sub`). A field operation is then a function on environments, the
values of all slots (`FOp.run`), and the complete addition `rcb` computes
`rcbAdd` of its inputs' values (`rcb_run`): for any slots, as long as the
slots it writes (`rcbW`) are distinct and none is one it only reads
(`rcbR`). A program reads a slot only once it holds a value (`readsOk`).

Everything here is over `Fin m` and Lean's core rings
(`Lean.Grind.CommRing`), without Mathlib's algebra: the proofs of the code
need none of it, and only the proofs of the group law
(`Proof/Weierstrass/Complete.lean`) import it.
-/

namespace VG.Impl.Weierstrass

/-- The slot an operation writes. -/
def FOp.out : FOp → Nat
  | .mul o _ _ | .add o _ _ | .sub o _ _ => o

/-- The slots an operation reads. -/
def FOp.ins : FOp → List Nat
  | .mul _ a b | .add _ a b | .sub _ a b => [a, b]

/-- The operation on the slots `σ o`, `σ a`, `σ b`. -/
def FOp.rename (σ : Nat → Nat) : FOp → FOp
  | .mul o a b => .mul (σ o) (σ a) (σ b)
  | .add o a b => .add (σ o) (σ a) (σ b)
  | .sub o a b => .sub (σ o) (σ a) (σ b)

/-- The operation on an environment: the output slot gets the product, sum
or difference of the inputs' values. -/
def FOp.run {F : Type _} [Lean.Grind.CommRing F] : FOp → (Nat → F) → Nat → F
  | .mul o a b, e => Function.update e o (e a * e b)
  | .add o a b, e => Function.update e o (e a + e b)
  | .sub o a b, e => Function.update e o (e a - e b)

end VG.Impl.Weierstrass

namespace VG.Proof.Weierstrass

open VG.Impl.Weierstrass

/-! ## Arithmetic modulo `m` -/

section
variable {m : Nat} [NeZero m]

theorem ofNat_eq_ofNat {a b : Nat} : Fin.ofNat m a = Fin.ofNat m b ↔ a % m = b % m := by
  rw [Fin.ext_iff, Fin.val_ofNat, Fin.val_ofNat]

theorem ofNat_mul' (a b : Nat) : Fin.ofNat m (a * b) = Fin.ofNat m a * Fin.ofNat m b := by
  apply Fin.ext
  rw [Fin.val_ofNat, Fin.val_mul, Fin.val_ofNat, Fin.val_ofNat, Nat.mul_mod]

theorem ofNat_add' (a b : Nat) : Fin.ofNat m (a + b) = Fin.ofNat m a + Fin.ofNat m b := by
  apply Fin.ext
  rw [Fin.val_ofNat, Fin.val_add, Fin.val_ofNat, Fin.val_ofNat, Nat.add_mod]

theorem ofNat_mod (a : Nat) : Fin.ofNat m (a % m) = Fin.ofNat m a := by
  rw [ofNat_eq_ofNat, Nat.mod_mod]

theorem ofNat_pow' (a k : Nat) : Fin.ofNat m (a ^ k) = Fin.ofNat m a ^ k := by
  induction k with
  | zero => rw [Nat.pow_zero, Lean.Grind.Semiring.pow_zero]; rfl
  | succ k ih => rw [Nat.pow_succ, ofNat_mul', ih, Lean.Grind.Semiring.pow_succ]

/-- `R` is invertible modulo `m`. -/
def UnitMod (m R : Nat) [NeZero m] : Prop := ∃ i : Fin m, Fin.ofNat m R * i = 1

/-- The inverse of `R` modulo `m`, if there is one (else `0`). -/
def rinv (m R : Nat) [NeZero m] : Fin m :=
  ((List.finRange m).find? fun i => Fin.ofNat m R * i == 1).getD 0

theorem mul_rinv {R : Nat} (h : UnitMod m R) : Fin.ofNat m R * rinv m R = 1 := by
  obtain ⟨i, hi⟩ := h
  unfold rinv
  cases e : (List.finRange m).find? fun i => Fin.ofNat m R * i == 1 with
  | none =>
    rw [List.find?_eq_none] at e
    exact absurd (beq_iff_eq.mpr hi) (e i (List.mem_finRange i))
  | some j =>
    have hj := List.find?_some (p := fun i => Fin.ofNat m R * i == 1) e
    exact beq_iff_eq.mp hj

/-- `2^k` is invertible modulo an odd `m`: `2 (m + 1) / 2 = 1` modulo `m`. -/
theorem unitMod_pow_two (hm : m % 2 = 1) (k : Nat) : UnitMod m (2 ^ k) := by
  refine ⟨Fin.ofNat m ((m + 1) / 2) ^ k, ?_⟩
  have h2 : Fin.ofNat m 2 * Fin.ofNat m ((m + 1) / 2) = 1 := by
    rw [← ofNat_mul', show 2 * ((m + 1) / 2) = m + 1 by omega]
    apply Fin.ext
    rw [Fin.val_ofNat, Nat.add_mod_left]
    rfl
  rw [ofNat_pow', ← Lean.Grind.CommSemiring.mul_pow, h2, Lean.Grind.Semiring.one_pow]

end

/-! ## Montgomery's form -/

/-- What a slot holding `x` stands for: `x R⁻¹ mod m`. -/
def toM (m R x : Nat) [NeZero m] : Fin m := Fin.ofNat m x * rinv m R

section
variable {m : Nat} [NeZero m]

theorem toM_mul {R r A B : Nat} (hR : UnitMod m R) (h : r * R % m = A * B % m) :
    toM m R r = toM m R A * toM m R B := by
  have h' : Fin.ofNat m r * Fin.ofNat m R = Fin.ofNat m A * Fin.ofNat m B := by
    rw [← ofNat_mul', ← ofNat_mul', ofNat_eq_ofNat, h]
  have hu := mul_rinv hR
  unfold toM
  grind

theorem toM_add (R A B : Nat) : toM m R ((A + B) % m) = toM m R A + toM m R B := by
  unfold toM
  rw [ofNat_mod, ofNat_add', Lean.Grind.Semiring.right_distrib]

theorem toM_sub {R A B : Nat} (h : B ≤ A + m) :
    toM m R ((A + m - B) % m) = toM m R A - toM m R B := by
  have e : Fin.ofNat m (A + m - B) + Fin.ofNat m B = Fin.ofNat m A := by
    rw [← ofNat_add', Nat.sub_add_cancel h, ofNat_eq_ofNat, Nat.add_mod_right]
  unfold toM
  rw [ofNat_mod]
  grind

end

/-! ## Programs on environments -/

/-- Running a program on an environment. -/
def runOps {F : Type _} [Lean.Grind.CommRing F] (ops : List FOp) (e : Nat → F) : Nat → F :=
  ops.foldl (fun e op => op.run e) e

theorem runOps_nil {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) : runOps [] e = e := rfl

theorem runOps_cons {F : Type _} [Lean.Grind.CommRing F] (op : FOp) (ops : List FOp) (e : Nat → F) :
    runOps (op :: ops) e = runOps ops (op.run e) := rfl

/-- Renaming the slots of an operation whose output no other slot is renamed
to. -/
theorem FOp.run_rename {F : Type _} [Lean.Grind.CommRing F] (σ : Nat → Nat) (op : FOp) (e : Nat → F)
    (h : ∀ y, σ y = σ op.out → y = op.out) :
    (fun y => (op.rename σ).run e (σ y)) = op.run (fun y => e (σ y)) := by
  funext y
  have hy : σ y = σ op.out ↔ y = op.out := ⟨h y, fun h => h ▸ rfl⟩
  cases op <;> simp only [FOp.rename, FOp.run, FOp.out, Function.update_apply] at hy ⊢ <;>
    simp only [hy]

theorem runOps_rename {F : Type _} [Lean.Grind.CommRing F] (σ : Nat → Nat) :
    ∀ (ops : List FOp) (e : Nat → F), (∀ op ∈ ops, ∀ y, σ y = σ op.out → y = op.out) →
      (fun y => runOps (ops.map (FOp.rename σ)) e (σ y)) = runOps ops (fun y => e (σ y))
  | [], _, _ => rfl
  | op :: ops, e, h => by
    rw [List.map_cons, runOps_cons, runOps_cons, ← FOp.run_rename σ op e (h op (by simp)),
      runOps_rename σ ops _ (fun op' hop => h op' (by simp [hop]))]

/-! ## The complete addition -/

/-- The slots `rcb` writes. -/
def rcbW (S : RcbSlots) (o : Pt) : List Nat := [S.t0, S.t1, S.t2, S.t3, S.t4, S.t5, o.x, o.y, o.z]

/-- The slots `rcb` only reads. -/
def rcbR (S : RcbSlots) (p q : Pt) : List Nat := [S.a, S.b3, p.x, p.y, p.z, q.x, q.y, q.z]

/-- `rcb` on the slots `0, 1, …`: the ones it writes first. -/
def rcbN : List FOp := rcb ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨14, 15, 16⟩ ⟨6, 7, 8⟩

/-- Slot `i` of `rcbN` as a slot of `rcb S p q o`. -/
def rcbσ (S : RcbSlots) (p q o : Pt) (i : Nat) : Nat := (rcbW S o ++ rcbR S p q).getD i S.a

theorem rcb_eq_rename (S : RcbSlots) (p q o : Pt) :
    rcb S p q o = rcbN.map (FOp.rename (rcbσ S p q o)) :=
  rfl

theorem rcbN_out : ∀ op ∈ rcbN, op.out < 9 := by decide

/-- `rcbN` on any environment. -/
theorem rcbN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps rcbN e 6, runOps rcbN e 7, runOps rcbN e 8) =
      VG.Proof.Weierstrass.rcbAdd (e 9) (e 10) (e 11) (e 12) (e 13) (e 14) (e 15) (e 16) := rfl

theorem getD_append_left {W R : List Nat} {d w : Nat} (hw : w < W.length) :
    (W ++ R).getD w d = W[w] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hw, List.getElem?_eq_getElem hw,
    Option.getD_some]

theorem getD_mem_or (l : List Nat) (k d : Nat) : l.getD k d ∈ l ∨ l.getD k d = d := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => exact Or.inr rfl
  | some v => exact Or.inl (List.mem_of_getElem? h)

theorem getD_append_mem {W R : List Nat} {d : Nat} (hd : d ∈ R) (y : Nat) :
    (W ++ R).getD y d ∈ W ++ R := by
  rcases getD_mem_or (W ++ R) y d with h | h
  · exact h
  · rw [h]; exact List.mem_append_right _ hd

/-- Only position `w` of `W ++ R` (or the default) holds `W[w]`, if `W` has no
duplicates and nothing in `R` (or the default) is in `W`. -/
theorem getD_append_inj {W R : List Nat} {d : Nat} (hW : W.Nodup) (hR : ∀ x ∈ R, x ∉ W)
    (hd : d ∉ W) {w : Nat} (hw : w < W.length) (y : Nat)
    (h : (W ++ R).getD y d = (W ++ R).getD w d) : y = w := by
  rw [getD_append_left hw] at h
  by_cases hy : y < W.length
  · rw [getD_append_left hy] at h
    exact hW.getElem_inj.mp h
  · exfalso
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
      ← List.getD_eq_getElem?_getD] at h
    rcases getD_mem_or R (y - W.length) d with h' | h'
    · exact hR _ h' (h ▸ List.getElem_mem hw)
    · exact hd (h' ▸ h ▸ List.getElem_mem hw)

/-- The slots `rcb` writes: no two are the same, and none is one it reads only. -/
structure RcbApart (S : RcbSlots) (p q o : Pt) : Prop where
  nodup : (rcbW S o).Nodup
  apart : ∀ x ∈ rcbR S p q, x ∉ rcbW S o

theorem RcbApart.inj {S : RcbSlots} {p q o : Pt} (h : RcbApart S p q o) {w : Nat} (hw : w < 9)
    (y : Nat) (hy : rcbσ S p q o y = rcbσ S p q o w) : y = w :=
  getD_append_inj h.nodup h.apart (h.apart _ (List.mem_cons_self ..)) hw y hy

theorem rcbσ_mem (S : RcbSlots) (p q o : Pt) (i : Nat) : rcbσ S p q o i ∈ rcbW S o ++ rcbR S p q :=
  getD_append_mem (List.mem_cons_self ..) i

theorem rcbσ_out (S : RcbSlots) (p q o : Pt) {i : Nat} (hi : i < 9) : rcbσ S p q o i ∈ rcbW S o := by
  rw [rcbσ, getD_append_left hi]
  exact List.getElem_mem _

theorem rcb_out {S : RcbSlots} {p q o : Pt} : ∀ op ∈ rcb S p q o, op.out ∈ rcbW S o := by
  intro op hop
  rw [rcb_eq_rename, List.mem_map] at hop
  obtain ⟨op', h', rfl⟩ := hop
  have := rcbσ_out S p q o (rcbN_out op' h')
  cases op' <;> exact this

theorem rcb_slots {S : RcbSlots} {p q o : Pt} :
    ∀ op ∈ rcb S p q o, ∀ x ∈ op.out :: op.ins, x ∈ rcbW S o ++ rcbR S p q := by
  intro op hop
  rw [rcb_eq_rename, List.mem_map] at hop
  obtain ⟨op', _, rfl⟩ := hop
  cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil,
    or_false] <;> rintro x (rfl | rfl | rfl) <;> exact rcbσ_mem ..

theorem FOp.out_rename (σ : Nat → Nat) (op : FOp) : (op.rename σ).out = σ op.out := by
  cases op <;> rfl

theorem rcbN_outs : ∀ i < 9, i ∈ rcbN.map FOp.out := by decide

/-- `rcb` writes every slot of `rcbW`. -/
theorem rcb_out_mem {S : RcbSlots} {p q o : Pt} {x : Nat} (hx : x ∈ rcbW S o) :
    x ∈ (rcb S p q o).map FOp.out := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  have hi' : i < 9 := hi
  obtain ⟨op, hop, h⟩ := List.mem_map.mp (rcbN_outs i hi')
  rw [rcb_eq_rename, List.map_map, ← getD_append_left (R := rcbR S p q) (d := S.a) hi]
  exact List.mem_map.mpr ⟨op, hop, by rw [Function.comp_apply, FOp.out_rename, h]; rfl⟩

/-- `rcb S p q o` computes `rcbAdd` of what its inputs hold. -/
theorem rcb_run {F : Type _} [Lean.Grind.CommRing F] {S : RcbSlots} {p q o : Pt} (h : RcbApart S p q o)
    (e : Nat → F) :
    (runOps (rcb S p q o) e o.x, runOps (rcb S p q o) e o.y, runOps (rcb S p q o) e o.z) =
      VG.Proof.Weierstrass.rcbAdd (e S.a) (e S.b3) (e p.x) (e p.y) (e p.z) (e q.x) (e q.y)
        (e q.z) := by
  have key := runOps_rename (rcbσ S p q o) rcbN e fun op hop => h.inj (rcbN_out op hop)
  have := rcbN_run (fun y => e (rcbσ S p q o y))
  rw [← key] at this
  exact this

/-- What `rcb` does not write, it keeps. -/
theorem runOps_of_not_out {F : Type _} [Lean.Grind.CommRing F] {x : Nat} :
    ∀ (ops : List FOp) (e : Nat → F), (∀ op ∈ ops, op.out ≠ x) → runOps ops e x = e x
  | [], _, _ => rfl
  | op :: ops, e, h => by
    rw [runOps_cons, runOps_of_not_out ops _ fun op' hop => h op' (by simp [hop])]
    have hx : x ≠ op.out := fun hx => h op (List.mem_cons_self ..) hx.symm
    cases op <;> exact Function.update_of_ne hx _ _

/-- `ops` read only slots of `V` or written by an earlier operation. -/
def readsOk : List FOp → List Nat → Bool
  | [], _ => true
  | op :: ops, V => op.ins.all (fun x => decide (x ∈ V)) && readsOk ops (op.out :: V)

/-- The slots holding a value after `ops`: `V` and those `ops` write. -/
def validAfter : List FOp → List Nat → List Nat
  | [], V => V
  | op :: ops, V => validAfter ops (op.out :: V)

theorem mem_validAfter {x : Nat} :
    ∀ (ops : List FOp) (V : List Nat), x ∈ validAfter ops V ↔ x ∈ V ∨ x ∈ ops.map FOp.out
  | [], V => by simp [validAfter]
  | op :: ops, V => by
    rw [validAfter, mem_validAfter ops, List.map_cons, List.mem_cons, List.mem_cons]
    grind

theorem readsOk_mono : ∀ {ops : List FOp} {V V' : List Nat}, readsOk ops V = true →
    (∀ x ∈ V, x ∈ V') → readsOk ops V' = true
  | [], _, _, _, _ => rfl
  | op :: ops, V, V', h, hV => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
    refine ⟨fun x hx => hV x (h.1 x hx), readsOk_mono h.2 fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hV x hx)

theorem readsOk_rename (σ : Nat → Nat) : ∀ {ops : List FOp} {V : List Nat}, readsOk ops V = true →
    readsOk (ops.map (FOp.rename σ)) (V.map σ) = true
  | [], _, _ => rfl
  | op :: ops, V, h => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    have h₂ := readsOk_rename σ h.2
    have hout : (op.rename σ).out = σ op.out := by cases op <;> rfl
    have hins : ∀ x ∈ (op.rename σ).ins, ∃ y ∈ op.ins, σ y = x := by
      cases op <;> simp [FOp.rename, FOp.ins]
    simp only [List.map_cons, readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨fun x hx => ?_, by rw [hout]; exact h₂⟩
    obtain ⟨y, hy, rfl⟩ := hins x hx
    exact List.mem_map_of_mem (h.1 y hy)

theorem rcbN_reads : readsOk rcbN [9, 10, 11, 12, 13, 14, 15, 16] = true := by decide

/-! ## Formulas on numbered slots

A formula written on the slots `0 … 16` as `rcbN` numbers them (`0 … 5` the
temporaries, `6 … 8` the result, `9`, `10` the constants, `11 … 13` and
`14 … 16` the points), renamed to the slots of a sum (`ofN`): what `rcb`'s
lemmas show, for any such formula that writes only the first nine and reads
the others or what it wrote (`NumOk`). The formulas for `a = -3` are such
(`rcb3N`, `dbl3N`). -/

/-- A formula on numbered slots, on the slots of `p`, `q` and `o`. -/
def ofN (N : List FOp) (S : RcbSlots) (p q o : Pt) : List FOp := N.map (FOp.rename (rcbσ S p q o))

/-- A formula on numbered slots writes only the first nine, among them the
result's `6 … 8`, and reads the others or what it wrote. -/
structure NumOk (N : List FOp) : Prop where
  out : ∀ op ∈ N, op.out < 9
  outs : ∀ i ∈ [6, 7, 8], i ∈ N.map FOp.out
  reads : readsOk N [9, 10, 11, 12, 13, 14, 15, 16] = true

theorem ofN_out {N : List FOp} (hN : NumOk N) {S : RcbSlots} {p q o : Pt} :
    ∀ op ∈ ofN N S p q o, op.out ∈ rcbW S o := by
  intro op hop
  rw [ofN, List.mem_map] at hop
  obtain ⟨op', h', rfl⟩ := hop
  rw [FOp.out_rename]
  exact rcbσ_out S p q o (hN.out op' h')

theorem ofN_slots {N : List FOp} {S : RcbSlots} {p q o : Pt} :
    ∀ op ∈ ofN N S p q o, ∀ x ∈ op.out :: op.ins, x ∈ rcbW S o ++ rcbR S p q := by
  intro op hop
  rw [ofN, List.mem_map] at hop
  obtain ⟨op', _, rfl⟩ := hop
  cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil,
    or_false] <;> rintro x (rfl | rfl | rfl) <;> exact rcbσ_mem ..

theorem ofN_out_mem {N : List FOp} (hN : NumOk N) {S : RcbSlots} {p q o : Pt} {x : Nat}
    (hx : x ∈ [o.x, o.y, o.z]) : x ∈ (ofN N S p q o).map FOp.out := by
  have key : ∀ i ∈ [6, 7, 8], rcbσ S p q o i ∈ (ofN N S p q o).map FOp.out := fun i hi => by
    obtain ⟨op, hop, h⟩ := List.mem_map.mp (hN.outs i hi)
    rw [ofN, List.map_map]
    exact List.mem_map.mpr ⟨op, hop, by rw [Function.comp_apply, FOp.out_rename, h]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact key 6 (by simp)
  · exact key 7 (by simp)
  · exact key 8 (by simp)

theorem ofN_readsOk {N : List FOp} (hN : NumOk N) (S : RcbSlots) (p q o : Pt) :
    readsOk (ofN N S p q o) (rcbR S p q) = true :=
  readsOk_rename _ hN.reads

/-- A formula on numbered slots computes on the renamed slots what it computes
on the numbered ones. -/
theorem ofN_run {F : Type _} [Lean.Grind.CommRing F] {N : List FOp} (hN : NumOk N) {S : RcbSlots}
    {p q o : Pt} (h : RcbApart S p q o) (e : Nat → F) (i : Nat) :
    runOps (ofN N S p q o) e (rcbσ S p q o i) = runOps N (fun y => e (rcbσ S p q o y)) i := by
  have key := runOps_rename (rcbσ S p q o) N e fun op hop => h.inj (hN.out op hop)
  exact congrFun key i

/-- Algorithm 4 on numbered slots. -/
def rcb3N : List FOp := rcb3 ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨14, 15, 16⟩ ⟨6, 7, 8⟩

/-- Algorithm 6 on numbered slots. -/
def dbl3N : List FOp := dbl3 ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

theorem rcb3N_ok : NumOk rcb3N := ⟨by decide, by decide, by decide⟩
theorem dbl3N_ok : NumOk dbl3N := ⟨by decide, by decide, by decide⟩

theorem rcb3_eq (S : RcbSlots) (p q o : Pt) : rcb3 S p q o = ofN rcb3N S p q o := rfl
theorem dbl3_eq (S : RcbSlots) (p o : Pt) : dbl3 S p o = ofN dbl3N S p p o := rfl

theorem rcb3N_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps rcb3N e 6, runOps rcb3N e 7, runOps rcb3N e 8) =
      VG.Proof.Weierstrass.rcbAdd3 (e 10) (e 11) (e 12) (e 13) (e 14) (e 15) (e 16) := rfl

theorem dbl3N_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dbl3N e 6, runOps dbl3N e 7, runOps dbl3N e 8) =
      VG.Proof.Weierstrass.rcbDbl3 (e 10) (e 11) (e 12) (e 13) := rfl

/-- A multiplication by `1` leaves Montgomery's form. -/
theorem toM_one_mul {m R r A : Nat} [NeZero m] (hR : UnitMod m R) (h : r * R % m = A * 1 % m) :
    Fin.ofNat m r = toM m R A := by
  have h' : Fin.ofNat m r * Fin.ofNat m R = Fin.ofNat m A := by
    rw [← ofNat_mul', ofNat_eq_ofNat, h, Nat.mul_one]
  have hu := mul_rinv hR
  unfold toM
  grind

/-- A multiplication by `R² mod m` enters Montgomery's form. -/
theorem toM_r2 {m R r A : Nat} [NeZero m] (hR : UnitMod m R) (h : r * R % m = A * (R * R % m) % m) :
    toM m R r = Fin.ofNat m A := by
  have h' : Fin.ofNat m r * Fin.ofNat m R = Fin.ofNat m A * (Fin.ofNat m R * Fin.ofNat m R) := by
    rw [← ofNat_mul', ← ofNat_mul', ← ofNat_mul', ofNat_eq_ofNat, h, Nat.mul_mod, Nat.mod_mod,
      ← Nat.mul_mod]
  have hu := mul_rinv hR
  unfold toM
  grind

/-- What `x R mod m` stands for. -/
theorem toM_mont {m R x : Nat} [NeZero m] (hR : UnitMod m R) : toM m R (x * R % m) = Fin.ofNat m x := by
  unfold toM
  rw [ofNat_mod, ofNat_mul', Lean.Grind.Semiring.mul_assoc, mul_rinv hR, Lean.Grind.Semiring.mul_one]

/-- A number below `m` stands for zero only if it is zero. -/
theorem toM_eq_zero_iff {m R x : Nat} [NeZero m] (hR : UnitMod m R) (hx : x < m) :
    toM m R x = 0 ↔ x = 0 := by
  unfold toM
  constructor
  · intro h
    have hu := mul_rinv hR
    have h' : Fin.ofNat m x = 0 := by grind
    have := congrArg Fin.val h'
    rwa [Fin.val_ofNat, Nat.mod_eq_of_lt hx] at this
  · rintro rfl
    exact Lean.Grind.Semiring.zero_mul _

theorem toM_one {m R : Nat} [NeZero m] (hR : UnitMod m R) : toM m R (R % m) = 1 := by
  unfold toM
  rw [ofNat_mod]
  exact mul_rinv hR

theorem toM_zero (m R : Nat) [NeZero m] : toM m R 0 = 0 :=
  Lean.Grind.Semiring.zero_mul _

end VG.Proof.Weierstrass
