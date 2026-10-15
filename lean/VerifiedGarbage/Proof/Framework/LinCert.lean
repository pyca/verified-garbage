module

public import Init.Data.List.Basic
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Meta.Tactic.Util
public meta import Lean.Meta.Tactic.Cases
public meta import Lean.Meta.Tactic.Assert
public meta import Lean.Meta.Tactic.Assumption

/-!
# Linear facts about `Nat`, by a certificate the kernel checks at once

Untrusted: this only changes how proofs are found; the kernel checks them.

`omega`'s proofs are large terms the kernel spends most of each call checking
(8–15 ms in the middle of a proof about machine states). `lin_cert` closes the
same goals when they follow linearly from facts about `Nat`: from the negated
goal and facts `Lᵢ ≤ Rᵢ` (`<`, `=`, `≥`, `>`, `¬ ≤`, `¬ <` of linear
expressions over atoms) it finds multipliers `kᵢ` (Fourier–Motzkin, at
elaboration time) such that `∑ kᵢ Lᵢ` has at least every coefficient of
`∑ kᵢ Rᵢ` and a larger constant, which no values of the atoms allow. The proof
is one application of `false_of_check`: the facts' proofs, whose types are
those of the reified facts (`Lin.denote`) by definition, and `check`, which
the kernel evaluates (on `Nat` literals; the functions are written with
recursors, which the kernel evaluates faster than `brecOn`). It costs the
kernel 2–3 ms.

An atom is any other term; facts that hold of an atom by its definition are
added: `k * (x / k) + x % k = x` and `x % k < k` for a literal `k`,
`x - y ≤ x` and `x ≤ x - y + y`, and the bounds of `BitVec.toNat` and
`Fin.val`. `closeSplit` splits on an arithmetic disjunction in context, or on
whether a subtraction truncates, up to three times. Only the facts connected
to the negated goal through atoms are used, and larger systems are left to
`omega`, which `lin_cert` falls back to.
-/

@[expose] public section

namespace VG.LinCert

/-- A linear Nat expression over the atoms `v`. -/
inductive Lin where
  | atom (i : Nat)
  | lit (n : Nat)
  | add (a b : Lin)
  | mul (k : Nat) (a : Lin)

/-- The `i`th element of `v` (`0` past its end), by `List.rec`. -/
noncomputable def nth (v : List Nat) : Nat → Nat :=
  List.rec (fun _ => 0) (fun x _ ih i => Nat.rec x (fun j _ => ih j) i) v

noncomputable def Lin.denote (v : List Nat) (e : Lin) : Nat :=
  Lin.rec (fun i => nth v i) (fun n => n) (fun _ _ a b => a + b) (fun k _ a => k * a) e

/-- The coefficient of atom `j`. -/
noncomputable def Lin.coef (j : Nat) (e : Lin) : Nat :=
  Lin.rec (fun i => bif Nat.beq i j then 1 else 0) (fun _ => 0) (fun _ _ a b => a + b) (fun k _ a => k * a) e

noncomputable def Lin.const (e : Lin) : Nat :=
  Lin.rec (fun _ => 0) (fun n => n) (fun _ _ a b => a + b) (fun k _ a => k * a) e

/-- Every atom is below `n`. -/
noncomputable def Lin.bnd (n : Nat) (e : Lin) : Bool :=
  Lin.rec (fun i => Nat.blt i n) (fun _ => true) (fun _ _ a b => a && b) (fun _ _ a => a) e

theorem nth_eq (v : List Nat) (i : Nat) : nth v i = v.getD i 0 := by
  induction v generalizing i with
  | nil => rfl
  | cons x v ih => cases i with
    | zero => rfl
    | succ i => exact ih i

/-- `∑_{j<n} c j * v j`. -/
def wsum (v : List Nat) (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => wsum v c n + c n * v.getD n 0

theorem wsum_add (v : List Nat) (c d : Nat → Nat) (n : Nat) :
    wsum v (fun j => c j + d j) n = wsum v c n + wsum v d n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wsum, ih, Nat.add_mul]; omega

theorem wsum_mul (v : List Nat) (k : Nat) (c : Nat → Nat) (n : Nat) :
    wsum v (fun j => k * c j) n = k * wsum v c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wsum, ih, Nat.mul_add, Nat.mul_assoc]

theorem wsum_atom (v : List Nat) (i : Nat) : ∀ n, i < n →
    wsum v (fun j => if i = j then 1 else 0) n = v.getD i 0
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    have z : ∀ m, m ≤ i → wsum v (fun j => if i = j then 1 else 0) m = 0 := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        have e : (if i = m then 1 else 0) = 0 := by simp only [ite_eq_right_iff]; omega
        simp only [wsum, ih (by omega), e, Nat.zero_mul, Nat.add_zero]
    by_cases e : i = n
    · subst e; simp only [wsum, z i (Nat.le_refl _), ↓reduceIte, Nat.one_mul, Nat.zero_add]
    · have e' : (if i = n then 1 else 0) = 0 := by simp only [ite_eq_right_iff]; omega
      simp only [wsum, e', Nat.zero_mul, Nat.add_zero]; exact wsum_atom v i n (by omega)

theorem wsum_zero (v : List Nat) (n : Nat) : wsum v (fun _ => 0) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wsum, ih]

theorem coef_atom (i j : Nat) : (Lin.atom i).coef j = if i = j then 1 else 0 := by
  simp only [Lin.coef, cond_eq_ite]
  by_cases h : i = j <;> simp [h]

theorem Lin.denote_eq (v : List Nat) (n : Nat) : ∀ e : Lin, e.bnd n = true →
    e.denote v = e.const + wsum v (fun j => e.coef j) n
  | .atom i, h => by
    simp only [Lin.bnd, Nat.blt_eq] at h
    have : (fun j => (Lin.atom i).coef j) = fun j => if i = j then 1 else 0 := funext (coef_atom i)
    rw [this, wsum_atom v i n h]
    simp only [Lin.denote, Lin.const, nth_eq, Nat.zero_add]
  | .lit m, _ => by
    simp only [Lin.denote, Lin.const, Lin.coef, wsum_zero, Nat.add_zero]
  | .add a b, h => by
    simp only [Lin.bnd, Bool.and_eq_true] at h
    have ea := Lin.denote_eq v n a h.1
    have eb := Lin.denote_eq v n b h.2
    simp only [Lin.denote, Lin.const, Lin.coef] at ea eb ⊢
    rw [wsum_add, ea, eb]; omega
  | .mul k a, h => by
    simp only [Lin.bnd] at h
    have ea := Lin.denote_eq v n a h
    simp only [Lin.denote, Lin.const, Lin.coef] at ea ⊢
    rw [wsum_mul, ea, Nat.mul_add]

theorem wsum_le (v : List Nat) (c d : Nat → Nat) : ∀ n, (∀ j < n, d j ≤ c j) → wsum v d n ≤ wsum v c n
  | 0, _ => Nat.le_refl _
  | n + 1, h => Nat.add_le_add (wsum_le v c d n fun j hj => h j (by omega))
      (Nat.mul_le_mul_right _ (h n (by omega)))

/-- All coefficients of `a` are at least those of `b`, below `n`. -/
noncomputable def dom (a b : Lin) (n : Nat) : Bool :=
  Nat.rec true (fun j ih => Nat.ble (b.coef j) (a.coef j) && ih) n

theorem dom_le {a b : Lin} : ∀ {n}, dom a b n = true → ∀ j < n, b.coef j ≤ a.coef j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, h, j, hj => by
    simp only [dom, Bool.and_eq_true, Nat.ble_eq] at h
    by_cases e : j = n
    · subst e; exact h.1
    · exact dom_le h.2 j (by omega)

/-- Facts `L ≤ R`, each with its multiplier. -/
abbrev Facts := List (Lin × Lin × Nat)

noncomputable def Holds (v : List Nat) (fs : Facts) : Prop :=
  List.rec True (fun f _ ih => f.1.denote v ≤ f.2.1.denote v ∧ ih) fs

noncomputable def sumL (fs : Facts) : Lin := List.rec (.lit 0) (fun f _ ih => .add (.mul f.2.2 f.1) ih) fs

noncomputable def sumR (fs : Facts) : Lin := List.rec (.lit 0) (fun f _ ih => .add (.mul f.2.2 f.2.1) ih) fs

theorem holds_sum (v : List Nat) : ∀ fs : Facts, Holds v fs → (sumL fs).denote v ≤ (sumR fs).denote v
  | [], _ => Nat.le_refl _
  | _ :: fs, ⟨h, hs⟩ => by
    have := holds_sum v fs hs
    simp only [sumL, sumR, Lin.denote] at this ⊢
    exact Nat.add_le_add (Nat.mul_le_mul_left _ h) this

/-- The certificate: the combined left side has every coefficient of the right
side's, and a larger constant, so the facts cannot all hold. -/
noncomputable def check (n : Nat) (fs : Facts) : Bool :=
  (sumL fs).bnd n && (sumR fs).bnd n && dom (sumL fs) (sumR fs) n &&
    Nat.blt (sumR fs).const (sumL fs).const

theorem false_of_check (v : List Nat) (n : Nat) (fs : Facts) (h : Holds v fs)
    (hc : check n fs = true) : False := by
  simp only [check, Bool.and_eq_true, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hl, hr⟩, hd⟩, hk⟩ := hc
  have h₁ := holds_sum v fs h
  rw [Lin.denote_eq v n _ hl, Lin.denote_eq v n _ hr] at h₁
  have h₂ := wsum_le v (fun j => (sumL fs).coef j) (fun j => (sumR fs).coef j) n (dom_le hd)
  omega

theorem le_sub_add (n m : Nat) : n ≤ n - m + m := by omega

end VG.LinCert

end

public meta section

namespace VG.LinCert.Meta
open Lean Meta Elab Tactic

/-- A reified linear expression: its `Lin` term, constant and coefficients. -/
structure R where
  e : Expr
  c : Nat
  co : Std.HashMap Nat Nat
  deriving Inhabited

structure St where
  atoms : Array Expr := #[]
  /-- Facts about the atoms (proof, type), from their definitions. -/
  extra : Array (Expr × Expr) := #[]

abbrev M := StateT St MetaM

/-- A Nat literal, as Lean writes it (numerals, raw literals, powers of literals). -/
partial def natLit? (t : Expr) : Option Nat :=
  if let some n := t.rawNatLit? then some n
  else if t.isAppOfArity ``OfNat.ofNat 3 then (t.getArg! 1).rawNatLit?
  else if t.isAppOfArity ``HPow.hPow 6 then do
    let a ← natLit? (t.getArg! 4); let b ← natLit? (t.getArg! 5)
    if b ≤ 1024 then some (a ^ b) else none
  else none

def isNatTy (e : Expr) : MetaM Bool := return e.consumeMData.isConstOf ``Nat

/-- Facts that hold of the atom `t` by its definition, without a case split. -/
def sideFacts (t : Expr) : MetaM (Array Expr) := do
  if t.isAppOfArity ``HDiv.hDiv 6 || t.isAppOfArity ``HMod.hMod 6 then
    if ← isNatTy (t.getArg! 0) then
      let x := t.getArg! 4; let k := t.getArg! 5
      if let some kv := natLit? k then
        if kv > 0 then
          let hk := mkApp (mkConst ``Nat.zero_lt_succ) (mkRawNatLit (kv - 1))
          return #[mkApp2 (mkConst ``Nat.div_add_mod) x k, mkApp3 (mkConst ``Nat.mod_lt) x k hk]
    return #[]
  if t.isAppOfArity ``HSub.hSub 6 then
    if ← isNatTy (t.getArg! 0) then
      let x := t.getArg! 4; let y := t.getArg! 5
      return #[mkApp2 (mkConst ``Nat.sub_le) x y, mkApp2 (mkConst ``VG.LinCert.le_sub_add) x y]
    return #[]
  if t.isAppOfArity ``BitVec.toNat 2 then
    return #[mkApp2 (mkConst ``BitVec.isLt) (t.getArg! 0) (t.getArg! 1)]
  if t.isAppOfArity ``Fin.val 2 then
    return #[mkApp2 (mkConst ``Fin.isLt) (t.getArg! 0) (t.getArg! 1)]
  return #[]

def atom (t : Expr) : M R := do
  let s ← get
  let i ← match s.atoms.findIdx? (· == t) with
    | some i => pure i
    | none => do
      set { s with atoms := s.atoms.push t }
      for pf in ← sideFacts t do
        let ty ← inferType pf
        modify fun s => { s with extra := s.extra.push (pf, ty) }
      pure s.atoms.size
  return ⟨mkApp (mkConst ``Lin.atom) (mkNatLit i), 0, ({} : Std.HashMap Nat Nat).insert i 1⟩

def litR (n : Nat) : R := ⟨mkApp (mkConst ``Lin.lit) (mkNatLit n), n, {}⟩

def addR (a b : R) : R :=
  ⟨mkApp2 (mkConst ``Lin.add) a.e b.e, a.c + b.c,
    b.co.fold (fun (m : Std.HashMap Nat Nat) k v => m.insert k (m.getD k 0 + v)) a.co⟩

def mulR (k : Nat) (a : R) : R :=
  ⟨mkApp2 (mkConst ``Lin.mul) (mkNatLit k) a.e, k * a.c,
    a.co.fold (fun (m : Std.HashMap Nat Nat) j v => m.insert j (k * v)) {}⟩

partial def reify (t : Expr) : M R := do
  if let some n := natLit? t then return litR n
  if t.isAppOfArity ``HAdd.hAdd 6 then
    return addR (← reify (t.getArg! 4)) (← reify (t.getArg! 5))
  if t.isAppOfArity ``HMul.hMul 6 then
    if let some k := natLit? (t.getArg! 4) then return mulR k (← reify (t.getArg! 5))
  if t.isAppOfArity ``Nat.succ 1 then return addR (← reify (t.getArg! 0)) (litR 1)
  atom t

/-- A fact `L ≤ R` with its proof. -/
structure Fact where
  pf : Expr
  l : R
  r : R
  deriving Inhabited

def isNat (e : Expr) : MetaM Bool := return e.consumeMData.isConstOf ``Nat

/-- The facts a hypothesis gives (none if it is not a linear Nat fact). -/
def factsOf (pf ty : Expr) : M (List Fact) := do
  let ty := (← instantiateMVars ty).consumeMData
  let le (pf a b : Expr) : M (List Fact) := do return [⟨pf, ← reify a, ← reify b⟩]
  let lt (pf a b : Expr) : M (List Fact) := do return [⟨pf, addR (← reify a) (litR 1), ← reify b⟩]
  match ty.getAppFn.constName?, ty.getAppNumArgs with
  | some ``LE.le, 4 => if ← isNat (ty.getArg! 0) then le pf (ty.getArg! 2) (ty.getArg! 3) else return []
  | some ``LT.lt, 4 => if ← isNat (ty.getArg! 0) then lt pf (ty.getArg! 2) (ty.getArg! 3) else return []
  | some ``GE.ge, 4 => if ← isNat (ty.getArg! 0) then le pf (ty.getArg! 3) (ty.getArg! 2) else return []
  | some ``GT.gt, 4 => if ← isNat (ty.getArg! 0) then lt pf (ty.getArg! 3) (ty.getArg! 2) else return []
  | some ``Eq, 3 =>
    if ← isNat (ty.getArg! 0) then
      let a := ty.getArg! 1; let b := ty.getArg! 2
      return (← le (mkApp3 (mkConst ``Nat.le_of_eq) a b pf) a b) ++
        (← le (mkApp3 (mkConst ``Nat.le_of_eq) b a (mkApp4 (mkConst ``Eq.symm [1]) (mkConst ``Nat) a b pf)) b a)
    else return []
  | some ``Not, 1 =>
    let p := (ty.getArg! 0).consumeMData
    match p.getAppFn.constName?, p.getAppNumArgs with
    | some ``LE.le, 4 =>
      if ← isNat (p.getArg! 0) then
        let a := p.getArg! 2; let b := p.getArg! 3
        lt (mkApp3 (mkConst ``Nat.gt_of_not_le) a b pf) b a
      else return []
    | some ``LT.lt, 4 =>
      if ← isNat (p.getArg! 0) then
        let a := p.getArg! 2; let b := p.getArg! 3
        le (mkApp3 (mkConst ``Nat.le_of_not_lt) a b pf) b a
      else return []
    | _, _ => return []
  | _, _ => return []

/-- Fourier–Motzkin with provenance: rows `∑ a_j x_j + c ≤ 0` (x ≥ 0), each with
its multipliers. A row with no negative coefficient and `c > 0` is a
contradiction. -/
structure Row where
  a : Std.HashMap Nat Int
  c : Int
  k : Array Nat

def Row.bad (r : Row) : Bool := r.c > 0 && r.a.fold (fun ok _ v => ok && v ≥ 0) true

def Row.comb (p n : Row) (j : Nat) : Row :=
  let ap := p.a.getD j 0; let an := -(n.a.getD j 0)  -- both > 0
  let a := p.a.fold (fun (m : Std.HashMap Nat Int) i v => m.insert i (m.getD i 0 + an * v))
    (n.a.fold (fun (m : Std.HashMap Nat Int) i v => m.insert i (ap * v)) {})
  ⟨a.erase j, an * p.c + ap * n.c, (p.k.zip n.k).map fun (x, y) => an.toNat * x + ap.toNat * y⟩

/-- Remove what cannot matter: a variable with no negative coefficient (a
positive one is allowed in a certificate) and the rows of a variable with no
positive coefficient (which no combination cancels). -/
partial def prune (rows : Array Row) (vars : List Nat) : Array Row × List Nat :=
  let pos : Std.HashSet Nat := rows.foldl (fun (s : Std.HashSet Nat) r =>
    r.a.fold (fun (s : Std.HashSet Nat) j (v : Int) => if v > 0 then s.insert j else s) s) {}
  let neg : Std.HashSet Nat := rows.foldl (fun (s : Std.HashSet Nat) r =>
    r.a.fold (fun (s : Std.HashSet Nat) j (v : Int) => if v < 0 then s.insert j else s) s) {}
  let onlyNeg := vars.filter fun j => neg.contains j && !pos.contains j
  let rows' := if onlyNeg.isEmpty then rows else rows.filter fun r => !onlyNeg.any fun j => r.a.getD j 0 < 0
  let vars' := vars.filter fun j => neg.contains j && pos.contains j
  let rows' := rows'.map fun r => { r with a := r.a.filter fun j _ => vars'.contains j }
  if rows'.size == rows.size && vars'.length == vars.length then (rows', vars') else prune rows' vars'

partial def fm (rows : Array Row) (vars : List Nat) (fuel : Nat) : Option (Array Nat) :=
  match rows.find? Row.bad with
  | some r => some r.k
  | none =>
    let (rows, vars) := prune rows vars
    match rows.find? Row.bad with
    | some r => some r.k
    | none =>
    if fuel = 0 then none else
    match vars with
    | [] => none
    | _ =>
      -- The variable with the fewest pairs.
      let cnt : Std.HashMap Nat (Nat × Nat) := rows.foldl (fun (m : Std.HashMap Nat (Nat × Nat)) r =>
        r.a.fold (fun (m : Std.HashMap Nat (Nat × Nat)) j (v : Int) =>
          let (p, n) := m.getD j (0, 0); m.insert j (if v > 0 then (p + 1, n) else (p, n + 1))) m) {}
      let cost (j : Nat) : Nat := let (p, n) := cnt.getD j (0, 0); p * n
      let j := vars.foldl (fun b j => if cost j < cost b then j else b) vars.head!
      let P := rows.filter (·.a.getD j 0 > 0)
      let N := rows.filter (·.a.getD j 0 < 0)
      let Z := rows.filter (·.a.getD j 0 == 0)
      let combos := P.flatMap fun p => N.map fun n => p.comb n j
      if Z.size + P.size + combos.size > 200 then none else
      -- `P` rows keep their (positive) `x_j`, which the check allows.
      fm (Z ++ P.map (fun r => { r with a := r.a.erase j }) ++ combos) (vars.erase j) (fuel - 1)

def mkFacts (fs : List (Fact × Nat)) : Expr :=
  let ty := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Lin) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Lin) (mkConst ``Nat))
  fs.foldr (fun (f, k) acc =>
    mkApp3 (mkConst ``List.cons [0]) ty
      (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Lin)
        (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Lin) (mkConst ``Nat)) f.l.e
        (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Lin) (mkConst ``Nat) f.r.e (mkNatLit k))) acc)
    (mkApp (mkConst ``List.nil [0]) ty)

/-- Close `g : False` from the facts `hs` (proofs; each with whether it comes
from the negated goal), or return `false`, leaving `g` unassigned. -/
def closeFalseWith (g : MVarId) (hs : Array (Expr × Bool)) : MetaM Bool := g.withContext do
  let (facts0, st) ← (do
    let mut out : Array (Fact × Bool) := #[]
    for (h, seed) in hs do
      for f in ← factsOf h (← inferType h) do out := out.push (f, seed)
    -- The atoms' facts, which may bring more atoms.
    let mut i := 0
    while i < (← get).extra.size do
      let (pf, ty) := (← get).extra[i]!
      for f in ← factsOf pf ty do out := out.push (f, false)
      i := i + 1
    return out : M (Array (Fact × Bool))).run {}
  if facts0.isEmpty then return false
  -- Keep the facts connected to the negated goal by shared atoms (all, if none is).
  let atomsOf (f : Fact) : List Nat := f.l.co.toList.map (·.1) ++ f.r.co.toList.map (·.1)
  let facts : Array Fact ← do
    if !(facts0.any (·.2)) then pure (facts0.map (·.1)) else
    let mut keep := facts0.map (·.2)
    let mut seen : Std.HashSet Nat := {}
    for (f, b) in facts0 do
      if b then for a in atomsOf f do seen := seen.insert a
    let mut changed := true
    while changed do
      changed := false
      for i in [0:facts0.size] do
        if !keep[i]! && (atomsOf facts0[i]!.1).any seen.contains then
          keep := keep.set! i true
          changed := true
          for a in atomsOf facts0[i]!.1 do seen := seen.insert a
    pure ((facts0.zip keep).filterMap fun ((f, _), k) => if k then some f else none)
  -- Larger systems are rarely linear consequences; leave them to `omega`.
  if facts.size > 24 then return false
  let n := st.atoms.size
  let vars := (List.range n).filter fun j => facts.any fun f => (atomsOf f).contains j
  let rows := facts.mapIdx fun i f =>
    let a : Std.HashMap Nat Int := f.r.co.fold (fun (m : Std.HashMap Nat Int) j (v : Nat) =>
      m.insert j (m.getD j 0 - (v : Int))) (f.l.co.fold (fun (m : Std.HashMap Nat Int) j (v : Nat) =>
        m.insert j (v : Int)) {})
    ⟨a, (f.l.c : Int) - f.r.c, (Array.replicate facts.size 0).set! i 1⟩
  let some ks := fm rows vars (vars.length + 1) | return false
  let used := (facts.zip ks).toList.filter (·.2 > 0)
  let v ← mkListLit (mkConst ``Nat) st.atoms.toList
  -- `Holds v fs`, as nested pairs of the facts' proofs.
  let mut holds := mkConst ``True.intro
  let mut holdsTy := mkConst ``True
  for (f, _) in used.reverse do
    let ty ← inferType f.pf
    holds := mkApp4 (mkConst ``And.intro) ty holdsTy f.pf holds
    holdsTy := mkApp2 (mkConst ``And) ty holdsTy
  let hc ← mkEqRefl (mkConst ``Bool.true)
  let pf := mkApp5 (mkConst ``false_of_check) v (mkNatLit n) (mkFacts used) holds hc
  -- Mention every fact, as `omega`'s proof does, so that the unused-variables
  -- linter judges the hypotheses as it does with `omega`.
  let ms := hs.filter (·.1.isFVar)
  let mut lam := pf
  for (h, _) in ms.reverse do
    lam := .lam `_h (← inferType h) lam .default
  g.assign (mkAppN lam (ms.map (·.1)))
  return true

/-- Whether `e` is a type `omega` reads facts about. -/
def arithType (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isConstOf ``Nat || e.isConstOf ``Int || e.isAppOfArity ``BitVec 1 || e.isAppOfArity ``Fin 1

/-- Whether `t` is a fact `omega` may read: a relation or `Dvd` over `Nat`,
`Int`, `Fin` or `BitVec`, or `¬`, `∧`, `∨`, `↔`, `→` of them (syntactically; it
is cheap). -/
partial def mentionable (t : Expr) : Bool :=
  let t := t.consumeMData
  match t.getAppFn.constName?, t.getAppNumArgs with
  | some ``Eq, 3 | some ``Ne, 3 | some ``LE.le, 4 | some ``LT.lt, 4 | some ``GE.ge, 4
  | some ``GT.gt, 4 | some ``Dvd.dvd, 4 => arithType (t.getArg! 0)
  | some ``Not, 1 => mentionable (t.getArg! 0)
  | some ``And, 2 | some ``Or, 2 | some ``Iff, 2 => mentionable (t.getArg! 0) && mentionable (t.getArg! 1)
  | _, _ => t.isArrow && mentionable t.bindingDomain! && mentionable t.bindingBody!

/-- `closeFalseWith` on the context's hypotheses that `omega` may read, the
last one being the negated goal. -/
def closeFalse (g : MVarId) : MetaM Bool := g.withContext do
  let last := (← getLCtx).lastDecl.map (·.fvarId)
  let mut hs := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    if mentionable d.type then hs := hs.push (d.toExpr, some d.fvarId == last)
  closeFalseWith g hs

/-- Whether `t` is a Nat relation, or a connective of them (what a split may use). -/
partial def isArithProp (t : Expr) : Bool :=
  let t := t.consumeMData
  match t.getAppFn.constName?, t.getAppNumArgs with
  | some ``Eq, 3 => (t.getArg! 0).consumeMData.isConstOf ``Nat
  | some ``LE.le, 4 | some ``LT.lt, 4 | some ``GE.ge, 4 | some ``GT.gt, 4 =>
    (t.getArg! 0).consumeMData.isConstOf ``Nat
  | some ``Not, 1 => isArithProp (t.getArg! 0)
  | some ``Or, 2 => isArithProp (t.getArg! 0) && isArithProp (t.getArg! 1)
  | _, _ => false

/-- The Nat subtractions `x - y` in `e`. -/
partial def subsOf (e : Expr) (acc : Array (Expr × Expr)) : Array (Expr × Expr) :=
  let acc := if e.isAppOfArity ``HSub.hSub 6 && (e.getArg! 0).consumeMData.isConstOf ``Nat then
    let p := (e.getArg! 4, e.getArg! 5)
    if acc.any (fun q => q.1 == p.1 && q.2 == p.2) then acc else acc.push p
  else acc
  match e with
  | .app f a => subsOf a (subsOf f acc)
  | .mdata _ b => subsOf b acc
  | _ => acc

/-- `closeFalse`, splitting on an arithmetic disjunction in context, or on
whether a subtraction `x - y` truncates, up to `depth` times. -/
partial def closeSplit (g : MVarId) (depth : Nat) (done : Array (Expr × Expr) := #[]) : MetaM Bool := do
  if ← closeFalse g then return true
  if depth = 0 then return false
  g.withContext do
    let mut subs : Array (Expr × Expr) := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty := (← instantiateMVars d.type).consumeMData
      if ty.isAppOfArity ``Or 2 && isArithProp ty then
        let s ← saveState
        let gs ← (some <$> g.cases d.fvarId) <|> pure none
        if let some gs := gs then
          if ← gs.allM fun sg => closeSplit sg.mvarId (depth - 1) done then return true
        s.restore
        return false
      if isArithProp ty then subs := subsOf ty subs
    let some (x, y) := subs.find? (fun p => !done.any fun q => q.1 == p.1 && q.2 == p.2) | return false
    let s ← saveState
    let h := mkApp2 (mkConst ``Nat.lt_or_ge) x y
    let g₁ ← g.assert `hsub (← inferType h) h
    let (fv, g₁) ← g₁.intro1P
    let gs ← g₁.cases fv
    let done := done.push (x, y)
    let ok ← gs.allM fun sg => sg.mvarId.withContext do
      let hv := (sg.fields[0]!).fvarId!
      let hty ← inferType (.fvar hv)
      -- `x < y`: `x - y = 0`; `x ≥ y`: `x - y + y = x`.
      let fact := if hty.consumeMData.isAppOfArity ``LT.lt 4 then
          mkApp3 (mkConst ``Nat.sub_eq_zero_of_le) x y (mkApp3 (mkConst ``Nat.le_of_lt) x y (.fvar hv))
        else mkApp3 (mkConst ``Nat.sub_add_cancel) x y (.fvar hv)
      let g₂ ← sg.mvarId.assert `hsub' (← inferType fact) fact
      let (_, g₂) ← g₂.intro1P
      closeSplit g₂ (depth - 1) done
    if ok then return true
    s.restore
    return false

end VG.LinCert.Meta

open Lean Meta Elab Tactic in
/-- `lin_cert` closes the goal from the context's linear Nat facts by a reflected
certificate, falling back to `omega`. -/
elab "lin_cert" : tactic => do
  let s ← saveState
  let g ← getMainGoal
  let ok ← g.withContext do
    let some g' ← g.falseOrByContra | return true
    VG.LinCert.Meta.closeSplit g' 3
  if ok then replaceMainGoal [] else
    s.restore
    evalTactic (← `(tactic| omega))

open Lean Meta in
/-- Close `g` by a hypothesis, up to reducible unfolding, as `omega` first tries. -/
def tryAssumption (g : MVarId) : MetaM Bool := do
  try
    withReducibleAndInstances g.assumption
    return true
  catch _ => return false

open Lean Meta Elab Tactic in
/-- `omega` tries `lin_cert`'s certificate first (after `assumption`, as
`omega` does), and otherwise falls through to Lean's `omega`; `omega` with a
configuration is Lean's. -/
@[tactic Lean.Parser.Tactic.omega] def omegaLinFirst : Tactic := fun stx => do
  if stx[1].getArgs.any (fun a => !a.getArgs.isEmpty) then throwUnsupportedSyntax
  let s ← saveState
  let g ← getMainGoal
  let ok ← g.withContext do
    if ← tryAssumption g then return true
    let some g' ← g.falseOrByContra | return true
    VG.LinCert.Meta.closeSplit g' 3
  if ok then replaceMainGoal [] else
    s.restore
    throwUnsupportedSyntax
