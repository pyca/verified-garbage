import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttSpec

namespace VG.Proof.MlDsa.AArch64.Optimized.Traversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

/-- A butterfly with its root-table index retained symbolically. -/
structure Op where
  index : Nat
  length : Nat
  rootIndex : Nat
  deriving DecidableEq, Repr

def Op.apply (o : Op) (w : Poly) : Poly := bfly w o.index o.length (zetas o.rootIndex)
def run (ops : List Op) (w : Poly) : Poly := ops.foldl (fun w o => o.apply w) w

def outerSlice (u : Nat) : List Op :=
  ([4,2,1] : List Nat).flatMap fun gap =>
    (List.range (4/gap)).flatMap fun g =>
      (List.range gap).flatMap fun j =>
        (List.range 4).map fun e =>
          ⟨64*gap*g+32*j+4*u+e,32*gap,4/gap+g⟩

def innerSlice (u : Nat) : List Op :=
  (([4,2,1] : List Nat).flatMap fun gap =>
    (List.range (4/gap)).flatMap fun g =>
      (List.range gap).flatMap fun j =>
        (List.range 4).map fun e =>
          ⟨32*u+8*gap*g+4*j+e,4*gap,32/gap+(4/gap)*u+g⟩) ++
  ((List.range 4).flatMap fun group =>
    ([2,1] : List Nat).flatMap fun len =>
      (List.range (4/len)).flatMap fun g =>
        (List.range len).map fun j =>
          ⟨32*u+8*group+2*len*g+j,len,128/len+16*u/len+4*group/len+g⟩)

def outerSchedule : List Op := (List.range 8).flatMap outerSlice
def innerSchedule : List Op := (List.range 8).flatMap innerSlice

def layerSchedule (len : Nat) : List Op :=
  (List.range (128/len)).flatMap fun g =>
    (List.range len).map fun j => ⟨2*len*g+j,len,128/len+g⟩

def standardOuter : List Op := ([128,64,32] : List Nat).flatMap layerSchedule
def standardInner : List Op := ([16,8,4,2,1] : List Nat).flatMap layerSchedule

/-- The checker permits only swaps of butterflies with disjoint, valid pairs. -/
def independent (a b : Op) : Bool := decide
  (0<a.length ∧ a.index+a.length<n ∧ 0<b.length ∧ b.index+b.length<n ∧
    a.index≠b.index ∧ a.index≠b.index+b.length ∧
    a.index+a.length≠b.index ∧ a.index+a.length≠b.index+b.length)

theorem independent_comm {a b : Op} (h : independent a b=true) (w : Poly) :
    b.apply (a.apply w) = a.apply (b.apply w) := by
  have h' : 0<a.length ∧ a.index+a.length<n ∧ 0<b.length ∧ b.index+b.length<n ∧
    a.index≠b.index ∧ a.index≠b.index+b.length ∧
    a.index+a.length≠b.index ∧ a.index+a.length≠b.index+b.length := of_decide_eq_true h
  exact bfly_comm w h'.1 h'.2.2.1 h'.2.1 h'.2.2.2.1
    h'.2.2.2.2.1 h'.2.2.2.2.2.1 h'.2.2.2.2.2.2.1 h'.2.2.2.2.2.2.2 _ _

def key (o : Op) : Nat := (256-o.length)*256+o.index

/-- Checked insertion never crosses a dependent butterfly. -/
def insert (a : Op) : List Op → Option (List Op)
  | [] => some [a]
  | b::bs => if key a≤key b then some (a::b::bs)
      else if independent a b then (insert a bs).map (b::·) else none

theorem insert_run {a : Op} {xs ys : List Op} (h : insert a xs=some ys) (w : Poly) :
    run ys w = run xs (a.apply w) := by
  induction xs generalizing ys w with
  | nil =>
    have : ys=[a] := by simpa [insert] using h.symm
    subst ys; rfl
  | cons b bs ih =>
    simp only [insert] at h
    split at h
    · cases h; rfl
    · split at h
      · rename_i hi
        cases he : insert a bs with
        | none => simp only [he,Option.map_none] at h; contradiction
        | some zs =>
          simp only [he,Option.map_some,Option.some.injEq] at h
          subst ys
          change run zs (b.apply w) = run bs (b.apply (a.apply w))
          rw [ih he, independent_comm hi]
      · contradiction

def normalize : List Op → Option (List Op)
  | [] => some []
  | a::xs => (normalize xs).bind (insert a)

theorem normalize_run {xs ys : List Op} (h : normalize xs=some ys) (w : Poly) :
    run ys w = run xs w := by
  induction xs generalizing ys w with
  | nil =>
    have : ys=[] := by simpa [normalize] using h.symm
    subst ys; rfl
  | cons a xs ih =>
    simp only [normalize] at h
    cases he : normalize xs with
    | none => simp only [he,Option.bind_none] at h; contradiction
    | some zs =>
      simp only [he,Option.bind_some] at h
      rw [insert_run h, ih he]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.Traversal
