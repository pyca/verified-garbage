import VerifiedGarbage.Proof.MlDsa.Arith.Ntt

namespace VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
open VG.Spec.MlDsa VG.Proof.MlDsa.Arith

theorem bflyInv_comm (w : Poly) {j len k step : Nat} (hl : 0 < len) (hm : 0 < step)
    (hj : j + len < n) (hk : k + step < n)
    (h00 : j ≠ k) (h01 : j ≠ k + step) (h10 : j + len ≠ k) (h11 : j + len ≠ k + step)
    (z t : Zq) :
    bflyInv (bflyInv w j len z) k step t = bflyInv (bflyInv w k step t) j len z := by
  apply ext_getElem!
  intro i hi
  rw [bflyInv_get (bflyInv w j len z) hm hk t hi, bflyInv_get (bflyInv w k step t) hl hj z hi,
    bflyInv_get w hl hj z (by omega : k < n), bflyInv_get w hl hj z hk,
    bflyInv_get w hl hj z hi, bflyInv_get w hm hk t (by omega : j < n),
    bflyInv_get w hm hk t hj, bflyInv_get w hm hk t hi]
  simp only [h00, h01, h10, h11, Ne.symm h00, Ne.symm h01, Ne.symm h10,
    Ne.symm h11, ite_false]
  by_cases h0 : i=k <;> by_cases h1 : i=k+step <;>
    by_cases h2 : i=j <;> by_cases h3 : i=j+len <;> simp_all

/-- A butterfly with its root-table index retained symbolically. -/
structure Op where
  index : Nat
  length : Nat
  rootIndex : Nat
  deriving DecidableEq, Repr

def Op.apply (o : Op) (w : Poly) : Poly := bflyInv w o.index o.length (-zetas o.rootIndex)
def run (ops : List Op) (w : Poly) : Poly := ops.foldl (fun w o => o.apply w) w

def localSlice (u : Nat) : List Op :=
  (([1,2] : List Nat).flatMap fun len =>
    (List.range 4).flatMap fun group =>
      (List.range (4/len)).flatMap fun g =>
        (List.range len).map fun j =>
          ⟨32*u+8*group+2*len*g+j,len,256/len-1-(16*u/len+4*group/len+g)⟩) ++
  (([1,2,4] : List Nat).flatMap fun gap =>
    (List.range (4/gap)).flatMap fun g =>
      (List.range gap).flatMap fun j =>
        (List.range 4).map fun e =>
          ⟨32*u+8*gap*g+4*j+e,4*gap,64/gap-1-(4*u/gap+g)⟩)

def stridedSlice (u : Nat) : List Op :=
  ([1,2,4] : List Nat).flatMap fun gap =>
    (List.range (4/gap)).flatMap fun g =>
      (List.range gap).flatMap fun j =>
        (List.range 4).map fun e =>
          ⟨64*gap*g+32*j+4*u+e,32*gap,8/gap-1-g⟩

def localSchedule : List Op := (List.range 8).flatMap localSlice
def stridedSchedule : List Op := (List.range 8).flatMap stridedSlice

def layerSchedule (len : Nat) : List Op :=
  (List.range (128/len)).flatMap fun g =>
    (List.range len).map fun j => ⟨2*len*g+j,len,256/len-1-g⟩

def standardLocal : List Op := ([1,2,4,8,16] : List Nat).flatMap layerSchedule
def standardStrided : List Op := ([32,64,128] : List Nat).flatMap layerSchedule

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
  exact bflyInv_comm w h'.1 h'.2.2.1 h'.2.1 h'.2.2.2.1
    h'.2.2.2.2.1 h'.2.2.2.2.2.1 h'.2.2.2.2.2.2.1 h'.2.2.2.2.2.2.2 _ _

def key (o : Op) : Nat := o.length*256+o.index

theorem run_cons (a : Op) (xs : List Op) (w : Poly) : run (a::xs) w=run xs (a.apply w) := rfl

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
    · cases h; simp only [run, List.foldl_cons]
    · split at h
      · rename_i hi
        cases he : insert a bs with
        | none => simp only [he,Option.map_none] at h; contradiction
        | some zs =>
          simp only [he,Option.map_some,Option.some.injEq] at h
          subst ys
          rw [run_cons, run_cons]
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

end VG.Proof.MlDsa.AArch64.Optimized.InverseTraversal
