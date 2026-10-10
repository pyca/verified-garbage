import VerifiedGarbage.Proof.Framework.Slots
import VerifiedGarbage.Proof.Framework.KernelList

/-!
# `Slots` operations for the kernel

The kernel evaluates structural recursion (compiled to `brecOn`) several times
slower than `List.rec` (`VG.KList`). `Slots` itself imports only Lean core,
for the precompiled hint search, which cannot compile `List.rec`; here are the
operations a taint domain's kernel-evaluated step uses, written with
`List.rec`, each proven equal to `Slots`'.
-/

namespace VG.Slots

/-- `nth`, with `List.rec`. -/
def nthK (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih i => Nat.casesOn (motive := fun _ => Nat) i a fun j => ih j) l

/-- `modify`, with `List.rec`. -/
def modifyK (f : Nat → Nat) (l : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat)
    (fun i => Nat.rec (motive := fun _ => List Nat) [f 0] (fun _ ih => 0 :: ih) i)
    (fun a l ih i => Nat.casesOn (motive := fun _ => List Nat) i (f a :: l) fun j => a :: ih j) l

/-- `subsetL`, with `List.rec`. -/
def subsetLK (s : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun a _ ih t => List.casesOn (motive := fun _ => Bool) t (Nat.beq a 0 && ih [])
      fun b t => Nat.beq (Nat.land a b) a && ih t) s

/-- `covers`, for the kernel. -/
def coversK (S : Slots) (i d w : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight (nthK S.masks i) d) (Nat.sub (Nat.pow 2 w) 1)) (Nat.sub (Nat.pow 2 w) 1)

/-- Some of the `w` bytes at offset `d` of region `i` are public. -/
def touchesK (S : Slots) (i d w : Nat) : Bool :=
  !Nat.beq (Nat.land (Nat.shiftRight (nthK S.masks i) d) (Nat.sub (Nat.pow 2 w) 1)) 0

/-- `add`, for the kernel. -/
def addK (S : Slots) (i d w : Nat) : Slots := ⟨modifyK (fun m => Nat.lor m (bits d w)) S.masks i⟩

/-- `remove`, for the kernel. -/
def removeK (S : Slots) (i d w : Nat) : Slots :=
  ⟨modifyK (fun m => Nat.xor m (Nat.land m (bits d w))) S.masks i⟩

/-- `subset`, for the kernel. -/
def subsetK (S T : Slots) : Bool := subsetLK S.masks T.masks

theorem nthK_eq : nthK = nth := by
  funext l i
  induction l generalizing i with
  | nil => rfl
  | cons a l ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem modifyK_eq : modifyK = modify := by
  funext f l i
  induction l generalizing i with
  | nil =>
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg (List.cons 0) ih
  | cons a l ih => cases i with
    | zero => rfl
    | succ i => exact congrArg (List.cons a) (ih i)

theorem subsetLK_eq : subsetLK = subsetL := by
  funext s t
  induction s generalizing t with
  | nil => rfl
  | cons a s ih => cases t with
    | nil => exact congrArg (Nat.beq a 0 && ·) (ih [])
    | cons b t => exact congrArg (Nat.beq (Nat.land a b) a && ·) (ih t)

theorem coversK_eq : coversK = covers := by
  funext S i d w; simp only [coversK, covers, get, nthK_eq]

theorem addK_eq : addK = add := by
  funext S i d w; simp only [addK, add, modifyK_eq]

theorem removeK_eq : removeK = remove := by
  funext S i d w; simp only [removeK, remove, modifyK_eq]

theorem subsetK_eq : subsetK = subset := by
  funext S T; simp only [subsetK, subset, subsetLK_eq]

theorem has_of_coversK {S : Slots} {i d w : Nat} (h : S.coversK i d w = true) {k : Nat}
    (h₁ : d ≤ k) (h₂ : k < d + w) : S.has i k = true := by
  rw [coversK_eq] at h; exact (covers_iff S i d w).mp h k h₁ h₂

theorem not_has_of_touchesK {S : Slots} {i d w : Nat} (h : S.touchesK i d w = false) {k : Nat}
    (h₁ : d ≤ k) (h₂ : k < d + w) : S.has i k = false := by
  simp only [touchesK, Bool.not_eq_false', nthK_eq] at h
  have e : (nth S.masks i >>> d) &&& (2 ^ w - 1) = 0 := by
    have := Nat.eq_of_beq_eq_true h; exact this
  have := congrArg (·.testBit (k - d)) e
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
    show d + (k - d) = k by omega, show decide (k - d < w) = true from decide_eq_true (by omega),
    Bool.and_true] at this
  rw [has_eq, get]; exact this

end VG.Slots
