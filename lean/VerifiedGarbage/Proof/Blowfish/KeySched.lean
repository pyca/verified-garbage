import VerifiedGarbage.Proof.Blowfish.Feistel

/-!
# The key schedule, one encryption at a time

`ksIter key j`: the schedule and the last output after `j` of the 521
encryptions; `ksIter_succ` is one more, and `expandKey key = (ksIter key
521).1`.
-/

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- The initial P-array XORed with the key, and the initial S-boxes. -/
def keyed (key : List Byte) : Schedule :=
  Vector.ofFn fun i =>
    if i.val < 18 then initial.getD i.val 0 ^^^ keyWord key i.val else initial.getD i.val 0

def ksStep (st : Schedule × Word × Word) (j : Nat) : Schedule × Word × Word :=
  let out := encryptWords st.1 st.2.1 st.2.2
  ((st.1.set! (2 * j) out.1).set! (2 * j + 1) out.2, out.1, out.2)

def ksIter (key : List Byte) (j : Nat) : Schedule × Word × Word :=
  (List.range j).foldl ksStep (keyed key, 0, 0)

theorem ksIter_succ (key : List Byte) (j : Nat) : ksIter key (j + 1) = ksStep (ksIter key j) j := by
  simp only [ksIter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem foldl_congr_fn {α β : Type} {f g : α → β → α} (h : ∀ a b, f a b = g a b) (l : List β) (a : α) :
    l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp only [List.foldl_cons, h, ih]

theorem expandKey_eq (key : List Byte) : expandKey key = (ksIter key 521).1 := by
  have hf : (fun ((k : Schedule), xL, xR) j =>
      let (xL, xR) := encryptWords k xL xR
      ((k.set! (2 * j) xL).set! (2 * j + 1) xR, xL, xR)) = ksStep := by
    funext ⟨k, xL, xR⟩ j; rfl
  unfold expandKey ksIter
  dsimp only
  rw [hf]
  rfl

end VG.Proof.Blowfish
