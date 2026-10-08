import VerifiedGarbage.Spec.Blowfish

/-!
# The Feistel network, round by round

`iter K order m (xL, xR)`: the halves after the first `m` rounds of
`feistel`, before its last swap is undone; `iter_succ` is one more round,
and `feistel_eq` the rest of `feistel` after sixteen.
-/

namespace VG.Proof.Blowfish

open VG VG.Spec.Blowfish

/-- One round: `xL ^= P`, `xR ^= F(xL)`, swap. -/
def roundStep (K : Schedule) (order : Nat → Nat) (st : Word × Word) (i : Nat) : Word × Word :=
  let xL := st.1 ^^^ pEntry K (order i)
  (f K xL ^^^ st.2, xL)

def iter (K : Schedule) (order : Nat → Nat) (m : Nat) (st : Word × Word) : Word × Word :=
  (List.range m).foldl (roundStep K order) st

theorem iter_succ (K : Schedule) (order : Nat → Nat) (m : Nat) (st : Word × Word) :
    iter K order (m + 1) st = roundStep K order (iter K order m st) m := by
  simp only [iter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem iter_zero (K : Schedule) (order : Nat → Nat) (st : Word × Word) : iter K order 0 st = st := rfl

theorem feistel_eq (K : Schedule) (order : Nat → Nat) (xL xR : Word) :
    feistel K order xL xR =
      ((iter K order 16 (xL, xR)).2 ^^^ pEntry K (order 17),
        (iter K order 16 (xL, xR)).1 ^^^ pEntry K (order 16)) := by
  simp only [feistel, iter]
  rfl

end VG.Proof.Blowfish
