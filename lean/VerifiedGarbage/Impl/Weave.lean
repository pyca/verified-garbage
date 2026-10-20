module

/-!
# Interleaving two blocks of code

`weave a b` merges the instruction lists `a` and `b`, of any ISA, keeping each
at the same relative progress, so that an out-of-order core finds
instructions of both in its window. Blocks whose footprints are independent
run as `a` and then `b` (`Proof/Framework/Interleave.lean`, `WP.weave`);
`weaveG` keeps groups of instructions together.
-/

@[expose] public section

namespace VG.Impl.Weave

/-- Interleave `a` and `b`, keeping each at the same relative progress, `i`
instructions of `a` (of `n`) and `j` of `b` (of `m`) taken. -/
def weaveGo {α : Type} (n m : Nat) : Nat → Nat → Nat → List α → List α → List α
  | 0, _, _, a, b => a ++ b
  | _ + 1, _, _, [], b => b
  | _ + 1, _, _, x :: a, [] => x :: a
  | f + 1, i, j, x :: a, y :: b =>
    if i * m ≤ j * n then x :: weaveGo n m f (i + 1) j a (y :: b) else y :: weaveGo n m f i (j + 1) (x :: a) b

def weave {α : Type} (a b : List α) : List α := weaveGo a.length b.length (a.length + b.length) 0 0 a b

/-- `weave` of groups of instructions, each kept together (e.g. an AArch64
`aese` and the `aesmc` after it, which cores fuse only when adjacent). -/
def weaveG {α : Type} (a b : List (List α)) : List α := (weave a b).flatten

end VG.Impl.Weave
