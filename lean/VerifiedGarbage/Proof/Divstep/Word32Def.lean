/-!
# Divsteps on 32-bit words: the definitions

The word divstep `wstep` and its iterates, apart from their proofs
(`Word.lean`), so that code proven to compute them needs no algebra.
-/

namespace VG.Proof.Divstep.W32

/-- The words of a step: `d`, the low bits of `f` and `g`, and the matrix. -/
structure WSt where
  D : BitVec 32
  F : BitVec 32
  G : BitVec 32
  U : BitVec 32
  V : BitVec 32
  Q : BitVec 32
  R : BitVec 32

/-- A divstep on words. -/
def wstep (w : WSt) : WSt :=
  let B := 0 - (w.G &&& 1)
  let S := ((w.D >>> 31) - 1) &&& B
  let G1 := w.G + (((w.F ^^^ S) - S) &&& B)
  let Q1 := w.Q + (((w.U ^^^ S) - S) &&& B)
  let R1 := w.R + (((w.V ^^^ S) - S) &&& B)
  ⟨((w.D ^^^ S) - S) + 2, w.F + (G1 &&& S), G1 >>> 1, (w.U + (Q1 &&& S)) <<< 1,
    (w.V + (R1 &&& S)) <<< 1, Q1, R1⟩

/-- `n` such steps. -/
def wsteps : Nat → WSt → WSt
  | 0, w => w
  | n + 1, w => wsteps n (wstep w)

theorem wsteps_succ (n : Nat) (w : WSt) : wsteps (n + 1) w = wstep (wsteps n w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => rw [wsteps, ih, wsteps]

end VG.Proof.Divstep.W32
