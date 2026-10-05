import VerifiedGarbage.Spec.Blake2
import VerifiedGarbage.Proof.Argon2.PermuteRows
import VerifiedGarbage.Spec.Blake2.Contract
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Spec`. -/
section

/-!
# Facts about the BLAKE2 specification
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2

variable {w : Nat} (P : VG.Spec.Blake2.Params w)

/-- The four words `G` computes from `v[a], v[b], v[c], v[d]` and the message
words `x, y`, in the order of the RFC's steps. -/
def mix (va vb vc vd x y : BitVec w) : BitVec w × BitVec w × BitVec w × BitVec w :=
  let a := va + vb + x
  let d := (vd ^^^ a).rotateRight P.R1
  let c := vc + d
  let b := (vb ^^^ c).rotateRight P.R2
  let a := a + b + y
  let d := (d ^^^ a).rotateRight P.R3
  let c := c + d
  let b := (b ^^^ c).rotateRight P.R4
  (a, b, c, d)

theorem set_get (v : Work w) (a : Fin 16) (x : BitVec w) (k : Nat) (hk : k < 16) :
    (v.set a x)[k] = if a.1 = k then x else v[k] := by
  simp [Vector.getElem_set]

theorem set_get_fin (v : Work w) (a b : Fin 16) (x : BitVec w) :
    (v.set a x)[b] = if a.1 = b.1 then x else v[b] := by
  simp [Vector.getElem_set]

/-- Word `k` after `G` on four distinct words. -/
theorem G_get (v : Work w) {a b c d : Fin 16} (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1)
    (had : a.1 ≠ d.1) (hbc : b.1 ≠ c.1) (hbd : b.1 ≠ d.1) (hcd : c.1 ≠ d.1) (x y : BitVec w)
    (k : Nat) (hk : k < 16) :
    (G P v a b c d x y)[k] =
      if b.1 = k then (VG.Proof.Blake2.mix P v[a] v[b] v[c] v[d] x y).2.1
      else if c.1 = k then (VG.Proof.Blake2.mix P v[a] v[b] v[c] v[d] x y).2.2.1
      else if d.1 = k then (VG.Proof.Blake2.mix P v[a] v[b] v[c] v[d] x y).2.2.2
      else if a.1 = k then (VG.Proof.Blake2.mix P v[a] v[b] v[c] v[d] x y).1 else v[k] := by
  simp only [G, VG.Proof.Blake2.set_get, VG.Proof.Blake2.set_get_fin, hab, hac, had, hbc, hbd, hcd, Ne.symm hab, Ne.symm hac,
    Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd, ite_true, ite_false]
  by_cases eb : b.1 = k
  · subst eb; simp only [ite_true, hab, hbc.symm, hbd.symm, ite_false, VG.Proof.Blake2.mix]
  by_cases ec : c.1 = k
  · subst ec; simp only [ite_true, eb, hac, hcd.symm, ite_false, VG.Proof.Blake2.mix]
  by_cases ed : d.1 = k
  · subst ed; simp only [ite_true, eb, ec, had, ite_false, VG.Proof.Blake2.mix]
  by_cases ea : a.1 = k
  · subst ea; simp only [ite_true, eb, ec, ed, ite_false, VG.Proof.Blake2.mix]
  simp only [eb, ec, ed, ea, ite_false]

/-- `compressBlocks` on `n + 1` blocks: `n` blocks, then the last. -/
theorem compressBlocks_succ (h : HashValue w) (m : Mem) (p : Addr) (n t : Nat) (f : Bool) :
    compressBlocks P h m p (n + 1) t f =
      F P (compressBlocks P h m p n t f) (blockAt w m (p + BitVec.ofNat 64 (blockBytes w * n)))
        (t + n * blockBytes w) f := by
  simp only [compressBlocks, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem compressBlocks_zero (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 0 t f = h := rfl

/-! ## Words of a block in memory -/

/-- A little-endian read is `leBytes` of the bytes. -/
theorem read_eq_leBytes (m : Mem) (a : Addr) (n : Nat) :
    m.read a n = leBytes n (fun i => m (a + BitVec.ofNat 64 i)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    show (m.read (a + 1) n ++ m a : BitVec (8 * n + 8)) = (leBytes n _ ++ _ : BitVec (8 * n + 8))
    rw [ih]
    have e : (fun i => m (a + 1 + BitVec.ofNat 64 i)) = fun i => m (a + BitVec.ofNat 64 (i + 1)) := by
      funext i; congr 1
      rw [BitVec.add_assoc, BitVec.add_comm 1, ← BitVec.ofNat_add_ofNat]; rfl
    rw [e]
    simp

/-- Word `j` of the block at `p` is the little-endian word at `p + (w/8)·j`. -/
theorem blockAt_word (m : Mem) (p : Addr) (j : Nat) (hj : j < 16) :
    blockAt w m p ⟨j, hj⟩ = m.readW (p + BitVec.ofNat 64 (w / 8 * j)) w := by
  simp only [blockAt, VG.Spec.Blake2.parseBlock, leWord, Mem.readW, VG.Proof.Blake2.read_eq_leBytes]
  congr 2
  funext i
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

end VG.Proof.Blake2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Cols`. -/
section

/-!
# A BLAKE2 round on four columns at once, for any word size

As `Lanes.lean` for BLAKE2b: the work vector as four rows of four words
(`4k…4k+3` for `k < 4`); the four column `G`s of a round are `G` on each
column of the rows at once (`mixColsP`), with the message words of column
`q` (`x q`, `y q`); the four diagonal `G`s are the same after rows 0, 2 and
3 are rotated left by three, one and two places (`rotInP`; row 1 stays), so
that column `q` holds diagonal `(q + 3) mod 4`, rotated back after it
(`rotOutP`). This is how code keeping each row in one vector register
computes a round (`round_colsP`).
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2

variable {w : Nat} (P : VG.Spec.Blake2.Params w)

/-- Component `k` of the result of `mix`: `a`, `b`, `c` or `d`. -/
def pick4 (k : Nat) (x : BitVec w × BitVec w × BitVec w × BitVec w) : BitVec w :=
  match k with
  | 0 => x.1
  | 1 => x.2.1
  | 2 => x.2.2.1
  | _ => x.2.2.2

/-- `G` on each column `q` (words `q`, `4 + q`, `8 + q`, `12 + q`) at once,
with the message words `x q` and `y q`. -/
def mixColsP (x y : Nat → BitVec w) (v : Work w) : Work w :=
  Vector.ofFn fun j => VG.Proof.Blake2.pick4 (j.val / 4)
    (VG.Proof.Blake2.mix P (v[j.val % 4]'(by omega)) (v[4 + j.val % 4]'(by omega)) (v[8 + j.val % 4]'(by omega))
      (v[12 + j.val % 4]'(by omega)) (x (j.val % 4)) (y (j.val % 4)))

/-- Rows 0, 2 and 3 rotated left by three, one and two places. -/
def rotInP (v : Work w) : Work w :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + j.val / 4 + 3) % 4]'(by omega)

/-- Rows 0, 2 and 3 rotated left by one, three and two places (back). -/
def rotOutP (v : Work w) : Work w :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + 3 * (j.val / 4) + 1) % 4]'(by omega)

theorem mixColsP_get (x y : Nat → BitVec w) (v : Work w) (j : Nat) (hj : j < 16) :
    (VG.Proof.Blake2.mixColsP P x y v)[j] = VG.Proof.Blake2.pick4 (j / 4) (VG.Proof.Blake2.mix P (v[j % 4]'(by omega)) (v[4 + j % 4]'(by omega))
      (v[8 + j % 4]'(by omega)) (v[12 + j % 4]'(by omega)) (x (j % 4)) (y (j % 4))) := by
  simp only [VG.Proof.Blake2.mixColsP, Vector.getElem_ofFn]

theorem rotInP_get (v : Work w) (j : Nat) (hj : j < 16) :
    (VG.Proof.Blake2.rotInP v)[j] = v[4 * (j / 4) + (j % 4 + j / 4 + 3) % 4]'(by omega) := by
  simp only [VG.Proof.Blake2.rotInP, Vector.getElem_ofFn]

theorem rotOutP_get (v : Work w) (j : Nat) (hj : j < 16) :
    (VG.Proof.Blake2.rotOutP v)[j] = v[4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4]'(by omega) := by
  simp only [VG.Proof.Blake2.rotOutP, Vector.getElem_ofFn]

theorem cases16' {j : Nat} (hj : j < 16) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
    j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by
  omega

/-- The value of a literal index. -/
theorem val_lit16 (k : Nat) : (no_index (OfNat.ofNat k : Fin 16)).val = k % 16 := rfl

theorem G_getP (v : Work w) {a c d e : Fin 16} (hab : a.1 ≠ c.1) (hac : a.1 ≠ d.1)
    (had : a.1 ≠ e.1) (hcd : c.1 ≠ d.1) (hce : c.1 ≠ e.1) (hde : d.1 ≠ e.1) (x y : BitVec w)
    (k : Nat) (hk : k < 16) :
    (G P v a c d e x y)[k] =
      if c.1 = k then (VG.Proof.Blake2.mix P v[a.1] v[c.1] v[d.1] v[e.1] x y).2.1
      else if d.1 = k then (VG.Proof.Blake2.mix P v[a.1] v[c.1] v[d.1] v[e.1] x y).2.2.1
      else if e.1 = k then (VG.Proof.Blake2.mix P v[a.1] v[c.1] v[d.1] v[e.1] x y).2.2.2
      else if a.1 = k then (VG.Proof.Blake2.mix P v[a.1] v[c.1] v[d.1] v[e.1] x y).1 else v[k] :=
  VG.Proof.Blake2.G_get P v hab hac had hcd hce hde x y k hk

/-- The four column `G`s of a round. -/
theorem columns_eqP (x y : Nat → BitVec w) (v : Work w) :
    G P (G P (G P (G P v 0 4 8 12 (x 0) (y 0)) 1 5 9 13 (x 1) (y 1)) 2 6 10 14 (x 2) (y 2))
      3 7 11 15 (x 3) (y 3) = VG.Proof.Blake2.mixColsP P x y v := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Blake2.mixColsP_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := VG.Proof.Blake2.cases16' hj
  all_goals
    simp (disch := decide) only [VG.Proof.Blake2.G_getP, VG.Proof.Blake2.val_lit16, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, VG.Proof.Blake2.pick4]

/-- The four diagonal `G`s of a round, with the message words `x i` and `y i`
of diagonal `i`. -/
theorem diagonals_eqP (x y : Nat → BitVec w) (v : Work w) :
    G P (G P (G P (G P v 0 5 10 15 (x 0) (y 0)) 1 6 11 12 (x 1) (y 1)) 2 7 8 13 (x 2) (y 2))
      3 4 9 14 (x 3) (y 3) =
      VG.Proof.Blake2.rotOutP (VG.Proof.Blake2.mixColsP P (fun q => x ((q + 3) % 4)) (fun q => y ((q + 3) % 4)) (VG.Proof.Blake2.rotInP v)) := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Blake2.rotOutP_get, VG.Proof.Blake2.rotInP_get, VG.Proof.Blake2.mixColsP_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := VG.Proof.Blake2.cases16' hj
  all_goals
    simp (disch := decide) only [VG.Proof.Blake2.G_getP, VG.Proof.Blake2.val_lit16, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, VG.Proof.Blake2.pick4]

/-- Round `r` on four columns: the column `G`s, then the diagonal ones. -/
theorem round_colsP (m : VG.Spec.Blake2.Block w) (v : Work w) (r : Nat) :
    round P m v r =
      VG.Proof.Blake2.rotOutP (VG.Proof.Blake2.mixColsP P (fun q => m (sigmaAt r (8 + 2 * ((q + 3) % 4))))
        (fun q => m (sigmaAt r (9 + 2 * ((q + 3) % 4))))
        (VG.Proof.Blake2.rotInP (VG.Proof.Blake2.mixColsP P (fun q => m (sigmaAt r (2 * q))) (fun q => m (sigmaAt r (2 * q + 1))) v))) := by
  rw [← VG.Proof.Blake2.diagonals_eqP P (fun i => m (sigmaAt r (8 + 2 * i))) (fun i => m (sigmaAt r (9 + 2 * i))),
    ← VG.Proof.Blake2.columns_eqP]
  rfl

end VG.Proof.Blake2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Lanes`. -/
section

/-!
# A BLAKE2b round on four columns at once

The work vector as four rows of four words (`4k…4k+3` for `k < 4`): the four
column `G`s of a round are `G` on each column of the rows at once
(`mixCols`), with the message words of column `q` (`x q`, `y q`). The four
diagonal `G`s are the same after rows 0, 2 and 3 are rotated left by three,
one and two places (`rotIn`; row 1 stays), so that column `q` holds diagonal
`(q + 3) mod 4`, rotated back after it (`rotOut`). This is how code keeping
each row in one vector register (of four 64-bit lanes) computes a round
(`round_lanes`).
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2
open VG.Proof.Argon2 (mixAt cases16 val_lit)

/-- `G` on each column `q` (words `q`, `4 + q`, `8 + q`, `12 + q`) at once,
with the message words `x q` and `y q`. -/
def mixCols (x y : Nat → BitVec 64) (v : Work 64) : Work 64 :=
  Vector.ofFn fun j => mixAt (j.val / 4)
    (VG.Proof.Blake2.mix b (v[j.val % 4]'(by omega)) (v[4 + j.val % 4]'(by omega)) (v[8 + j.val % 4]'(by omega))
      (v[12 + j.val % 4]'(by omega)) (x (j.val % 4)) (y (j.val % 4)))

/-- Rows 0, 2 and 3 rotated left by three, one and two places. -/
def rotIn (v : Work 64) : Work 64 :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + j.val / 4 + 3) % 4]'(by omega)

/-- Rows 0, 2 and 3 rotated left by one, three and two places (back). -/
def rotOut (v : Work 64) : Work 64 :=
  Vector.ofFn fun j => v[4 * (j.val / 4) + (j.val % 4 + 3 * (j.val / 4) + 1) % 4]'(by omega)

theorem mixCols_get (x y : Nat → BitVec 64) (v : Work 64) (j : Nat) (hj : j < 16) :
    (VG.Proof.Blake2.mixCols x y v)[j] = mixAt (j / 4) (VG.Proof.Blake2.mix b (v[j % 4]'(by omega)) (v[4 + j % 4]'(by omega))
      (v[8 + j % 4]'(by omega)) (v[12 + j % 4]'(by omega)) (x (j % 4)) (y (j % 4))) := by
  simp only [VG.Proof.Blake2.mixCols, Vector.getElem_ofFn]

theorem rotIn_get (v : Work 64) (j : Nat) (hj : j < 16) :
    (VG.Proof.Blake2.rotIn v)[j] = v[4 * (j / 4) + (j % 4 + j / 4 + 3) % 4]'(by omega) := by
  simp only [VG.Proof.Blake2.rotIn, Vector.getElem_ofFn]

theorem rotOut_get (v : Work 64) (j : Nat) (hj : j < 16) :
    (VG.Proof.Blake2.rotOut v)[j] = v[4 * (j / 4) + (j % 4 + 3 * (j / 4) + 1) % 4]'(by omega) := by
  simp only [VG.Proof.Blake2.rotOut, Vector.getElem_ofFn]

theorem G_get' (v : Work 64) {a c d e : Fin 16} (hab : a.1 ≠ c.1) (hac : a.1 ≠ d.1)
    (had : a.1 ≠ e.1) (hbc : c.1 ≠ d.1) (hbd : c.1 ≠ e.1) (hcd : d.1 ≠ e.1) (x y : BitVec 64)
    (k : Nat) (hk : k < 16) :
    (G b v a c d e x y)[k] =
      if c.1 = k then (VG.Proof.Blake2.mix b v[a.1] v[c.1] v[d.1] v[e.1] x y).2.1
      else if d.1 = k then (VG.Proof.Blake2.mix b v[a.1] v[c.1] v[d.1] v[e.1] x y).2.2.1
      else if e.1 = k then (VG.Proof.Blake2.mix b v[a.1] v[c.1] v[d.1] v[e.1] x y).2.2.2
      else if a.1 = k then (VG.Proof.Blake2.mix b v[a.1] v[c.1] v[d.1] v[e.1] x y).1 else v[k] :=
  VG.Proof.Blake2.G_get b v hab hac had hbc hbd hcd x y k hk

/-- The four column `G`s of a round. -/
theorem columns_eq (x y : Nat → BitVec 64) (v : Work 64) :
    G b (G b (G b (G b v 0 4 8 12 (x 0) (y 0)) 1 5 9 13 (x 1) (y 1)) 2 6 10 14 (x 2) (y 2))
      3 7 11 15 (x 3) (y 3) = VG.Proof.Blake2.mixCols x y v := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Blake2.mixCols_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp (disch := decide) only [VG.Proof.Blake2.G_get', val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceEqDiff, ↓reduceIte, mixAt]

/-- The four diagonal `G`s of a round, with the message words `x i` and `y i`
of diagonal `i`. -/
theorem diagonals_eq (x y : Nat → BitVec 64) (v : Work 64) :
    G b (G b (G b (G b v 0 5 10 15 (x 0) (y 0)) 1 6 11 12 (x 1) (y 1)) 2 7 8 13 (x 2) (y 2))
      3 4 9 14 (x 3) (y 3) =
      VG.Proof.Blake2.rotOut (VG.Proof.Blake2.mixCols (fun q => x ((q + 3) % 4)) (fun q => y ((q + 3) % 4)) (VG.Proof.Blake2.rotIn v)) := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Blake2.rotOut_get, VG.Proof.Blake2.rotIn_get, VG.Proof.Blake2.mixCols_get]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl := cases16 hj
  all_goals
    simp (disch := decide) only [VG.Proof.Blake2.G_get', val_lit, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd,
      Nat.reduceMul, Nat.reduceEqDiff, ↓reduceIte, mixAt]

/-- Round `r` of BLAKE2b on four columns: the column `G`s, then the diagonal
ones. -/
theorem round_lanes (m : Block 64) (v : Work 64) (r : Nat) :
    round b m v r =
      VG.Proof.Blake2.rotOut (VG.Proof.Blake2.mixCols (fun q => m (sigmaAt r (8 + 2 * ((q + 3) % 4))))
        (fun q => m (sigmaAt r (9 + 2 * ((q + 3) % 4))))
        (VG.Proof.Blake2.rotIn (VG.Proof.Blake2.mixCols (fun q => m (sigmaAt r (2 * q))) (fun q => m (sigmaAt r (2 * q + 1))) v))) := by
  rw [← VG.Proof.Blake2.diagonals_eq (fun i => m (sigmaAt r (8 + 2 * i))) (fun i => m (sigmaAt r (9 + 2 * i))),
    ← VG.Proof.Blake2.columns_eq]
  rfl

end VG.Proof.Blake2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Stream`. -/
section

/-!
# Streaming BLAKE2: target-independent lemmas

The streaming code keeps `r` bytes of the data `d` in the buffer (`ReprR`):
`Repr` is `ReprR` with `r = bufLen w |d|` (the last 1 to `bb` bytes), and
within `update` the buffer may also be full or empty. Each step of the code is
one lemma here: copying bytes into the buffer (`reprR_append`), compressing
the full buffer (`reprR_flush`), compressing blocks straight from the data
(`reprR_blocks`), and the final compression (`finalHash_eq`).
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2

section
variable {w : Nat}

/-- The number of bytes a streaming state with a byte count of `n` holds in
its buffer: the last `1` to `bb`, none if `n = 0`. -/
def bufLen (w n : Nat) : Nat := if n = 0 then 0 else (n - 1) % blockBytes w + 1

/-- Where the buffer starts in the streaming state. -/
abbrev bufOff (w : Nat) : Nat := 8 * (w / 8)

variable (P : VG.Spec.Blake2.Params w)

/-- The streaming state at `p` holds the last `r ≤ bb` bytes of the data `d`
in its buffer, and its hash state is `h0` updated with every block before
them. -/
def ReprR (h0 : HashValue w) (mem : Mem) (p : Addr) (d : List Byte) (r : Nat) : Prop :=
  r ≤ blockBytes w ∧ r ≤ d.length ∧ (d.length - r) % blockBytes w = 0 ∧
  stateAt w mem p = compressList P h0 d ((d.length - r) / blockBytes w) ∧
  bytesAt mem (p + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w)) r = d.drop (d.length - r)

/-! ## Lists and blocks -/

theorem leBytes_congr {n : Nat} {f g : Nat → Byte} (h : ∀ i < n, f i = g i) :
    leBytes n f = leBytes n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [leBytes]
    rw [ih fun i hi => h (i + 1) (by omega), h 0 (by omega)]

theorem parseBlock_congr {f g : Nat → Byte} (h : ∀ k < blockBytes w, f k = g k) :
    VG.Spec.Blake2.parseBlock (w := w) f = VG.Spec.Blake2.parseBlock g := by
  funext j
  simp only [VG.Spec.Blake2.parseBlock, leWord]
  congr 1
  apply VG.Proof.Blake2.leBytes_congr
  intro i hi
  apply h
  have : w / 8 * j.1 ≤ w / 8 * 15 := Nat.mul_le_mul_left _ (by omega)
  simp only [blockBytes]; omega

theorem getD_append_left {d x : List Byte} {i : Nat} (h : i < d.length) :
    (d ++ x).getD i 0 = d.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right {d x : List Byte} {i : Nat} (h : d.length ≤ i) :
    (d ++ x).getD i 0 = x.getD (i - d.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem F_congr {h : HashValue w} {b b' : VG.Spec.Blake2.Block w} {t t' : Nat} {f : Bool} (hb : b = b')
    (ht : t = t') : F P h b t f = F P h b' t' f := by subst hb ht; rfl

theorem compressList_succ (h : HashValue w) (d : List Byte) (n : Nat) :
    compressList P h d (n + 1) =
      F P (compressList P h d n) (VG.Spec.Blake2.parseBlock fun k => d.getD (blockBytes w * n + k) 0)
        ((n + 1) * blockBytes w) false := by
  simp only [compressList, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `compressList` reads only the first `bb · n` bytes. -/
theorem compressList_congr (h : HashValue w) {d d' : List Byte} {n : Nat}
    (hd : ∀ i < blockBytes w * n, d.getD i 0 = d'.getD i 0) :
    compressList P h d n = compressList P h d' n := by
  induction n with
  | zero => simp only [compressList, List.range_zero, List.foldl_nil]
  | succ n ih =>
    rw [VG.Proof.Blake2.compressList_succ, VG.Proof.Blake2.compressList_succ, ih fun i hi => hd i (by rw [Nat.mul_succ]; omega)]
    exact congrArg (fun b => F P _ b _ false)
      (VG.Proof.Blake2.parseBlock_congr fun k hk => hd _ (by rw [Nat.mul_succ]; omega))

theorem compressList_append (h : HashValue w) {d : List Byte} (x : List Byte) {n : Nat}
    (hn : blockBytes w * n ≤ d.length) :
    compressList P h (d ++ x) n = compressList P h d n :=
  VG.Proof.Blake2.compressList_congr P h fun _ hi => VG.Proof.Blake2.getD_append_left (by omega)

/-! ## The number of bytes in the buffer -/

theorem bufLen_le (hbb : 0 < blockBytes w) (n : Nat) : VG.Proof.Blake2.bufLen w n ≤ blockBytes w := by
  unfold VG.Proof.Blake2.bufLen; split
  · omega
  · have := Nat.mod_lt (n - 1) hbb; omega

theorem bufLen_le_self (n : Nat) : VG.Proof.Blake2.bufLen w n ≤ n := by
  unfold VG.Proof.Blake2.bufLen; split
  · omega
  · have := Nat.mod_le (n - 1) (blockBytes w); omega

/-- The data before the buffer is `bb · compressed w d` bytes. -/
theorem sub_bufLen (d : List Byte) :
    d.length - VG.Proof.Blake2.bufLen w d.length = blockBytes w * compressed w d := by
  unfold VG.Proof.Blake2.bufLen compressed; split
  · simp [*]
  · have := Nat.div_add_mod (d.length - 1) (blockBytes w); omega

theorem bufLen_pos {n : Nat} (h : n ≠ 0) : 1 ≤ VG.Proof.Blake2.bufLen w n := by
  unfold VG.Proof.Blake2.bufLen; simp [h]

theorem repr_iff (hbb : 0 < blockBytes w) (h0 : HashValue w) (mem : Mem) (p : Addr) (d : List Byte) :
    VG.Spec.Blake2.Repr P h0 mem p d ↔ VG.Proof.Blake2.ReprR P h0 mem p d (VG.Proof.Blake2.bufLen w d.length) := by
  have e := VG.Proof.Blake2.sub_bufLen (w := w) d
  have e' : (d.length - VG.Proof.Blake2.bufLen w d.length) / blockBytes w = compressed w d := by
    rw [e, Nat.mul_div_cancel_left _ hbb]
  have e'' : d.length - blockBytes w * compressed w d = VG.Proof.Blake2.bufLen w d.length := by
    have := VG.Proof.Blake2.bufLen_le_self (w := w) d.length; omega
  unfold Spec.Blake2.Repr VG.Proof.Blake2.ReprR
  rw [e', e, e'', Nat.mul_mod_right]
  exact ⟨fun ⟨a, b⟩ => ⟨VG.Proof.Blake2.bufLen_le hbb _, VG.Proof.Blake2.bufLen_le_self _, rfl, a, b⟩, fun ⟨_, _, _, a, b⟩ => ⟨a, b⟩⟩

/-- A state holding at least one byte in its buffer is the streaming state of
its data. -/
theorem repr_of_reprR (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem : Mem} {p : Addr}
    {d : List Byte} {r : Nat} (h : VG.Proof.Blake2.ReprR P h0 mem p d r) (hr : 1 ≤ r) :
    Spec.Blake2.Repr P h0 mem p d := by
  have e : VG.Proof.Blake2.bufLen w d.length = r := by
    obtain ⟨h1, h2, h3, -⟩ := h
    have hq := Nat.div_add_mod (d.length - r) (blockBytes w)
    rw [h3, Nat.add_zero] at hq
    have hd : d.length ≠ 0 := by omega
    simp only [VG.Proof.Blake2.bufLen, hd, ite_false]
    rw [show d.length - 1 = (r - 1) + blockBytes w * ((d.length - r) / blockBytes w) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [VG.Proof.Blake2.repr_iff P hbb, e]; exact h

/-! ## The steps of `update` -/

/-- Appending `x` to the buffer, if it fits, with the hash state unchanged. -/
theorem reprR_append {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d x : List Byte} {r : Nat}
    (h : VG.Proof.Blake2.ReprR P h0 mem p d r) (hx : r + x.length ≤ blockBytes w)
    (hs : stateAt w mem' p = stateAt w mem p)
    (hb : bytesAt mem' (p + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w)) (r + x.length) =
      bytesAt mem (p + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w)) r ++ x) :
    VG.Proof.Blake2.ReprR P h0 mem' p (d ++ x) (r + x.length) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : (d ++ x).length - (r + x.length) = d.length - r := by simp; omega
  have hq : blockBytes w * ((d.length - r) / blockBytes w) ≤ d.length :=
    Nat.le_trans (Nat.mul_div_le _ _) (by omega)
  refine ⟨hx, by simp; omega, by rw [e]; exact h3, ?_, ?_⟩
  · rw [e, hs, h4, VG.Proof.Blake2.compressList_append P h0 x hq]
  · rw [e, hb, h5, List.drop_append_of_le_length (by omega)]

/-- Compressing the full buffer, which is not the last block: its counter is
`|d|`. -/
theorem reprR_flush (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem mem' : Mem} {p : Addr}
    {d : List Byte} (h : VG.Proof.Blake2.ReprR P h0 mem p d (blockBytes w))
    (hs : stateAt w mem' p =
      F P (stateAt w mem p) (blockAt w mem (p + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w))) d.length false) :
    VG.Proof.Blake2.ReprR P h0 mem' p d 0 := by
  obtain ⟨_, h2, h3, h4, h5⟩ := h
  have hq := Nat.div_add_mod (d.length - blockBytes w) (blockBytes w)
  rw [h3] at hq
  generalize hqd : (d.length - blockBytes w) / blockBytes w = q at hq h4
  have hd0 : d.length / blockBytes w = q + 1 := by
    rw [show d.length = blockBytes w * (q + 1) by rw [Nat.mul_succ]; omega,
      Nat.mul_div_cancel_left _ hbb]
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_, by simp [bytesAt]⟩
  · rw [Nat.sub_zero, show d.length = blockBytes w * (q + 1) by rw [Nat.mul_succ]; omega,
      Nat.mul_mod_right]
  · rw [Nat.sub_zero, hd0, VG.Proof.Blake2.compressList_succ, hs, h4]
    refine VG.Proof.Blake2.F_congr P ?_ ?_
    · apply VG.Proof.Blake2.parseBlock_congr
      intro k hk
      have := congrArg (fun l => l.getD k 0) h5
      simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
        Option.map_some, Option.getD_some, List.getElem?_drop] at this
      rw [this, show d.length - blockBytes w + k = blockBytes w * q + k by omega]
      simp [List.getD_eq_getElem?_getD]
    · rw [Nat.succ_mul, Nat.mul_comm q]; omega

theorem bytesAt_getD (mem : Mem) (q : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt mem q n).getD i 0 = mem (q + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- The blocks after `bb · n` bytes of data `d` are those at `q`. -/
theorem compressList_bytes (h : HashValue w) {d : List Byte} {n : Nat}
    (hd : d.length = blockBytes w * n) (mem : Mem) (q : Addr) {K k : Nat} (hk : k ≤ K) :
    compressList P h (d ++ bytesAt mem q (blockBytes w * K)) (n + k) =
      compressBlocks P (compressList P h d n) mem q k (d.length + blockBytes w) false := by
  induction k with
  | zero => rw [Nat.add_zero, VG.Proof.Blake2.compressList_append P h _ (by omega), VG.Proof.Blake2.compressBlocks_zero]
  | succ k ih =>
    rw [← Nat.add_assoc, VG.Proof.Blake2.compressList_succ, VG.Proof.Blake2.compressBlocks_succ, ih (by omega)]
    refine VG.Proof.Blake2.F_congr P ?_ ?_
    · apply VG.Proof.Blake2.parseBlock_congr
      intro j hj
      have hkK : blockBytes w * k + j < blockBytes w * K := by
        have h1 : blockBytes w * (k + 1) ≤ blockBytes w * K := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_succ] at h1; omega
      rw [VG.Proof.Blake2.getD_append_right (by rw [hd, Nat.mul_add]; omega),
        show blockBytes w * (n + k) + j - d.length = blockBytes w * k + j by rw [hd, Nat.mul_add]; omega,
        VG.Proof.Blake2.bytesAt_getD _ _ hkK, BitVec.ofNat_add, BitVec.add_assoc]
    · rw [hd, Nat.mul_comm (blockBytes w) n, Nat.succ_mul, Nat.add_mul]; omega

/-- Compressing `k` whole blocks straight from the data (at `q`), with an
empty buffer: the first one's counter is `|d| + bb`. -/
theorem reprR_blocks (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem mem' : Mem} {p q : Addr}
    {d : List Byte} {k : Nat} (h : VG.Proof.Blake2.ReprR P h0 mem p d 0)
    (hs : stateAt w mem' p =
      compressBlocks P (stateAt w mem p) mem q k (d.length + blockBytes w) false) :
    VG.Proof.Blake2.ReprR P h0 mem' p (d ++ bytesAt mem q (blockBytes w * k)) 0 := by
  obtain ⟨_, _, h3, h4, _⟩ := h
  rw [Nat.sub_zero] at h3 h4
  have hn := Nat.div_add_mod d.length (blockBytes w)
  rw [h3, Nat.add_zero] at hn
  have hl : (d ++ bytesAt mem q (blockBytes w * k)).length = blockBytes w * (d.length / blockBytes w + k) := by
    simp only [List.length_append, bytesAt, List.length_map, List.length_range, Nat.mul_add]; omega
  refine ⟨Nat.zero_le _, Nat.zero_le _, by rw [Nat.sub_zero, hl, Nat.mul_mod_right], ?_,
    by simp [bytesAt]⟩
  rw [Nat.sub_zero, hl, Nat.mul_div_cancel_left _ hbb, hs, h4,
    VG.Proof.Blake2.compressList_bytes P h0 hn.symm mem q (Nat.le_refl k)]

theorem compressList_zero (h : HashValue w) (d : List Byte) : compressList P h d 0 = h := by
  simp only [compressList, List.range_zero, List.foldl_nil]

/-! ## `init` -/

theorem padZeros_eq {key : List Byte} (h0 : key.length ≠ 0) (h : key.length ≤ blockBytes w) :
    padZeros w key = key ++ List.replicate (blockBytes w - key.length) 0 := by
  unfold padZeros
  congr 2
  by_cases e : key.length = blockBytes w
  · rw [e, Nat.mod_self, Nat.sub_zero, Nat.mod_self, Nat.sub_self]
  · rw [Nat.mod_eq_of_lt (show key.length < blockBytes w by omega),
      Nat.mod_eq_of_lt (show blockBytes w - key.length < blockBytes w by omega)]

/-- The state `init` writes: the initial hash value and, for a key, the key
padded with zeros in the buffer. -/
theorem repr_keyBlock (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem : Mem} {p : Addr}
    {key : List Byte} (hk : key.length ≤ blockBytes w) (hs : stateAt w mem p = h0)
    (hb : key.length ≠ 0 → bytesAt mem (p + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w)) (blockBytes w) =
      key ++ List.replicate (blockBytes w - key.length) 0) :
    Spec.Blake2.Repr P h0 mem p (keyBlock w key) := by
  rw [VG.Proof.Blake2.repr_iff P hbb]
  unfold keyBlock
  split
  · simp only [List.length_nil, show VG.Proof.Blake2.bufLen w 0 = 0 from rfl]
    exact ⟨Nat.zero_le _, Nat.le_refl _, Nat.zero_mod _, by
      rw [List.length_nil, Nat.zero_div, VG.Proof.Blake2.compressList_zero, hs], by simp [bytesAt]⟩
  · rename_i h0'
    rw [VG.Proof.Blake2.padZeros_eq h0' hk]
    have hl : (key ++ List.replicate (blockBytes w - key.length) 0).length = blockBytes w := by
      simp; omega
    have hbl : VG.Proof.Blake2.bufLen w (blockBytes w) = blockBytes w := by
      simp only [VG.Proof.Blake2.bufLen, Nat.ne_of_gt hbb, ite_false, Nat.mod_eq_of_lt (show blockBytes w - 1 < blockBytes w by omega)]
      omega
    rw [hl, hbl]
    refine ⟨Nat.le_refl _, by rw [hl], by rw [hl, Nat.sub_self, Nat.zero_mod], ?_, ?_⟩ <;>
      rw [hl, Nat.sub_self]
    exacts [
      by rw [Nat.zero_div, VG.Proof.Blake2.compressList_zero, hs], by rw [List.drop_zero, hb h0']]

/-! ## `finalize` -/

/-- The last block, padded with zeros, compressed with the final block flag
and the counter `|d|`, gives the final hash. -/
theorem final_eq (hbb : 0 < blockBytes w) {h0 : HashValue w} {mem mem' : Mem} {p : Addr}
    {d : List Byte} (h : Spec.Blake2.Repr P h0 mem p d) (hs : stateAt w mem' p = stateAt w mem p)
    (hb : bytesAt mem' (p + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w)) (blockBytes w) =
      bytesAt mem (p + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w)) (VG.Proof.Blake2.bufLen w d.length) ++
        List.replicate (blockBytes w - VG.Proof.Blake2.bufLen w d.length) 0) :
    (F P (stateAt w mem' p) (blockAt w mem' (p + BitVec.ofNat 64 (VG.Proof.Blake2.bufOff w))) d.length true).toList.flatMap
      wordBytes = finalHash P h0 d := by
  obtain ⟨-, -, -, h4, h5⟩ := (VG.Proof.Blake2.repr_iff P hbb h0 mem p d).mp h
  have e := VG.Proof.Blake2.sub_bufLen (w := w) d
  have hr := VG.Proof.Blake2.bufLen_le hbb d.length
  have e' : (d.length - VG.Proof.Blake2.bufLen w d.length) / blockBytes w = compressed w d := by
    rw [e, Nat.mul_div_cancel_left _ hbb]
  rw [e'] at h4
  rw [e] at h5
  have e2 : d.length - blockBytes w * compressed w d = VG.Proof.Blake2.bufLen w d.length := by
    have := VG.Proof.Blake2.bufLen_le_self (w := w) d.length; omega
  unfold finalHash
  rw [hs, h4]
  refine congrArg (fun h : HashValue w => h.toList.flatMap wordBytes) (VG.Proof.Blake2.F_congr P ?_ rfl)
  apply VG.Proof.Blake2.parseBlock_congr
  intro k hk
  have := congrArg (fun l => l.getD k 0) hb
  simp only [VG.Proof.Blake2.bytesAt_getD _ _ hk] at this
  rw [this, h5]
  by_cases hkr : k < VG.Proof.Blake2.bufLen w d.length
  · rw [VG.Proof.Blake2.getD_append_left (by simp only [List.length_drop, e2]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  · rw [VG.Proof.Blake2.getD_append_right (by simp only [List.length_drop, e2]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    rw [List.getElem?_eq_none (by omega)]
    split <;> rfl

/-! ## Memory -/

theorem stateAt_congr {mem mem' : Mem} {p : Addr}
    (h : ∀ i < VG.Proof.Blake2.bufOff w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    stateAt w mem' p = stateAt w mem p := by
  simp only [stateAt]
  congr 1; funext j
  apply Mem.readW_congr
  intro i hi
  have : w / 8 * j.1 ≤ w / 8 * 7 := Nat.mul_le_mul_left _ (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by simp only [VG.Proof.Blake2.bufOff]; omega)

theorem blockAt_congr {mem mem' : Mem} {p : Addr}
    (h : ∀ k < blockBytes w, mem' (p + BitVec.ofNat 64 k) = mem (p + BitVec.ofNat 64 k)) :
    blockAt w mem' p = blockAt w mem p :=
  VG.Proof.Blake2.parseBlock_congr h

theorem compressBlocks_congr {h : HashValue w} {m m' : Mem} {p : Addr} {n t : Nat} {f : Bool}
    (hm : ∀ j < blockBytes w * n, m' (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j)) :
    compressBlocks P h m' p n t f = compressBlocks P h m p n t f := by
  induction n with
  | zero => rw [VG.Proof.Blake2.compressBlocks_zero, VG.Proof.Blake2.compressBlocks_zero]
  | succ n ih =>
    rw [VG.Proof.Blake2.compressBlocks_succ, VG.Proof.Blake2.compressBlocks_succ,
      ih fun j hj => hm j (by rw [Nat.mul_succ]; omega)]
    refine VG.Proof.Blake2.F_congr P (VG.Proof.Blake2.blockAt_congr fun k hk => ?_) rfl
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hm _ (by rw [Nat.mul_succ]; omega)

theorem bytesAt_congr {mem mem' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    bytesAt mem' p n = bytesAt mem p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-! ## Bytes and words -/

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem wordBytes_readW (m : Mem) (a : Addr) (hw : w = 32 ∨ w = 64) :
    wordBytes (m.readW a w) = bytesAt m a (w / 8) := by
  apply List.ext_getElem (by simp [wordBytes, bytesAt])
  intro i h1 _
  simp only [wordBytes, List.length_map, List.length_range] at h1
  simp only [wordBytes, bytesAt, List.getElem_map, List.getElem_range]
  rw [← Mem.extractLsb'_read m a h1]
  rcases hw with rfl | rfl <;> rfl

theorem bytesAt_words (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (w / 8 * n) =
      (List.range n).flatMap fun j => bytesAt m (p + BitVec.ofNat 64 (w / 8 * j)) (w / 8) := by
  induction n with
  | zero => simp [bytesAt]
  | succ n ih => rw [Nat.mul_succ, VG.Proof.Blake2.bytesAt_add, ih, List.range_succ, List.flatMap_append]; simp

/-- The bytes of a stored state. -/
theorem bytesAt_state (m : Mem) (p : Addr) (hw : w = 32 ∨ w = 64) :
    bytesAt m p (VG.Proof.Blake2.bufOff w) = (stateAt w m p).toList.flatMap wordBytes := by
  rw [VG.Proof.Blake2.bufOff, Nat.mul_comm, VG.Proof.Blake2.bytesAt_words, stateAt, Vector.toList_ofFn, List.flatMap,
    List.flatMap, List.map_ofFn, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, Function.comp_apply,
    Fin.val_succ, Fin.val_zero, Nat.reduceAdd, VG.Proof.Blake2.wordBytes_readW m _ hw]

end

end VG.Proof.Blake2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Scratch`. -/
section

/-!
# BLAKE2's streaming postconditions read memory only within the buffers

`update` and `finalize` keep their working space in a frame of their own
(`Verified.stackScratch`); on x86 and ARMv7, where the frame also holds a
copy of the arguments passed on the stack, that needs their postconditions to
read the memory on entry only within the function's buffers: the streaming
state (`repr_congr`) and the data (`bytesAt_congr`).
-/

namespace VG.Proof.Blake2

open VG.Spec.Blake2

/-- `Repr` only depends on the state's bytes: the hash state and the buffered
last block. -/
theorem repr_congr' {w : Nat} (hw : 8 ≤ w) {P : VG.Spec.Blake2.Params w} {h0 : HashValue w} {mem mem' : Mem}
    {p : Addr} {d : List Byte}
    (h : ∀ i < VG.Proof.Blake2.bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : Repr P h0 mem p d) : Repr P h0 mem' p d := by
  refine ⟨by rw [VG.Proof.Blake2.stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply VG.Proof.Blake2.bytesAt_congr
  intro i hi
  have hb : d.length - blockBytes w * compressed w d ≤ blockBytes w := by
    simp only [compressed]
    have := Nat.div_add_mod (d.length - 1) (blockBytes w)
    have := Nat.mod_lt (d.length - 1) (show 0 < blockBytes w by simp only [blockBytes]; omega)
    omega
  have := h (VG.Proof.Blake2.bufOff w + i) (by omega)
  rwa [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem updateBPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (updateBSig.words pb).length →
    (∀ b ∈ Sig.bufs updateBSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateBSig.words pb) (updateBPost pb) vs m₁ m' r →
      Curry.apply (updateBSig.words pb) (updateBPost pb) vs m₂ m' r
  | [st, ct, dt, ln], m₁, m₂, m', r, _, hb, h => by
    simp only [updateBSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    have hd : ∀ i < (ln.setWidth pb).toNat, m₂ (dt + BitVec.ofNat 64 i) = m₁ (dt + BitVec.ofNat 64 i) :=
      fun i hi => by
        have := Nat.mod_le ln.toNat (2 ^ pb)
        have := ln.isLt
        rw [BitVec.toNat_setWidth] at hi
        exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro h0 d hr hc hl
    rw [show bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int pb).ofRaw ln).toNat =
      bytesAt m₁ dt (ln.setWidth pb).toNat from VG.Proof.Blake2.bytesAt_congr hd]
    exact h h0 d (VG.Proof.Blake2.repr_congr' (by decide)
      (fun i hi => (hs i (by simp only [VG.Proof.Blake2.bufOff, blockBytes] at hi; omega)).symm) hr) hc hl

theorem finalizeBPost_local (pb : Nat) :
    ∀ vs m₁ m₂ m' r, vs.length = (finalizeBSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeBSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeBSig.words pb) (finalizeBPost pb) vs m₁ m' r →
        Curry.apply (finalizeBSig.words pb) (finalizeBPost pb) vs m₂ m' r
  | [st, ct, ot], m₁, m₂, m', r, _, hb, h => by
    simp only [finalizeBSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 192, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro h0 d hr hl hc
    exact h h0 d (VG.Proof.Blake2.repr_congr' (by decide)
      (fun i hi => (hs i (by simp only [VG.Proof.Blake2.bufOff, blockBytes] at hi; omega)).symm) hr) hl hc

theorem updateSPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (updateSSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSSig.words pb) (updateSPost pb) vs m₁ m' r →
      Curry.apply (updateSSig.words pb) (updateSPost pb) vs m₂ m' r
  | [st, ct, dt, ln], m₁, m₂, m', r, _, hb, h => by
    simp only [updateSSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    have hd : ∀ i < (ln.setWidth pb).toNat, m₂ (dt + BitVec.ofNat 64 i) = m₁ (dt + BitVec.ofNat 64 i) :=
      fun i hi => by
        have := Nat.mod_le ln.toNat (2 ^ pb)
        have := ln.isLt
        rw [BitVec.toNat_setWidth] at hi
        exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro h0 d hr hc hl
    rw [show bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int pb).ofRaw ln).toNat =
      bytesAt m₁ dt (ln.setWidth pb).toNat from VG.Proof.Blake2.bytesAt_congr hd]
    exact h h0 d (VG.Proof.Blake2.repr_congr' (by decide)
      (fun i hi => (hs i (by simp only [VG.Proof.Blake2.bufOff, blockBytes] at hi; omega)).symm) hr) hc hl

theorem finalizeSPost_local (pb : Nat) :
    ∀ vs m₁ m₂ m' r, vs.length = (finalizeSSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeSSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeSSig.words pb) (finalizeSPost pb) vs m₁ m' r →
        Curry.apply (finalizeSSig.words pb) (finalizeSPost pb) vs m₂ m' r
  | [st, ct, ot], m₁, m₂, m', r, _, hb, h => by
    simp only [finalizeSSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro h0 d hr hl hc
    exact h h0 d (VG.Proof.Blake2.repr_congr' (by decide)
      (fun i hi => (hs i (by simp only [VG.Proof.Blake2.bufOff, blockBytes] at hi; omega)).symm) hr) hl hc

end VG.Proof.Blake2

end
