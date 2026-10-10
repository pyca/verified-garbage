import VerifiedGarbage.Spec.Cast5
import VerifiedGarbage.Impl.Cast5.Lines
import VerifiedGarbage.Proof.Cast5.Memory

/-!
# CAST5 key schedule: the lines as the implementations compute them

The implementations keep `x0 … xF` and `z0 … zF` as bytes (here functions
`Nat → Byte`, `XZ`), compute a line's value with the XORs in their own
order (`lineVal`), and store it big-endian into a quadruple (`putQuad`) or
as a subkey. Each group of four lines of §2.4 is the spec's (`zOfX_eq`,
`xOfZ_eq`, `keysA_eq`, …).
-/

namespace VG.Proof.Cast5

open VG.Spec.Cast5 VG.Impl.Cast5

/-- The arrays `x` and `z`. -/
structure XZ where
  x : Nat → Byte
  z : Nat → Byte

/-- A byte of `x` or `z`. -/
def XZ.get (s : XZ) : Pos → Byte
  | (.x, i) => s.x i
  | (.z, i) => s.z i

/-- An array. -/
def XZ.arr (s : XZ) : Arr → Nat → Byte
  | .x => s.x
  | .z => s.z

/-- S-box `e` (5–8). -/
def sbox : Nat → Byte → Word
  | 5 => S5
  | 6 => S6
  | 7 => S7
  | _ => S8

/-- Quadruple `q` of `f`, the first byte most significant. -/
def quadOf (f : Nat → Byte) (q : Nat) : Word :=
  f (4 * q) ++ f (4 * q + 1) ++ f (4 * q + 2) ++ f (4 * q + 3)

/-- `f` with quadruple `q` replaced by `w`, big-endian. -/
def putQuad (f : Nat → Byte) (q : Nat) (w : Word) : Nat → Byte := fun i =>
  if i / 4 = q then (w >>> (8 * (3 - i % 4))).setWidth 8 else f i

/-- The value of a line, its XORs in the implementations' order:
`S8[d] ^ S7[c] ^ S6[b] ^ S5[a] ^ Sₑ[f]`, then the quadruple. -/
def lineVal (s : XZ) (l : Line) : Word :=
  let v := S8 (s.get l.main.2.2.2) ^^^ S7 (s.get l.main.2.2.1) ^^^ S6 (s.get l.main.2.1) ^^^
    S5 (s.get l.main.1) ^^^ sbox l.extra.1 (s.get l.extra.2)
  match l.word with
  | some (a, q) => v ^^^ quadOf (s.arr a) q
  | none => v

/-- The four lines of `ls`, each storing into quadruple `k` of `z`. -/
def runZ (ls : List Line) (s : XZ) : XZ :=
  (List.range 4).foldl (fun s k => { s with z := putQuad s.z k (lineVal s (ls.getD k default)) }) s

/-- The four lines of `ls`, each storing into quadruple `k` of `x`. -/
def runX (ls : List Line) (s : XZ) : XZ :=
  (List.range 4).foldl (fun s k => { s with x := putQuad s.x k (lineVal s (ls.getD k default)) }) s

/-- The array as the spec's vector. -/
def vec (f : Nat → Byte) : Key16 := Vector.ofFn fun i => f i.val

theorem vec_get (f : Nat → Byte) {i : Nat} (h : i < 16) : (vec f)[i] = f i := by
  simp [vec]

theorem quad_vec (f : Nat → Byte) {q : Nat} (hq : q < 4) : quad (vec f) q = quadOf f q := by
  rw [quad, quadOf, vec, getD_ofFn _ (by omega), getD_ofFn _ (by omega), getD_ofFn _ (by omega),
    getD_ofFn _ (by omega)]

theorem setQuad_vec (f : Nat → Byte) (q : Nat) (w : Word) : setQuad (vec f) q w = vec (putQuad f q w) := by
  apply Vector.ext
  intro i hi
  simp [setQuad, vec, putQuad]

/-- XORs reordered. -/
theorem xor6 (w a b c d e : Word) :
    w ^^^ a ^^^ b ^^^ c ^^^ d ^^^ e = d ^^^ c ^^^ b ^^^ a ^^^ e ^^^ w := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases w.getLsbD i <;> cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;>
    cases d.getLsbD i <;> cases e.getLsbD i <;> rfl

theorem xor5 (a b c d e : Word) : a ^^^ b ^^^ c ^^^ d ^^^ e = d ^^^ c ^^^ b ^^^ a ^^^ e := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;>
    cases e.getLsbD i <;> rfl

theorem getElem_setQuad (v : Key16) (q : Nat) (w : Word) {i : Nat} (hi : i < 16) :
    (setQuad v q w)[i] = if i / 4 = q then (w >>> (8 * (3 - i % 4))).setWidth 8 else v[i] := by
  simp [setQuad]

/-- A quadruple stored both ways keeps the arrays equal below it. -/
theorem setQuad_step {Z : Key16} {zf : Nat → Byte} {k : Nat}
    (hZ : ∀ i (h : i < 16), i < 4 * k → Z[i] = zf i) {v w : Word} (hvw : v = w) :
    ∀ i (h : i < 16), i < 4 * (k + 1) → (setQuad Z k v)[i] = putQuad zf k w i := by
  intro i h hk'
  rw [getElem_setQuad _ _ _ h, putQuad, hvw]
  by_cases hq : i / 4 = k
  · rw [ite_eq_left hq, ite_eq_left hq]
  · rw [ite_eq_right hq, ite_eq_right hq]
    exact hZ i h (by omega)

/-- Four lines run in sequence, each storing quadruple `k`, compute the same
whether on the spec's vectors or on functions, if each line does
(`e k`, `f k`) from equal bytes of the quadruples before it. -/
theorem run4 (R : Key16) (zf0 : Nat → Byte) (e : Nat → Key16 → Word) (f : Nat → (Nat → Byte) → Word)
    (he : ∀ k < 4, ∀ (Z : Key16) (zf : Nat → Byte), (∀ i (h : i < 16), i < 4 * k → Z[i] = zf i) →
      e k Z = f k zf) :
    setQuad (setQuad (setQuad (setQuad R 0 (e 0 R)) 1 (e 1 (setQuad R 0 (e 0 R)))) 2
      (e 2 (setQuad (setQuad R 0 (e 0 R)) 1 (e 1 (setQuad R 0 (e 0 R)))))) 3
      (e 3 (setQuad (setQuad (setQuad R 0 (e 0 R)) 1 (e 1 (setQuad R 0 (e 0 R)))) 2
        (e 2 (setQuad (setQuad R 0 (e 0 R)) 1 (e 1 (setQuad R 0 (e 0 R))))))) =
    vec (putQuad (putQuad (putQuad (putQuad zf0 0 (f 0 zf0)) 1 (f 1 (putQuad zf0 0 (f 0 zf0)))) 2
      (f 2 (putQuad (putQuad zf0 0 (f 0 zf0)) 1 (f 1 (putQuad zf0 0 (f 0 zf0)))))) 3
      (f 3 (putQuad (putQuad (putQuad zf0 0 (f 0 zf0)) 1 (f 1 (putQuad zf0 0 (f 0 zf0)))) 2
        (f 2 (putQuad (putQuad zf0 0 (f 0 zf0)) 1 (f 1 (putQuad zf0 0 (f 0 zf0)))))))) := by
  have c0 : ∀ i (h : i < 16), i < 4 * 0 → R[i] = zf0 i := fun i _ h => absurd h (by omega)
  have c1 := setQuad_step c0 (he 0 (by decide) _ _ c0)
  have c2 := setQuad_step c1 (he 1 (by decide) _ _ c1)
  have c3 := setQuad_step c2 (he 2 (by decide) _ _ c2)
  have c4 := setQuad_step c3 (he 3 (by decide) _ _ c3)
  apply Vector.ext
  intro i hi
  rw [c4 i hi (by omega)]
  simp [vec]

/-- The lines of `zOfX`, as the spec writes them. -/
def eZ (x : Key16) : Nat → Key16 → Word := fun k z =>
  match k with
  | 0 => quad x 0 ^^^ S5 x[0xD] ^^^ S6 x[0xF] ^^^ S7 x[0xC] ^^^ S8 x[0xE] ^^^ S7 x[0x8]
  | 1 => quad x 2 ^^^ S5 z[0x0] ^^^ S6 z[0x2] ^^^ S7 z[0x1] ^^^ S8 z[0x3] ^^^ S8 x[0xA]
  | 2 => quad x 3 ^^^ S5 z[0x7] ^^^ S6 z[0x6] ^^^ S7 z[0x5] ^^^ S8 z[0x4] ^^^ S5 x[0x9]
  | _ => quad x 1 ^^^ S5 z[0xA] ^^^ S6 z[0x9] ^^^ S7 z[0xB] ^^^ S8 z[0x8] ^^^ S6 x[0xB]

/-- The lines of `xOfZ`, as the spec writes them. -/
def eX (z : Key16) : Nat → Key16 → Word := fun k x =>
  match k with
  | 0 => quad z 2 ^^^ S5 z[0x5] ^^^ S6 z[0x7] ^^^ S7 z[0x4] ^^^ S8 z[0x6] ^^^ S7 z[0x0]
  | 1 => quad z 0 ^^^ S5 x[0x0] ^^^ S6 x[0x2] ^^^ S7 x[0x1] ^^^ S8 x[0x3] ^^^ S8 z[0x2]
  | 2 => quad z 1 ^^^ S5 x[0x7] ^^^ S6 x[0x6] ^^^ S7 x[0x5] ^^^ S8 x[0x4] ^^^ S5 z[0x1]
  | _ => quad z 3 ^^^ S5 x[0xA] ^^^ S6 x[0x9] ^^^ S7 x[0xB] ^^^ S8 x[0x8] ^^^ S6 z[0x3]

theorem zOfX_eq (s : XZ) : zOfX (vec s.x) = vec (runZ zLines s).z :=
  run4 (Vector.replicate 16 0) s.z (eZ (vec s.x)) (fun k zf => lineVal ⟨s.x, zf⟩ (zLines.getD k default))
    (by
      intro k hk Z zf hZ
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      · simp (disch := decide) only [eZ, zLines, List.getD_cons_succ, List.getD_cons_zero, lineVal, XZ.get,
          XZ.arr, sbox, Impl.Cast5.x, Impl.Cast5.z, quad_vec, vec_get, hZ]
        exact xor6 _ _ _ _ _ _)

theorem xOfZ_eq (s : XZ) : xOfZ (vec s.z) = vec (runX xLines s).x :=
  run4 (Vector.replicate 16 0) s.x (eX (vec s.z)) (fun k xf => lineVal ⟨xf, s.z⟩ (xLines.getD k default))
    (by
      intro k hk X xf hX
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      · simp (disch := decide) only [eX, xLines, List.getD_cons_succ, List.getD_cons_zero, lineVal, XZ.get,
          XZ.arr, sbox, Impl.Cast5.x, Impl.Cast5.z, quad_vec, vec_get, hX]
        exact xor6 _ _ _ _ _ _)

/-- The four subkeys of a group of lines. -/
def keys4 (ls : List Line) (s : XZ) : List Word :=
  [lineVal s (ls.getD 0 default), lineVal s (ls.getD 1 default), lineVal s (ls.getD 2 default),
    lineVal s (ls.getD 3 default)]

theorem keysA_eq (s : XZ) : keysA (vec s.z) = keys4 aLines s := by
  simp (disch := decide) only [keysA, keys4, aLines, List.getD_cons_succ, List.getD_cons_zero, lineVal,
    XZ.get, sbox, Impl.Cast5.z, vec_get]
  exact congr (congrArg _ (xor5 ..)) <| congr (congrArg _ (xor5 ..)) <|
    congr (congrArg _ (xor5 ..)) <| congr (congrArg _ (xor5 ..)) rfl

theorem keysB_eq (s : XZ) : keysB (vec s.x) = keys4 bLines s := by
  simp (disch := decide) only [keysB, keys4, bLines, List.getD_cons_succ, List.getD_cons_zero, lineVal,
    XZ.get, sbox, Impl.Cast5.x, vec_get]
  exact congr (congrArg _ (xor5 ..)) <| congr (congrArg _ (xor5 ..)) <|
    congr (congrArg _ (xor5 ..)) <| congr (congrArg _ (xor5 ..)) rfl

theorem keysC_eq (s : XZ) : keysC (vec s.z) = keys4 cLines s := by
  simp (disch := decide) only [keysC, keys4, cLines, List.getD_cons_succ, List.getD_cons_zero, lineVal,
    XZ.get, sbox, Impl.Cast5.z, vec_get]
  exact congr (congrArg _ (xor5 ..)) <| congr (congrArg _ (xor5 ..)) <|
    congr (congrArg _ (xor5 ..)) <| congr (congrArg _ (xor5 ..)) rfl

theorem keysD_eq (s : XZ) : keysD (vec s.x) = keys4 dLines s := by
  simp (disch := decide) only [keysD, keys4, dLines, List.getD_cons_succ, List.getD_cons_zero, lineVal,
    XZ.get, sbox, Impl.Cast5.x, vec_get]
  exact congr (congrArg _ (xor5 ..)) <| congr (congrArg _ (xor5 ..)) <|
    congr (congrArg _ (xor5 ..)) <| congr (congrArg _ (xor5 ..)) rfl

/-- One half of §2.4 as the implementations run it: the subkeys and the
arrays it leaves. -/
def halfImpl (s : XZ) : List Word × XZ :=
  let s1 := runZ zLines s
  let s2 := runX xLines s1
  let s3 := runZ zLines s2
  let s4 := runX xLines s3
  (keys4 aLines s1 ++ keys4 bLines s2 ++ keys4 cLines s3 ++ keys4 dLines s4, s4)

theorem half_eq (s : XZ) : half (vec s.x) = ((halfImpl s).1, vec (halfImpl s).2.x) := by
  simp only [half, halfImpl]
  rw [zOfX_eq, keysA_eq, xOfZ_eq, keysB_eq, zOfX_eq, keysC_eq, xOfZ_eq, keysD_eq]

/-- The key schedule as the implementations run it, from the padded key `x`
(and any `z`). -/
theorem expandKey_eq (key : List Byte) (z : Nat → Byte) :
    expandKey key =
      Vector.ofFn fun i => ((halfImpl ⟨fun j => key.getD j 0, z⟩).1 ++
        (halfImpl (halfImpl ⟨fun j => key.getD j 0, z⟩).2).1).getD i.val 0 := by
  have h1 := half_eq ⟨fun j => key.getD j 0, z⟩
  have h2 := half_eq (halfImpl ⟨fun j => key.getD j 0, z⟩).2
  simp only [expandKey]
  rw [show (Vector.ofFn fun i : Fin 16 => key.getD i.val 0) = vec fun j => key.getD j 0 from rfl, h1]
  simp only
  rw [h2]

end VG.Proof.Cast5
