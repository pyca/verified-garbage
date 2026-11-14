module

public import VerifiedGarbage.Spec.Cast5
public import VerifiedGarbage.Impl.Cast5.Lines
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Cast5.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.InstancePriority

/-! ### `Cast5.KeyLines`, which only this module used -/

section

/-!
# CAST5 key schedule: the lines as the implementations compute them

The implementations keep `x0 … xF` and `z0 … zF` as bytes (here functions
`Nat → Byte`, `XZ`), compute a line's value with the XORs in their own
order (`lineVal`), and store it big-endian into a quadruple (`putQuad`) or
as a subkey. Each group of four lines of §2.4 is the spec's (`zOfX_eq`,
`xOfZ_eq`, `keysA_eq`, …).
-/

@[expose] public section

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
  rw [quad, quadOf, vec, getD_ofFn _ (by omega_using [hq]), getD_ofFn _ (by omega_using [hq]), getD_ofFn _ (by omega_using [hq]),
    getD_ofFn _ (by omega_using [hq])]

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
    exact hZ i h (by omega_using [hk', hq])

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
  have c0 : ∀ i (h : i < 16), i < 4 * 0 → R[i] = zf0 i := fun i _ h => absurd h (by omega_using [])
  have c1 := setQuad_step c0 (he 0 (by decide) _ _ c0)
  have c2 := setQuad_step c1 (he 1 (by decide) _ _ c1)
  have c3 := setQuad_step c2 (he 2 (by decide) _ _ c2)
  have c4 := setQuad_step c3 (he 3 (by decide) _ _ c3)
  apply Vector.ext
  intro i hi
  rw [c4 i hi (by omega_using [hi])]
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
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
      · simp (disch := decide) only [eZ, zLines, List.getD_cons_succ, List.getD_cons_zero, lineVal, XZ.get,
          XZ.arr, sbox, Impl.Cast5.x, Impl.Cast5.z, quad_vec, vec_get, hZ]
        exact xor6 _ _ _ _ _ _)

theorem xOfZ_eq (s : XZ) : xOfZ (vec s.z) = vec (runX xLines s).x :=
  run4 (Vector.replicate 16 0) s.x (eX (vec s.z)) (fun k xf => lineVal ⟨xf, s.z⟩ (xLines.getD k default))
    (by
      intro k hk X xf hX
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
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

end

end


/-!
# CAST5 key expansion: the working space and the subkeys

The implementations keep `x` and `z` in the working space at `c`, a byte each
(`HoldsXZ`), and write the subkeys so far to `K` (`Keys`); each write of key
expansion keeps what it does not overwrite (`KMem`). A group of lines stores
into `x` or `z` (`runQ`) or appends subkeys (`keys4`), and the halves of §2.4
make the schedule (`halves`, `scheduleAt_keys`).
-/

@[expose] public section

namespace VG.Proof.Cast5

open VG VG.Impl.Cast5

/-- A byte after a write at an offset of the same base. -/
theorem byte_write (m : Mem) (c : Addr) {d e n : Nat} (v : BitVec (8 * n)) (hd : d + n ≤ 2 ^ 63)
    (he : e < 2 ^ 63) :
    (m.write (c + BitVec.ofNat 64 d) n v) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + n then v.extractLsb' (8 * (e - d)) 8 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.write]
  rw [Offset.sub_toNat' c (by omega_using [hd]) (by omega_using [he])]
  by_cases h : d ≤ e
  · rw [ite_eq_left h]
    by_cases h2 : e < d + n
    · rw [ite_eq_left (by omega_using [h, h2]), ite_eq_left ⟨h, h2⟩]
    · rw [ite_eq_right (by omega_using [h2]), ite_eq_right (by omega_using [h2])]
  · rw [ite_eq_right h, ite_eq_right (by omega_using [hd]), ite_eq_right (by omega_using [h])]

/-- A byte outside a write. -/
theorem byte_writeW_sep (m : Mem) (c : Addr) {d e w : Nat} (v : BitVec w) (hd : d + w / 8 ≤ 2 ^ 63)
    (he : e < 2 ^ 63) (h : e < d ∨ d + w / 8 ≤ e) :
    (m.writeW (c + BitVec.ofNat 64 d) v) (c + BitVec.ofNat 64 e) = m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he, ite_eq_right (by omega_using [h])]

/-- `[p + e, p + e + k)` and `[p, p + n)` are separate if `n ≤ e`. -/
theorem sep_base' (p : Addr) {n e k : Nat} (h : n ≤ e) (he : e + k ≤ 2 ^ 64) :
    Mem.Sep (p + BitVec.ofNat 64 e) k p n :=
  fun x h₁ h₂ => Offset.sep_base p h he x h₂ h₁

theorem off_lt (a : Arr) : off a + 16 ≤ 48 := by cases a <;> decide
theorem off_ge (a : Arr) : 16 ≤ off a := by cases a <;> decide

/-- The working space at `p` holds the arrays of `st`, a byte each. -/
def HoldsXZ (m : Mem) (p : Addr) (st : XZ) : Prop :=
  ∀ a i, i < 16 → m (p + BitVec.ofNat 64 (off a + i)) = st.arr a i

theorem HoldsXZ.pos {m : Mem} {p : Addr} {st : XZ} (h : HoldsXZ m p st) {q : Pos} (hq : q.2 < 16) :
    m (p + BitVec.ofNat 64 (srcOff q)) = st.get q := by
  obtain ⟨a, i⟩ := q
  cases a <;> exact h _ i hq

theorem HoldsXZ.quad {m : Mem} {p : Addr} {st : XZ} (h : HoldsXZ m p st) (a : Arr) {q : Nat} (hq : q < 4) :
    byteRev32 (m.readW (p + BitVec.ofNat 64 (off a + 4 * q)) 32) = quadOf (st.arr a) q := by
  have e1 : (1 : Addr) = BitVec.ofNat 64 1 := rfl
  rw [byteRev32_readW, e1, Proof.Cast5.add_ofNat_add, Proof.Cast5.add_ofNat_add,
    Proof.Cast5.add_ofNat_add, quadOf, show off a + 4 * q + 1 + 1 + 1 = off a + (4 * q + 3) by omega_using [],
    show off a + 4 * q + 1 + 1 = off a + (4 * q + 2) by omega_using [],
    show off a + 4 * q + 1 = off a + (4 * q + 1) by omega_using [], h a _ (by omega_using [hq]), h a _ (by omega_using [hq]),
    h a _ (by omega_using [hq]), h a _ (by omega_using [hq])]

/-- What `line_ok` needs of a line: its bytes are in `x` and `z`, its extra
S-box one of S5–S8, its quadruple one of four. -/
def lineOk (l : Impl.Cast5.Line) : Bool :=
  l.main.1.2 < 16 && l.main.2.1.2 < 16 && l.main.2.2.1.2 < 16 && l.main.2.2.2.2 < 16 &&
    5 ≤ l.extra.1 && l.extra.1 ≤ 8 &&
    (match l.word with | some (_, q) => q < 4 | none => true)

/-- The subkeys `ws`, little-endian words, at `K`. -/
def Keys (m : Mem) (K : Addr) (ws : List Spec.Cast5.Word) : Prop :=
  ∀ i < ws.length, m.readW (K + BitVec.ofNat 64 (4 * i)) 32 = ws.getD i 0

/-- The memory of key expansion from `m0`: `x` and `z` at `c`, the subkeys
`ws` at `K`, and nothing else written but the working space's first 64 bytes
and the schedule. -/
structure KMem (m0 m : Mem) (c K : Addr) (st : XZ) (ws : List Spec.Cast5.Word) : Prop where
  xz : HoldsXZ m c st
  keys : Keys m K ws
  fr : Frame [⟨c, 64⟩, ⟨K, 128⟩] m0 m

/-- A write of `w / 8` bytes at `c + d`, within the working space. -/
theorem KMem.write {m0 m : Mem} {c K : Addr} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KMem m0 m c K st ws) (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) (hws : ws.length ≤ 32)
    {d w : Nat} (v : BitVec w) (hd : d + w / 8 ≤ 64) (hx : d + w / 8 ≤ 16 ∨ 48 ≤ d) :
    KMem m0 (m.writeW (c + BitVec.ofNat 64 d) v) c K st ws where
  xz a i hi := by
    have := off_lt a; have := off_ge a
    rw [byte_writeW_sep m c v (by omega_using [hd]) (by omega_arith) (by omega_arith)]
    exact h.xz a i hi
  keys i hi := by
    rw [Mem.readW_writeW_sep (dKS.sep (Offset.contains_base K (by omega_using [hws, hi]) (by omega_using [hws, hi]))
      (Offset.contains_base c (by omega_using [hd]) (by omega_using [hd]))) (by decide)]
    exact h.keys i hi
  fr := h.fr.writeW List.mem_cons_self v (Offset.contains_base c (by omega_using [hd]) (by omega_using [hd]))

/-- `st` with quadruple `q` of the array `a` replaced by `w`. -/
def XZ.put (st : XZ) : Arr → Nat → Spec.Cast5.Word → XZ
  | .x, q, w => { st with x := putQuad st.x q w }
  | .z, q, w => { st with z := putQuad st.z q w }

theorem XZ.arr_put (st : XZ) (a a' : Arr) (q : Nat) (w : Spec.Cast5.Word) (i : Nat) :
    (st.put a q w).arr a' i = if a' = a then putQuad (st.arr a) q w i else st.arr a' i := by
  cases a <;> cases a' <;> rfl

/-- A quadruple stored, byte-reversed, into `x` or `z`. -/
theorem KMem.quad {m0 m : Mem} {c K : Addr} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KMem m0 m c K st ws) (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) (hws : ws.length ≤ 32)
    (a : Arr) {q : Nat} (hq : q < 4) (w : Spec.Cast5.Word) :
    KMem m0 (m.writeW (c + BitVec.ofNat 64 (off a + 4 * q)) (byteRev32 w)) c K (st.put a q w) ws where
  xz a' i hi := by
    have := off_lt a; have := off_ge a; have := off_lt a'; have := off_ge a'
    simp only [Mem.writeW]
    rw [byte_write m c _ (by omega_arith) (by omega_arith), XZ.arr_put]
    by_cases ha : a' = a
    · subst ha
      rw [ite_eq_left rfl, putQuad]
      by_cases hi4 : i / 4 = q
      · rw [ite_eq_left (by omega_using [hi4]), ite_eq_left hi4, show off a' + i - (off a' + 4 * q) = i % 4 by omega_using [hi4]]
        simp only [BitVec.setWidth_eq]
        exact byteRev32_byte w (by omega_using [])
      · rw [ite_eq_right (by omega_using [hi4]), ite_eq_right hi4]
        exact h.xz a' i hi
    · rw [ite_eq_right ha, ite_eq_right (by cases a <;> cases a' <;> simp_all [off, xOff, zOff] <;> omega_arith)]
      exact h.xz a' i hi
  keys i hi := by
    have := off_lt a
    rw [Mem.readW_writeW_sep (dKS.sep (Offset.contains_base K (by omega_using [hws, hi]) (by omega_using [hws, hi]))
      (Offset.contains_base c (by omega_using [hq, this]) (by omega_using [hq, this]))) (by decide)]
    exact h.keys i hi
  fr := by
    have := off_lt a
    exact h.fr.writeW List.mem_cons_self _ (Offset.contains_base c (by omega_using [hq, this]) (by omega_using [hq, this]))

/-- The next subkey stored. -/
theorem KMem.key {m0 m : Mem} {c K : Addr} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KMem m0 m c K st ws) (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) (hws : ws.length < 32)
    (w : Spec.Cast5.Word) :
    KMem m0 (m.writeW (K + BitVec.ofNat 64 (4 * ws.length)) w) c K st (ws ++ [w]) where
  xz a i hi := by
    have := off_lt a
    have hb : Region.Contains ⟨K, 128⟩ (K + BitVec.ofNat 64 (4 * ws.length)) 4 :=
      Offset.contains_base K (by omega_using [hws]) (by omega_using [hws])
    simp only [Mem.writeW]
    rw [Mem.write_apply fun hx => dKS _ (hb.byte hx) (Offset.contains_base c (by omega_using [hi, this]) (by omega_using [hi, this]))]
    exact h.xz a i hi
  keys i hi := by
    rw [List.length_append, List.length_singleton] at hi
    by_cases hl : i < ws.length
    · rw [Mem.readW_writeW_sep (Offset.sep K (by omega_using [hl]) (by omega_using [hws, hi]) (by omega_using [hws])) (by decide),
        getD_append', ite_eq_left hl]
      exact h.keys i hl
    · rw [show i = ws.length by omega_using [hi, hl], Mem.readW_writeW_self32, getD_append', ite_eq_right (by omega_using []),
        Nat.sub_self]
      rfl
  fr := h.fr.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (Offset.contains_base K (by omega_using [hws]) (by omega_using [hws]))

/-- The extra lookups of a group, from the bytes at `a`, `b`, `c`, `d`. -/
def exVal (st : XZ) (a b c d : Pos) : Nat → Spec.Cast5.Word
  | 0 => Spec.Cast5.S8 (st.get d)
  | 1 => Spec.Cast5.S7 (st.get c)
  | 2 => Spec.Cast5.S6 (st.get b)
  | _ => Spec.Cast5.S5 (st.get a)

theorem exVal_sbox (st : XZ) (ls : List Impl.Cast5.Line) {e : Nat} (h5 : 5 ≤ e) (h8 : e ≤ 8) :
    exVal st (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8) (8 - e) =
      sbox e (st.get (extraOf ls e)) := by
  rcases (show e = 5 ∨ e = 6 ∨ e = 7 ∨ e = 8 by omega_using [h5, h8]) with rfl | rfl | rfl | rfl <;>
    simp only [exVal, sbox, Nat.reduceSub]

/-- The first `k` lines of a group storing into `a`. -/
def runQ (a : Arr) (ls : List Impl.Cast5.Line) (k : Nat) (st : XZ) : XZ :=
  (List.range k).foldl (fun s j => s.put a j (lineVal s (ls.getD j default))) st

theorem runQ_succ (a : Arr) (ls : List Impl.Cast5.Line) (k : Nat) (st : XZ) :
    runQ a ls (k + 1) st = (runQ a ls k st).put a k (lineVal (runQ a ls k st) (ls.getD k default)) := by
  simp only [runQ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem get_put (st : XZ) (a : Arr) (q : Nat) (w : Spec.Cast5.Word) {p : Pos} (hp : p.1 ≠ a) :
    (st.put a q w).get p = st.get p := by
  obtain ⟨a', i⟩ := p
  cases a <;> cases a' <;> first | exact absurd rfl hp | rfl

theorem get_runQ (a : Arr) (ls : List Impl.Cast5.Line) (k : Nat) (st : XZ) {p : Pos} (hp : p.1 ≠ a) :
    (runQ a ls k st).get p = st.get p := by
  induction k with
  | zero => rfl
  | succ k ih => rw [runQ_succ, get_put _ _ _ _ hp, ih]

theorem runQ_z (st : XZ) : runQ .z zLines 4 st = runZ zLines st := rfl
theorem runQ_x (st : XZ) : runQ .x xLines 4 st = runX xLines st := rfl

/-- What a group needs of its lines. -/
def GroupOk (a : Option Arr) (ls : List Impl.Cast5.Line) : Prop :=
  (∀ k < 4, lineOk (ls.getD k default) = true ∧
    extraOf ls (ls.getD k default).extra.1 = (ls.getD k default).extra.2 ∧
    a ≠ some (ls.getD k default).extra.2.1) ∧
  ∀ e < 4, (extraOf ls (5 + e)).2 < 16

theorem take_keys4 (ls : List Impl.Cast5.Line) (st : XZ) {k : Nat} (hk : k < 4) :
    (keys4 ls st).take (k + 1) = (keys4 ls st).take k ++ [lineVal st (ls.getD k default)] := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> rfl

/-- The halves done from `st`: the arrays and the subkeys so far. -/
def halves (st : XZ) : Nat → XZ × List Spec.Cast5.Word
  | 0 => (st, [])
  | h + 1 => ((halfImpl (halves st h).1).2, (halves st h).2 ++ (halfImpl (halves st h).1).1)

theorem halves_length (st : XZ) (h : Nat) : (halves st h).2.length = 16 * h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [halves, List.length_append, ih, halfImpl, keys4, List.length_cons, List.length_nil]
    omega_using []

theorem halves_succ (st : XZ) (h : Nat) :
    halves st (h + 1) = ((halfImpl (halves st h).1).2, (halves st h).2 ++ (halfImpl (halves st h).1).1) :=
  (rfl)

theorem halves_two (st : XZ) :
    (halves st 2).2 = (halfImpl st).1 ++ (halfImpl (halfImpl st).2).1 := by
  rw [halves_succ, halves_succ]
  exact congrArg (· ++ _) (List.nil_append _)

theorem bytesAt_getD (m : Mem) (p : Addr) (n i : Nat) :
    (Spec.Cast5.bytesAt m p n).getD i 0 = if i < n then m (p + BitVec.ofNat 64 i) else 0 := by
  simp only [Spec.Cast5.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  next hi => rw [List.getElem?_range hi]; rfl
  next hi => rw [List.getElem?_eq_none (by rw [List.length_range]; omega_using [hi])]; rfl

theorem vector_getElem_getD {α : Type} {n : Nat} (v : Vector α n) {i : Nat} (hi : i < n) (d : α) :
    v[i] = v.getD i d := by
  simp [Vector.getD, Array.getD, hi]

theorem scheduleAt_keys {m : Mem} {K : Addr} {ws : List Spec.Cast5.Word} (h : Keys m K ws)
    (hl : ws.length = 32) : Spec.Cast5.scheduleAt m K = Vector.ofFn fun i => ws.getD i.val 0 := by
  apply Vector.ext
  intro i hi
  rw [vector_getElem_getD _ hi 0, Proof.Cast5.scheduleAt_getD _ _ hi, h i (by omega_using [hl, hi]), Vector.getElem_ofFn]

end VG.Proof.Cast5
