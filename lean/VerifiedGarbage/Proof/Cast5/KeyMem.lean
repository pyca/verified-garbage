import VerifiedGarbage.Proof.Cast5.KeyLines
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Cast5.Table

/-!
# CAST5 key expansion: the working space and the subkeys

The implementations keep `x` and `z` in the working space at `c`, a byte each
(`HoldsXZ`), and write the subkeys so far to `K` (`Keys`); each write of key
expansion keeps what it does not overwrite (`KMem`). A group of lines stores
into `x` or `z` (`runQ`) or appends subkeys (`keys4`), and the halves of §2.4
make the schedule (`halves`, `scheduleAt_keys`).
-/

namespace VG.Proof.Cast5

open VG VG.Impl.Cast5

/-- A byte after a write at an offset of the same base. -/
theorem byte_write (m : Mem) (c : Addr) {d e n : Nat} (v : BitVec (8 * n)) (hd : d + n ≤ 2 ^ 63)
    (he : e < 2 ^ 63) :
    (m.write (c + BitVec.ofNat 64 d) n v) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + n then v.extractLsb' (8 * (e - d)) 8 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.write]
  rw [Offset.sub_toNat' c (by omega_arith) (by omega_arith)]
  by_cases h : d ≤ e
  · rw [ite_eq_left h]
    by_cases h2 : e < d + n
    · rw [ite_eq_left (by omega_arith), ite_eq_left ⟨h, h2⟩]
    · rw [ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]
  · rw [ite_eq_right h, ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]

/-- A byte outside a write. -/
theorem byte_writeW_sep (m : Mem) (c : Addr) {d e w : Nat} (v : BitVec w) (hd : d + w / 8 ≤ 2 ^ 63)
    (he : e < 2 ^ 63) (h : e < d ∨ d + w / 8 ≤ e) :
    (m.writeW (c + BitVec.ofNat 64 d) v) (c + BitVec.ofNat 64 e) = m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he, ite_eq_right (by omega_arith)]

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
    Proof.Cast5.add_ofNat_add, quadOf, show off a + 4 * q + 1 + 1 + 1 = off a + (4 * q + 3) by omega_arith,
    show off a + 4 * q + 1 + 1 = off a + (4 * q + 2) by omega_arith,
    show off a + 4 * q + 1 = off a + (4 * q + 1) by omega_arith, h a _ (by omega_arith), h a _ (by omega_arith),
    h a _ (by omega_arith), h a _ (by omega_arith)]

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
    rw [byte_writeW_sep m c v (by omega_arith) (by omega_arith) (by omega_arith)]
    exact h.xz a i hi
  keys i hi := by
    rw [Mem.readW_writeW_sep (dKS.sep (Offset.contains_base K (by omega_arith) (by omega_arith))
      (Offset.contains_base c (by omega_arith) (by omega_arith))) (by decide)]
    exact h.keys i hi
  fr := h.fr.writeW List.mem_cons_self v (Offset.contains_base c (by omega_arith) (by omega_arith))

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
      · rw [ite_eq_left (by omega_arith), ite_eq_left hi4, show off a' + i - (off a' + 4 * q) = i % 4 by omega_arith]
        simp only [BitVec.setWidth_eq]
        exact byteRev32_byte w (by omega_arith)
      · rw [ite_eq_right (by omega_arith), ite_eq_right hi4]
        exact h.xz a' i hi
    · rw [ite_eq_right ha, ite_eq_right (by cases a <;> cases a' <;> simp_all [off, xOff, zOff] <;> omega_arith)]
      exact h.xz a' i hi
  keys i hi := by
    have := off_lt a
    rw [Mem.readW_writeW_sep (dKS.sep (Offset.contains_base K (by omega_arith) (by omega_arith))
      (Offset.contains_base c (by omega_arith) (by omega_arith))) (by decide)]
    exact h.keys i hi
  fr := by
    have := off_lt a
    exact h.fr.writeW List.mem_cons_self _ (Offset.contains_base c (by omega_arith) (by omega_arith))

/-- The next subkey stored. -/
theorem KMem.key {m0 m : Mem} {c K : Addr} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KMem m0 m c K st ws) (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) (hws : ws.length < 32)
    (w : Spec.Cast5.Word) :
    KMem m0 (m.writeW (K + BitVec.ofNat 64 (4 * ws.length)) w) c K st (ws ++ [w]) where
  xz a i hi := by
    have := off_lt a
    have hb : Region.Contains ⟨K, 128⟩ (K + BitVec.ofNat 64 (4 * ws.length)) 4 :=
      Offset.contains_base K (by omega_arith) (by omega_arith)
    simp only [Mem.writeW]
    rw [Mem.write_apply fun hx => dKS _ (hb.byte hx) (Offset.contains_base c (by omega_arith) (by omega_arith))]
    exact h.xz a i hi
  keys i hi := by
    rw [List.length_append, List.length_singleton] at hi
    by_cases hl : i < ws.length
    · rw [Mem.readW_writeW_sep (Offset.sep K (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        getD_append', ite_eq_left hl]
      exact h.keys i hl
    · rw [show i = ws.length by omega_arith, Mem.readW_writeW_self32, getD_append', ite_eq_right (by omega_arith),
        Nat.sub_self]
      rfl
  fr := h.fr.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (Offset.contains_base K (by omega_arith) (by omega_arith))

/-- The extra lookups of a group, from the bytes at `a`, `b`, `c`, `d`. -/
def exVal (st : XZ) (a b c d : Pos) : Nat → Spec.Cast5.Word
  | 0 => Spec.Cast5.S8 (st.get d)
  | 1 => Spec.Cast5.S7 (st.get c)
  | 2 => Spec.Cast5.S6 (st.get b)
  | _ => Spec.Cast5.S5 (st.get a)

theorem exVal_sbox (st : XZ) (ls : List Impl.Cast5.Line) {e : Nat} (h5 : 5 ≤ e) (h8 : e ≤ 8) :
    exVal st (extraOf ls 5) (extraOf ls 6) (extraOf ls 7) (extraOf ls 8) (8 - e) =
      sbox e (st.get (extraOf ls e)) := by
  rcases (show e = 5 ∨ e = 6 ∨ e = 7 ∨ e = 8 by omega_arith) with rfl | rfl | rfl | rfl <;>
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
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_arith) with rfl | rfl | rfl | rfl <;> rfl

/-- The halves done from `st`: the arrays and the subkeys so far. -/
def halves (st : XZ) : Nat → XZ × List Spec.Cast5.Word
  | 0 => (st, [])
  | h + 1 => ((halfImpl (halves st h).1).2, (halves st h).2 ++ (halfImpl (halves st h).1).1)

theorem halves_length (st : XZ) (h : Nat) : (halves st h).2.length = 16 * h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [halves, List.length_append, ih, halfImpl, keys4, List.length_cons, List.length_nil]
    omega_arith

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
  next hi => rw [List.getElem?_eq_none (by rw [List.length_range]; omega_arith)]; rfl

theorem vector_getElem_getD {α : Type} {n : Nat} (v : Vector α n) {i : Nat} (hi : i < n) (d : α) :
    v[i] = v.getD i d := by
  simp [Vector.getD, Array.getD, hi]

theorem scheduleAt_keys {m : Mem} {K : Addr} {ws : List Spec.Cast5.Word} (h : Keys m K ws)
    (hl : ws.length = 32) : Spec.Cast5.scheduleAt m K = Vector.ofFn fun i => ws.getD i.val 0 := by
  apply Vector.ext
  intro i hi
  rw [vector_getElem_getD _ hi 0, Proof.Cast5.scheduleAt_getD _ _ hi, h i (by omega_arith), Vector.getElem_ofFn]

end VG.Proof.Cast5
