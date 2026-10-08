import VerifiedGarbage.Proof.Cast5.X86_64.KeyLine

/-!
# CAST5 key expansion on x86-64: the working space and the subkeys

The working space at `c` holds `x` and `z` (`HoldsXZ`) and the group's extra
lookups (`Extras`); the subkeys so far are at `K` (`Keys`). Each write of key
expansion keeps what it does not overwrite.
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.Impl.Cast5 VG.Impl.Cast5.X86_64

/-- A byte after a write at an offset of the same base. -/
theorem byte_write (m : Mem) (c : Addr) {d e n : Nat} (v : BitVec (8 * n)) (hd : d + n ≤ 2 ^ 63)
    (he : e < 2 ^ 63) :
    (m.write (c + BitVec.ofNat 64 d) n v) (c + BitVec.ofNat 64 e) =
      if d ≤ e ∧ e < d + n then v.extractLsb' (8 * (e - d)) 8 else m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.write]
  rw [Offset.sub_toNat' c (by omega) (by omega)]
  by_cases h : d ≤ e
  · rw [ite_eq_left h]
    by_cases h2 : e < d + n
    · rw [ite_eq_left (by omega), ite_eq_left ⟨h, h2⟩]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A byte outside a write. -/
theorem byte_writeW_sep (m : Mem) (c : Addr) {d e w : Nat} (v : BitVec w) (hd : d + w / 8 ≤ 2 ^ 63)
    (he : e < 2 ^ 63) (h : e < d ∨ d + w / 8 ≤ e) :
    (m.writeW (c + BitVec.ofNat 64 d) v) (c + BitVec.ofNat 64 e) = m (c + BitVec.ofNat 64 e) := by
  simp only [Mem.writeW]
  rw [byte_write m c _ hd he, ite_eq_right (by omega)]

/-- The subkeys `ws`, little-endian words, at `K`. -/
def Keys (m : Mem) (K : Addr) (ws : List Spec.Cast5.Word) : Prop :=
  ∀ i < ws.length, m.readW (K + BitVec.ofNat 64 (4 * i)) 32 = ws.getD i 0

/-- The group's extra lookups, lanes `0 … 3` at `c + 48`. -/
def Extras (m : Mem) (c : Addr) (f : Nat → Spec.Cast5.Word) : Prop :=
  ∀ j < 4, m.readW (c + BitVec.ofNat 64 (extraOff + 4 * j)) 32 = f j

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
    rw [byte_writeW_sep m c v (by omega) (by omega) (by omega)]
    exact h.xz a i hi
  keys i hi := by
    rw [Mem.readW_writeW_sep (dKS.sep (Offset.contains_base K (by omega) (by omega))
      (Offset.contains_base c (by omega) (by omega))) (by decide)]
    exact h.keys i hi
  fr := h.fr.writeW List.mem_cons_self v (Offset.contains_base c (by omega) (by omega))

/-- `Extras` after a write of `w / 8` bytes at `c + d`, below them. -/
theorem Extras.write {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {d w : Nat}
    (v : BitVec w) (hd : d + w / 8 ≤ extraOff) :
    Extras (m.writeW (c + BitVec.ofNat 64 d) v) c f := fun j hj => by
  rw [Mem.readW_writeW_sep (Offset.sep c (by unfold extraOff at *; omega) (by unfold extraOff; omega)
    (by unfold extraOff at *; omega)) (by decide)]
  exact h j hj

/-- `Extras` after a write elsewhere. -/
theorem Extras.write_disj {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {a : Addr}
    {w : Nat} (v : BitVec w) (hd : Region.Disjoint ⟨c, 64⟩ ⟨a, w / 8⟩) :
    Extras (m.writeW a v) c f := fun j hj => by
  rw [Mem.readW_writeW_sep (hd.sep (Offset.contains_base c (by unfold extraOff; omega)
    (by unfold extraOff; omega)) (Region.contains_self _ _)) (by decide)]
  exact h j hj

/-- `st` with quadruple `q` of the array `a` replaced by `w`. -/
def _root_.VG.Proof.Cast5.XZ.put (st : XZ) : Arr → Nat → Spec.Cast5.Word → XZ
  | .x, q, w => { st with x := putQuad st.x q w }
  | .z, q, w => { st with z := putQuad st.z q w }

theorem _root_.VG.Proof.Cast5.XZ.arr_put (st : XZ) (a a' : Arr) (q : Nat) (w : Spec.Cast5.Word) (i : Nat) :
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
    rw [byte_write m c _ (by omega) (by omega), XZ.arr_put]
    by_cases ha : a' = a
    · subst ha
      rw [ite_eq_left rfl, putQuad]
      by_cases hi4 : i / 4 = q
      · rw [ite_eq_left (by omega), ite_eq_left hi4, show off a' + i - (off a' + 4 * q) = i % 4 by omega]
        simp only [BitVec.setWidth_eq]
        exact byteRev32_byte w (by omega)
      · rw [ite_eq_right (by omega), ite_eq_right hi4]
        exact h.xz a' i hi
    · rw [ite_eq_right ha, ite_eq_right (by cases a <;> cases a' <;> simp_all [off, xOff, zOff] <;> omega)]
      exact h.xz a' i hi
  keys i hi := by
    have := off_lt a
    rw [Mem.readW_writeW_sep (dKS.sep (Offset.contains_base K (by omega) (by omega))
      (Offset.contains_base c (by omega) (by omega))) (by decide)]
    exact h.keys i hi
  fr := by
    have := off_lt a
    exact h.fr.writeW List.mem_cons_self _ (Offset.contains_base c (by omega) (by omega))

/-- The next subkey stored. -/
theorem KMem.key {m0 m : Mem} {c K : Addr} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KMem m0 m c K st ws) (dKS : Region.Disjoint ⟨K, 128⟩ ⟨c, 64⟩) (hws : ws.length < 32)
    (w : Spec.Cast5.Word) :
    KMem m0 (m.writeW (K + BitVec.ofNat 64 (4 * ws.length)) w) c K st (ws ++ [w]) where
  xz a i hi := by
    have := off_lt a
    have hb : Region.Contains ⟨K, 128⟩ (K + BitVec.ofNat 64 (4 * ws.length)) 4 :=
      Offset.contains_base K (by omega) (by omega)
    simp only [Mem.writeW]
    rw [Mem.write_apply fun hx => dKS _ (hb.byte hx) (Offset.contains_base c (by omega) (by omega))]
    exact h.xz a i hi
  keys i hi := by
    rw [List.length_append, List.length_singleton] at hi
    by_cases hl : i < ws.length
    · rw [Mem.readW_writeW_sep (Offset.sep K (by omega) (by omega) (by omega)) (by decide),
        getD_append', ite_eq_left hl]
      exact h.keys i hl
    · rw [show i = ws.length by omega, Mem.readW_writeW_self32, getD_append', ite_eq_right (by omega),
        Nat.sub_self]
      rfl
  fr := h.fr.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (Offset.contains_base K (by omega) (by omega))

end VG.Proof.Cast5.X86_64
