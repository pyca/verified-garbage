import VerifiedGarbage.Proof.Bignum.Layout

/-!
# Multiword arithmetic on x86-64: operands read from any header slot

Code that reads an operand's base from the header slot `sArr X` works for
whichever array `x` that slot names (`OpAt m B w X x`): the slot of its own
array (`X = x`, `Hdr.opAt`), or a slot the caller wrote the base into, when
the arrays are given at run time (`Impl/Bignum/X86_64/MontFn.lean`). A slot
below `sFn 12` keeps its value wherever the header does (`OpAt.of_outside`,
`OpAt.of_arrays`, `OpAt.of_frm`).
-/

namespace VG.Proof.Bignum

open VG VG.Impl.Bignum

/-- Header slot `sArr X` holds the base of array `x`. -/
def OpAt (m : Mem) (B : Addr) (w X x : Nat) : Prop := word m B (8 * sArr X) = off B (slot w x)

theorem Hdr.opAt {m : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : Hdr m B w minv) {x : Nat}
    (hx : x < 8) : OpAt m B w x x :=
  hH.harr x hx

theorem OpAt.of_word {m m' : Mem} {B : Addr} {w X x : Nat} (h : OpAt m B w X x)
    (he : word m' B (8 * sArr X) = word m B (8 * sArr X)) : OpAt m' B w X x :=
  he.trans h

theorem OpAt.of_outside {m m' : Mem} {B : Addr} {w X x : Nat} (h : OpAt m B w X x) {o n : Nat}
    (ho : Outside B o n m m') (hX : 8 * sArr X + 8 ≤ o ∨ o + n ≤ 8 * sArr X) (hX' : X < 24) :
    OpAt m' B w X x :=
  h.of_word (ho.word hX (by unfold sArr; omega))

theorem OpAt.of_arrays {m m' : Mem} {B : Addr} {w X x : Nat} {js : List Nat} (h : OpAt m B w X x)
    (ha : Arrays B w js m m') (hX : X < 24) : OpAt m' B w X x :=
  h.of_word (ha.word_eq (fun j _ => Or.inl (hdr_lt_slot w j (by unfold sArr; omega))) (by unfold sArr; omega))

theorem OpAt.of_frm {m m' : Mem} {B : Addr} {w X x : Nat} {rs : List (Nat × Nat)} (h : OpAt m B w X x)
    (hf : Frm B rs m m') (hX : ∀ r ∈ rs, 8 * sArr X + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sArr X) (hX' : X < 24) :
    OpAt m' B w X x :=
  h.of_word (hf.word_eq hX (by unfold sArr; omega))

/-- The header slots `sArr X` of the pairs `(X, x)` of `ps` hold the bases of
their arrays `x`, each below `sFn 12`, the first slot the ADX code borrows. -/
def Ops (m : Mem) (B : Addr) (w : Nat) (ps : List (Nat × Nat)) : Prop :=
  ∀ p ∈ ps, p.1 < 20 ∧ OpAt m B w p.1 p.2

theorem Ops.at {m : Mem} {B : Addr} {w : Nat} {ps : List (Nat × Nat)} (h : Ops m B w ps) {X x : Nat}
    (hp : (X, x) ∈ ps) : OpAt m B w X x :=
  (h _ hp).2

theorem Ops.lt {m : Mem} {B : Addr} {w : Nat} {ps : List (Nat × Nat)} (h : Ops m B w ps) {X x : Nat}
    (hp : (X, x) ∈ ps) : X < 20 :=
  (h _ hp).1

/-- With every pair a slot of its own array. -/
theorem Hdr.ops {m : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : Hdr m B w minv)
    {ps : List (Nat × Nat)} (hp : ∀ p ∈ ps, p.1 = p.2 ∧ p.2 < 8) : Ops m B w ps := fun p h => by
  obtain ⟨e, hx⟩ := hp p h
  exact ⟨by omega, by unfold OpAt; rw [e]; exact hH.harr _ hx⟩

/-- The three slots of the operands of `montMul o a b`, each its own. -/
theorem Hdr.ops3 {m : Mem} {B : Addr} {w : Nat} {minv : BitVec 64} (hH : Hdr m B w minv) {o a b : Nat}
    (ho : o < 8) (ha : a < 8) (hb : b < 8) : Ops m B w [(o, o), (a, a), (b, b)] :=
  hH.ops fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨rfl, ‹_›⟩

theorem Ops.of_word {m m' : Mem} {B : Addr} {w : Nat} {ps : List (Nat × Nat)} (h : Ops m B w ps)
    (he : ∀ X < 20, word m' B (8 * sArr X) = word m B (8 * sArr X)) : Ops m' B w ps := fun p hp =>
  ⟨(h p hp).1, (h p hp).2.of_word (he _ (h p hp).1)⟩

theorem Ops.of_outside {m m' : Mem} {B : Addr} {w : Nat} {ps : List (Nat × Nat)} (h : Ops m B w ps) {o n : Nat}
    (ho : Outside B o n m m') (hX : 8 * sFn 12 ≤ o) : Ops m' B w ps :=
  h.of_word fun X hX' => ho.word (by unfold sArr; unfold sFn at hX; omega) (by unfold sArr; omega)

theorem Ops.of_frm {m m' : Mem} {B : Addr} {w : Nat} {ps : List (Nat × Nat)} (h : Ops m B w ps)
    {rs : List (Nat × Nat)} (hf : Frm B rs m m') (hX : ∀ r ∈ rs, 8 * sFn 12 ≤ r.1) : Ops m' B w ps :=
  h.of_word fun X hX' => hf.word_eq (fun r hr => by have := hX r hr; unfold sArr; unfold sFn at this; omega)
    (by unfold sArr; omega)

theorem Ops.of_arrays {m m' : Mem} {B : Addr} {w : Nat} {ps : List (Nat × Nat)} (h : Ops m B w ps)
    {js : List Nat} (ha : Arrays B w js m m') : Ops m' B w ps :=
  h.of_word fun X hX' => ha.word_eq (fun j _ => Or.inl (hdr_lt_slot w j (by unfold sArr; omega)))
    (by unfold sArr; omega)

/-- A store to a slot from `sFn 12` on keeps them. -/
theorem Ops.store {m : Mem} {B : Addr} {w : Nat} {ps : List (Nat × Nat)} (h : Ops m B w ps) {i : Nat}
    (hi : sFn 12 ≤ i) (hi' : i < 32) (v : BitVec 64) : Ops (m.writeW (off B (8 * i)) v) B w ps :=
  h.of_word fun X hX' => (writeW_outside m B v (by omega)).word (by unfold sArr; unfold sFn at hi; omega)
    (by unfold sArr; omega)

end VG.Proof.Bignum
