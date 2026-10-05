import VerifiedGarbage.Impl.Weierstrass.AArch64.TComb

/-!
# The comb's tables in memory: their length

`tcombWords` of `J` tables of `H` entries each has `J H 2n` words
(`tcombWords_length`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass

theorem length_flatMap_uniform {α β : Type} (f : α → List β) (k : Nat) :
    ∀ (l : List α), (∀ x ∈ l, (f x).length = k) → (l.flatMap f).length = l.length * k
  | [], _ => by simp
  | x :: l, h => by
    rw [List.flatMap_cons, List.length_append, h x (List.mem_cons_self ..),
      length_flatMap_uniform f k l (fun y hy => h y (List.mem_cons_of_mem _ hy)), List.length_cons,
      Nat.succ_mul, Nat.add_comm]

theorem tcombWords_entry_len (n R p : Nat) (xy : Nat × Nat) :
    ((List.range n).map (wordOf (xy.1 * R % p)) ++ (List.range n).map (wordOf (xy.2 * R % p))).length =
      2 * n := by simp; omega

theorem tcombWords_length {n R p H J : Nat} {tbl : List (List (Nat × Nat))} (hJ : tbl.length = J)
    (hH : ∀ j < J, (tbl.getD j []).length = H) :
    (tcombWords n R p tbl).length = J * (H * (2 * n)) := by
  unfold tcombWords
  rw [length_flatMap_uniform _ (H * (2 * n)) _ (fun t ht => by
    obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem ht
    have := hH j' (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at this
    simp only [Option.getD_some] at this
    rw [length_flatMap_uniform _ (2 * n) _ fun xy _ => tcombWords_entry_len n R p xy, this]), hJ]

end VG.Proof.Weierstrass.AArch64
