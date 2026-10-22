module

public import VerifiedGarbage.Proof.Ffdh.Lead

/-!
# FFDH: the first nonzero octet, by a scan of every octet

A branch-free scan reads every octet of `bs` and keeps the first nonzero
one and its index (`scanAt`, after `j` octets; the index is that of the last
octet until one is found). After all of them, it holds `lead bs` and its
octet (`scanAt_length`).
-/

@[expose] public section

namespace VG.Proof.Ffdh

open VG

/-- After `j` octets: whether a nonzero one was found, the index and the octet kept. -/
def scanAt (bs : List Byte) : Nat → Bool × Nat × Byte
  | 0 => (false, bs.length - 1, 0)
  | j + 1 =>
    let r := scanAt bs j
    if !r.1 && bs.getD j 0 != 0 then (true, j, bs.getD j 0) else r

theorem scanAt_succ (bs : List Byte) (j : Nat) :
    scanAt bs (j + 1) = if !(scanAt bs j).1 && bs.getD j 0 != 0 then (true, j, bs.getD j 0) else scanAt bs j :=
  rfl

theorem getD_of {bs : List Byte} {k : Nat} (hk : k < bs.length) : bs.getD k 0 = bs[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- The octet at `lead bs` is zero only if it is the last. -/
theorem lead_last {bs : List Byte} (h : bs ≠ []) (b : bs.getD (lead bs) 0 = 0) : bs.length - 1 = lead bs := by
  have hL := lead_lt h
  rcases Nat.lt_or_ge (lead bs + 1) bs.length with lt | ge
  · exact absurd (by rw [← getD_of hL]; exact b) (lead_nonzero h lt)
  · omega

/-- Before `lead bs`, nothing is found; after it, the scan holds it. -/
theorem scanAt_inv {bs : List Byte} (h : bs ≠ []) (j : Nat) (hj : j ≤ bs.length) :
    (j ≤ lead bs → scanAt bs j = (false, bs.length - 1, 0)) ∧
    (lead bs < j → scanAt bs j = (bs.getD (lead bs) 0 != 0, lead bs, bs.getD (lead bs) 0)) := by
  induction j with
  | zero => exact ⟨fun _ => rfl, fun h' => absurd h' (Nat.not_lt_zero _)⟩
  | succ j ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    rw [scanAt_succ]
    have z : ∀ k < lead bs, bs.getD k 0 = 0 := fun k hk => by
      obtain ⟨hk', e⟩ := lead_zero k hk
      rw [getD_of hk', e]
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · rw [ih₁ (by omega), z j (by omega)]; rfl
    · by_cases e : j = lead bs
      · subst e
        rw [ih₁ (Nat.le_refl _)]
        by_cases b : bs.getD (lead bs) 0 = 0
        · rw [lead_last h b]
          generalize bs.getD (lead bs) 0 = v at b ⊢
          subst b; rfl
        · generalize bs.getD (lead bs) 0 = v at b ⊢
          have b8 : ¬ v = 0#8 := b
          simp [b8]
      · rw [ih₂ (by omega)]
        by_cases b : bs.getD (lead bs) 0 = 0
        · have := lead_last h b
          omega
        · generalize bs.getD (lead bs) 0 = v at b ⊢
          have b8 : ¬ v = 0#8 := b
          rw [show (!(v != 0) && bs.getD j 0 != 0) = false by simp [b8]]
          rfl

/-- After every octet, the scan holds `lead bs` and its octet. -/
theorem scanAt_length {bs : List Byte} (h : bs ≠ []) :
    (scanAt bs bs.length).2 = (lead bs, bs.getD (lead bs) 0) := by
  rw [(scanAt_inv h bs.length (Nat.le_refl _)).2 (lead_lt h)]

end VG.Proof.Ffdh
