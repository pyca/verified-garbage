module

public import VerifiedGarbage.TCB.Sig
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Tables of the interface `Hash`: what every target's proofs share

That the first of a list of functions at the address of a name is that
name's, when distinct names are at distinct addresses (`find_name`,
`pw_ne`), as an indirect call of a table's function finds it; and, for the
contracts' satisfiability, addresses of functions distinct for distinct
names (`symsOf`) and a table of five 64-bit words written to memory
(`put5`), and the same for 32-bit targets (`symsOf32`, `put5w`).
-/

@[expose] public section

namespace VG.Proof.HashTable

open VG

-- Code's equality, for the registrations' checks that the variants'
-- functions of the same name have the same code.
deriving instance DecidableEq for VG.Code

/-- Distinct names at distinct addresses, for any two of a list. -/
theorem pw_ne {sy : String → Addr} : ∀ {l : List String}, l.Pairwise (fun f g => f ≠ g → sy f ≠ sy g) →
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y → sy x ≠ sy y
  | [], _ => by simp
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    intro x hx y hy hne
    rcases List.mem_cons.mp hx with ex | lx
    · rcases List.mem_cons.mp hy with ey | ly
      · exact absurd (ex.trans ey.symm) hne
      · subst ex; exact h.1 y ly hne
    · rcases List.mem_cons.mp hy with ey | ly
      · subst ey; exact fun e => h.1 x lx (Ne.symm hne) e.symm
      · exact pw_ne h.2 x lx y ly hne

/-- The first function of `ts` at the address of `n` is `n`'s, when the
functions of other names are elsewhere and those of the name `n` are `c`. -/
theorem find_name {β : Type} {sy : String → Addr} : ∀ {ts : List (String × β)} {n : String} {c : β},
    (n, c) ∈ ts → (∀ q ∈ ts, q.1 ≠ n → sy q.1 ≠ sy n) → (∀ q ∈ ts, q.1 = n → q.2 = c) →
    ts.find? (fun q => sy q.1 == sy n) = some (n, c)
  | [], _, _, h, _, _ => absurd h List.not_mem_nil
  | q :: ts, n, c, hm, hd, hc => by
    simp only [List.find?_cons]
    by_cases he : q.1 = n
    · have e2 := hc q (List.mem_cons_self ..) he
      obtain ⟨q1, q2⟩ := q
      simp only at he e2
      subst he e2
      simp
    · have hne := hd q (List.mem_cons_self ..) he
      have e : (sy q.1 == sy n) = false := by simpa using hne
      rw [e]
      exact find_name ((List.mem_cons.mp hm).resolve_left fun e' => he (by rw [← e'])) (fun r hr => hd r
        (List.mem_cons_of_mem _ hr)) fun r hr => hc r (List.mem_cons_of_mem _ hr)

/-! ## A state holding a table, for the contracts' satisfiability -/

/-- Addresses of `ns`' names, distinct for distinct names. -/
def symsOf (ns : List String) (n : String) : Addr := BitVec.ofNat 64 (0x400000 + 16 * ns.idxOf n)

theorem symsOf_distinct {ns : List String} (h : ns.length < 2 ^ 32) :
    ns.Pairwise fun f g => f ≠ g → symsOf ns f ≠ symsOf ns g :=
  (List.pairwise_of_forall (R := fun _ _ => True) fun _ _ => trivial).imp_of_mem fun {f g} hf hg _ hne e => by
    have i1 := List.idxOf_lt_length_of_mem hf
    have i2 := List.idxOf_lt_length_of_mem hg
    have e' := congrArg BitVec.toNat e
    simp only [symsOf, BitVec.toNat_ofNat] at e'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e'
    have hi : ns.idxOf f = ns.idxOf g := by omega
    exact hne (by rw [← List.getElem_idxOf i1, ← List.getElem_idxOf i2]; simp only [hi])

/-- A 64-bit word apart from a write of one. -/
theorem readW_sep64 {m : Mem} {a b : Addr} {v : BitVec 64} (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat)
    (ha : a.toNat + 8 ≤ 2 ^ 64) (hb : b.toNat + 8 ≤ 2 ^ 64) : (m.writeW b v).readW a 64 = m.readW a 64 :=
  Mem.readW_writeW_sep (fun x h1 h2 => by
    simp only [Nat.reduceDiv] at h1 h2
    rcases h with h | h <;> bv_omega) (by decide)

/-- Five words written at `p`. -/
def put5 (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ : BitVec 64) : Mem :=
  ((((m.writeW (p + BitVec.ofNat 64 (8 * 0)) w₀).writeW (p + BitVec.ofNat 64 (8 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (8 * 2)) w₂).writeW (p + BitVec.ofNat 64 (8 * 3)) w₃).writeW (p + BitVec.ofNat 64 (8 * 4)) w₄

/-- The table `put5` writes at `0x300000`. -/
theorem put5_held {m : Mem} {ws : List (BitVec 64)} (hl : ws.length = 5) :
    Abi.tableHeld 64 (put5 m 0x300000 (ws.getD 0 0) (ws.getD 1 0) (ws.getD 2 0) (ws.getD 3 0) (ws.getD 4 0))
      0x300000 ws := by
  intro i hi
  rw [hl] at hi
  simp only [put5]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [readW_sep64, Mem.readW_writeW_self64, BitVec.setWidth_eq] <;> decide
  · rw [Mem.readW_writeW_self64, BitVec.setWidth_eq]

/-- Below `0x300000`, `put5` at `0x300000` changes no word. -/
theorem put5_below {m : Mem} {a : Addr} (ha : a.toNat + 8 ≤ 0x300000) (w₀ w₁ w₂ w₃ w₄ : BitVec 64) :
    (put5 m 0x300000 w₀ w₁ w₂ w₃ w₄).readW a 64 = m.readW a 64 := by
  have h0 : (0x300000 + BitVec.ofNat 64 (8 * 0) : Addr).toNat = 0x300000 := by decide
  have h1 : (0x300000 + BitVec.ofNat 64 (8 * 1) : Addr).toNat = 0x300008 := by decide
  have h2 : (0x300000 + BitVec.ofNat 64 (8 * 2) : Addr).toNat = 0x300010 := by decide
  have h3 : (0x300000 + BitVec.ofNat 64 (8 * 3) : Addr).toNat = 0x300018 := by decide
  have h4 : (0x300000 + BitVec.ofNat 64 (8 * 4) : Addr).toNat = 0x300020 := by decide
  simp only [put5]
  rw [readW_sep64, readW_sep64, readW_sep64, readW_sep64, readW_sep64]
  all_goals first | (simp only [h0, h1, h2, h3, h4]; omega) | omega

/-! ## The same for 32-bit targets -/

/-- Addresses of `ns`' names, 32 bits wide, distinct for distinct names. -/
def symsOf32 (ns : List String) (n : String) : BitVec 32 := BitVec.ofNat 32 (0x400000 + 16 * ns.idxOf n)

theorem symsOf32_distinct {ns : List String} (h : ns.length < 2 ^ 24) :
    ns.Pairwise fun f g => f ≠ g → (symsOf32 ns f).setWidth 64 ≠ (symsOf32 ns g).setWidth 64 :=
  (List.pairwise_of_forall (R := fun _ _ => True) fun _ _ => trivial).imp_of_mem fun {f g} hf hg _ hne e => by
    have i1 := List.idxOf_lt_length_of_mem hf
    have i2 := List.idxOf_lt_length_of_mem hg
    have e' := congrArg BitVec.toNat e
    simp only [symsOf32, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at e'
    rw [Nat.mod_eq_of_lt (a := _ % 2 ^ 32) (by omega), Nat.mod_eq_of_lt (a := _ % 2 ^ 32) (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e'
    have hi : ns.idxOf f = ns.idxOf g := by omega
    exact hne (by rw [← List.getElem_idxOf i1, ← List.getElem_idxOf i2]; simp only [hi])

/-- A 32-bit word apart from a write of one. -/
theorem readW_sep32 {m : Mem} {a b : Addr} {v : BitVec 32} (h : a.toNat + 4 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat)
    (ha : a.toNat + 4 ≤ 2 ^ 64) (hb : b.toNat + 4 ≤ 2 ^ 64) : (m.writeW b v).readW a 32 = m.readW a 32 :=
  Mem.readW_writeW_sep (fun x h1 h2 => by
    simp only [Nat.reduceDiv] at h1 h2
    rcases h with h | h <;> bv_omega) (by decide)

/-- Five 32-bit words written at `p`. -/
def put5w (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ : BitVec 32) : Mem :=
  ((((m.writeW (p + BitVec.ofNat 64 (4 * 0)) w₀).writeW (p + BitVec.ofNat 64 (4 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (4 * 2)) w₂).writeW (p + BitVec.ofNat 64 (4 * 3)) w₃).writeW (p + BitVec.ofNat 64 (4 * 4)) w₄

/-- The table `put5w` writes at `0x300000`, of the low halves of `ws`. -/
theorem put5w_held {m : Mem} {ws : List (BitVec 64)} (hl : ws.length = 5) :
    Abi.tableHeld 32 (put5w m 0x300000 ((ws.getD 0 0).setWidth 32) ((ws.getD 1 0).setWidth 32)
      ((ws.getD 2 0).setWidth 32) ((ws.getD 3 0).setWidth 32) ((ws.getD 4 0).setWidth 32)) 0x300000 ws := by
  intro i hi
  rw [hl] at hi
  simp only [put5w, Nat.reduceDiv]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
  · rw [readW_sep32, readW_sep32, readW_sep32, readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [readW_sep32, readW_sep32, readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [readW_sep32, readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [readW_sep32, Mem.readW_writeW_self32] <;> decide
  · rw [Mem.readW_writeW_self32]

/-- Below `0x300000`, `put5w` at `0x300000` changes no 32-bit word. -/
theorem put5w_below {m : Mem} {a : Addr} (ha : a.toNat + 4 ≤ 0x300000) (w₀ w₁ w₂ w₃ w₄ : BitVec 32) :
    (put5w m 0x300000 w₀ w₁ w₂ w₃ w₄).readW a 32 = m.readW a 32 := by
  have h0 : (0x300000 + BitVec.ofNat 64 (4 * 0) : Addr).toNat = 0x300000 := by decide
  have h1 : (0x300000 + BitVec.ofNat 64 (4 * 1) : Addr).toNat = 0x300004 := by decide
  have h2 : (0x300000 + BitVec.ofNat 64 (4 * 2) : Addr).toNat = 0x300008 := by decide
  have h3 : (0x300000 + BitVec.ofNat 64 (4 * 3) : Addr).toNat = 0x30000C := by decide
  have h4 : (0x300000 + BitVec.ofNat 64 (4 * 4) : Addr).toNat = 0x300010 := by decide
  simp only [put5w]
  rw [readW_sep32, readW_sep32, readW_sep32, readW_sep32, readW_sep32]
  all_goals first | (simp only [h0, h1, h2, h3, h4]; omega) | omega

end VG.Proof.HashTable
