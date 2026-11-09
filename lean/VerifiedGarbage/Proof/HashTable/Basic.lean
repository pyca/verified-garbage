module

public import VerifiedGarbage.TCB.Sig
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Tables of hash functions: what every target's proofs share

That the first of a list of functions at the address of a name is that
name's, when distinct names are at distinct addresses (`find_name`,
`pw_ne`), as an indirect call of a table's function finds it; and, for the
contracts' satisfiability, addresses of functions distinct for distinct
names (`symsOf`) and the words of a table written to memory (`putWs`), and
the same for 32-bit targets (`symsOf32`, `putWs32`).
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

/-- The functions' addresses are distinct, in the list of the functions of
two tables of the same functions. -/
theorem symsOf_distinct2 {ns : List String} (h : ns.length < 2 ^ 32) :
    (ns ++ ns).Pairwise fun f g => f ≠ g → symsOf ns f ≠ symsOf ns g :=
  (List.pairwise_of_forall (R := fun _ _ => True) fun _ _ => trivial).imp_of_mem fun {f g} hf hg _ hne e => by
    have hf' : f ∈ ns := (List.mem_append.mp hf).elim id id
    have hg' : g ∈ ns := (List.mem_append.mp hg).elim id id
    have i1 := List.idxOf_lt_length_of_mem hf'
    have i2 := List.idxOf_lt_length_of_mem hg'
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

/-- The functions' addresses are distinct, in the list of the functions of
two tables of the same functions. -/
theorem symsOf32_distinct2 {ns : List String} (h : ns.length < 2 ^ 24) :
    (ns ++ ns).Pairwise fun f g => f ≠ g → (symsOf32 ns f).setWidth 64 ≠ (symsOf32 ns g).setWidth 64 :=
  (List.pairwise_of_forall (R := fun _ _ => True) fun _ _ => trivial).imp_of_mem fun {f g} hf hg _ hne e => by
    have hf' : f ∈ ns := (List.mem_append.mp hf).elim id id
    have hg' : g ∈ ns := (List.mem_append.mp hg).elim id id
    have i1 := List.idxOf_lt_length_of_mem hf'
    have i2 := List.idxOf_lt_length_of_mem hg'
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

/-- The words `ws` written from `p`. -/
def putWs (m : Mem) (p : Addr) : List (BitVec 64) → Mem
  | [] => m
  | w :: ws => putWs (m.writeW p w) (p + 8) ws

theorem add8_toNat {p : Addr} (h : p.toNat + 8 < 2 ^ 64) : (p + 8).toNat = p.toNat + 8 := by
  rw [BitVec.toNat_add, show (8 : Addr).toNat = 8 from rfl, Nat.mod_eq_of_lt h]

/-- A word apart from the words `putWs` writes. -/
theorem putWs_out {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    (a.toNat + 8 ≤ p.toNat ∨ p.toNat + 8 * ws.length ≤ a.toNat) → p.toNat + 8 * ws.length < 2 ^ 64 →
    a.toNat + 8 ≤ 2 ^ 64 → (putWs m p ws).readW a 64 = m.readW a 64
  | _, [], _, _, _ => rfl
  | p, w :: ws, h, hp, ha => by
    simp only [List.length_cons] at h hp
    have h8 := add8_toNat (p := p) (by omega)
    simp only [putWs]
    rw [putWs_out (by rw [h8]; omega) (by rw [h8]; omega) ha, readW_sep64 (by omega) ha (by omega)]

/-- The words `putWs` writes. -/
theorem putWs_held {m : Mem} : ∀ {p : Addr} {ws : List (BitVec 64)}, p.toNat + 8 * ws.length < 2 ^ 64 →
    Abi.tableHeld 64 (putWs m p ws) p ws
  | _, [], _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | p, w :: ws, hp => by
    simp only [List.length_cons] at hp
    have h8 := add8_toNat (p := p) (by omega)
    intro i hi
    simp only [putWs]
    cases i with
    | zero =>
      rw [show p + BitVec.ofNat 64 (64 / 8 * 0) = p from BitVec.add_zero p,
        putWs_out (.inl (by rw [h8])) (by rw [h8]; omega) (by omega), Mem.readW_writeW_self64]
      simp
    | succ i =>
      have := putWs_held (m := m.writeW p w) (p := p + 8) (ws := ws) (by rw [h8]; omega) i
        (by simp at hi; omega)
      rw [show p + BitVec.ofNat 64 (64 / 8 * (i + 1)) = p + 8 + BitVec.ofNat 64 (64 / 8 * i) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega]
      simpa using this


/-- The low halves of the words `ws` written from `p`, 4 bytes apart: a
table of a 32-bit target. -/
def putWs32 (m : Mem) (p : Addr) : List (BitVec 64) → Mem
  | [] => m
  | w :: ws => putWs32 (m.writeW p (w.setWidth 32)) (p + 4) ws

theorem add4_toNat {p : Addr} (h : p.toNat + 4 < 2 ^ 64) : (p + 4).toNat = p.toNat + 4 := by
  rw [BitVec.toNat_add, show (4 : Addr).toNat = 4 from rfl, Nat.mod_eq_of_lt h]

/-- A 32-bit word apart from the words `putWs32` writes. -/
theorem putWs32_out {m : Mem} {a : Addr} : ∀ {p : Addr} {ws : List (BitVec 64)},
    (a.toNat + 4 ≤ p.toNat ∨ p.toNat + 4 * ws.length ≤ a.toNat) → p.toNat + 4 * ws.length < 2 ^ 64 →
    a.toNat + 4 ≤ 2 ^ 64 → (putWs32 m p ws).readW a 32 = m.readW a 32
  | _, [], _, _, _ => rfl
  | p, w :: ws, h, hp, ha => by
    simp only [List.length_cons] at h hp
    have h4 := add4_toNat (p := p) (by omega)
    simp only [putWs32]
    rw [putWs32_out (by rw [h4]; omega) (by rw [h4]; omega) ha, readW_sep32 (by omega) ha (by omega)]

/-- The words `putWs32` writes. -/
theorem putWs32_held {m : Mem} : ∀ {p : Addr} {ws : List (BitVec 64)}, p.toNat + 4 * ws.length < 2 ^ 64 →
    Abi.tableHeld 32 (putWs32 m p ws) p ws
  | _, [], _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | p, w :: ws, hp => by
    simp only [List.length_cons] at hp
    have h4 := add4_toNat (p := p) (by omega)
    intro i hi
    simp only [putWs32]
    cases i with
    | zero =>
      rw [show p + BitVec.ofNat 64 (32 / 8 * 0) = p from BitVec.add_zero p,
        putWs32_out (.inl (by rw [h4])) (by rw [h4]; omega) (by omega), Mem.readW_writeW_self32]
      simp
    | succ i =>
      have := putWs32_held (m := m.writeW p (w.setWidth 32)) (p := p + 4) (ws := ws) (by rw [h4]; omega) i
        (by simp at hi; omega)
      rw [show p + BitVec.ofNat 64 (32 / 8 * (i + 1)) = p + 4 + BitVec.ofNat 64 (32 / 8 * i) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega]
      simpa using this

end VG.Proof.HashTable
