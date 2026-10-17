module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Sym
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Bound
public import VerifiedGarbage.Proof.Poly1305.Limbs44

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: terms as numbers

As for AVX-512 (`Avx512/Bound.lean`): the limbs the code computes stay far
below `2⁶⁴`, so its additions and left shifts never wrap. `Q.bnd` bounds each
term from bounds on the registers it starts from, `Q.ok` checks that its
additions (those of `vpmadd52luq` and `vpmadd52huq` included) and left shifts
do not wrap under those bounds, and `Q.nat` is its value as a number. A
multiply-add takes the low 52 bits of its sources (`% 2⁵²` in `Q.nat`), and
adds the low (or high) 52 bits of their product. `nat_ok` proves that a term
is `Q.nat` and within `Q.bnd` where the kernel evaluates `Q.ok` of concrete
terms to `true`; `Q.natw` is the value with every reduction kept, exact for
any term (`natw_ok`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi capW orB capW_ge orB_ge)
open VG.Proof.Poly1305.X86_64.Avx512 (qz shufIdx shufIdx_lt)
open VG.Proof.X25519.X86_64.Ifma (mad52 mad52_toNat)
open VG.Proof.Poly1305.Limbs44 (madN)

/-- Bounds on the registers a block starts from: on each vector register's
quadwords (`v`), on the general-purpose registers, and on the quadwords of
memory at `rdi + d` (`mb`). -/
structure Bnds where
  v : XReg → Nat
  g : Reg → Nat
  mb : Nat → Nat

/-- The values a block starts from, as numbers. -/
abbrev Env := Avx512.Env
abbrev envOf := Avx512.envOf

/-- A bound on `madN h a b` from bounds on `a` and `b`. -/
def madB (h : Bool) (a b : Nat) : Nat :=
  if h then min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1) / 2 ^ 52
  else min (min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1)) (2 ^ 52 - 1)

theorem madN_le {h : Bool} {a b A B : Nat} (ha : a ≤ A) (hb : b ≤ B) : madN h a b ≤ madB h A B := by
  have a1 : a % 2 ^ 52 ≤ min A (2 ^ 52 - 1) :=
    Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) ha, Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have b1 : b % 2 ^ 52 ≤ min B (2 ^ 52 - 1) :=
    Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hb, Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have p := Nat.mul_le_mul a1 b1
  cases h
  · simp only [madN, madB, Bool.false_eq_true, ite_false]
    exact Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) p, Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  · simp only [madN, madB, ite_true]
    exact Nat.div_le_div_right p

def Q.bnd (B : Bnds) : Q → Nat → Nat
  | .reg r, _ => min (B.v (xr r)) (2 ^ 64 - 1)
  | .gpr g, _ => min (B.g g) (2 ^ 64 - 1)
  | .lane0 a, k => if k = 0 then a.bnd B 0 else 0
  | .bc a, _ => a.bnd B 0
  | .ld _, _ => 2 ^ 64 - 1
  | .mb d, _ => min (B.mb d) (2 ^ 64 - 1)
  | .zero, _ => 0
  | .add a b, k => capW (a.bnd B k + b.bnd B k)
  | .and a b, k => min (a.bnd B k) (b.bnd B k)
  | .or a b, k => orB (a.bnd B k) (b.bnd B k)
  | .shl a n, k => capW (a.bnd B k * 2 ^ n)
  | .shr a n, k => a.bnd B k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.bnd B k else b.bnd B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.bnd B (k + 1) else b.bnd B k
  | .shuf a b sel, k => if k / 2 < 2 then a.bnd B (shufIdx sel k) else b.bnd B (shufIdx sel k)
  | .mad h c a b, k => capW (c.bnd B k + madB h (a.bnd B k) (b.bnd B k))

/-- The value of a term as a number, with no reductions modulo `2⁶⁴`: what
the code computes where `Q.ok` holds. -/
def Q.nat (E : Env) : Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.nat E 0 else 0
  | .bc a, _ => a.nat E 0
  | .ld i, k => E.m (i + k)
  | .mb d, _ => E.mb d
  | .zero, _ => 0
  | .add a b, k => a.nat E k + b.nat E k
  | .and a b, k => a.nat E k &&& b.nat E k
  | .or a b, k => a.nat E k ||| b.nat E k
  | .shl a n, k => a.nat E k * 2 ^ n
  | .shr a n, k => a.nat E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.nat E k else b.nat E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.nat E (k + 1) else b.nat E k
  | .shuf a b sel, k => if k / 2 < 2 then a.nat E (shufIdx sel k) else b.nat E (shufIdx sel k)
  | .mad h c a b, k => c.nat E k + madN h (a.nat E k) (b.nat E k)

/-- The value of a term as a number, reduced as the code does: exact
whatever the bounds (`natw_ok`). -/
def Q.natw (E : Env) : Q → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .lane0 a, k => if k = 0 then a.natw E 0 else 0
  | .bc a, _ => a.natw E 0
  | .ld i, k => E.m (i + k)
  | .mb d, _ => E.mb d
  | .zero, _ => 0
  | .add a b, k => (a.natw E k + b.natw E k) % 2 ^ 64
  | .and a b, k => a.natw E k &&& b.natw E k
  | .or a b, k => a.natw E k ||| b.natw E k
  | .shl a n, k => a.natw E k * 2 ^ n % 2 ^ 64
  | .shr a n, k => a.natw E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.natw E k else b.natw E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.natw E (k + 1) else b.natw E k
  | .shuf a b sel, k => if k / 2 < 2 then a.natw E (shufIdx sel k) else b.natw E (shufIdx sel k)
  | .mad h c a b, k => (c.natw E k + madN h (a.natw E k) (b.natw E k)) % 2 ^ 64

/-- No addition or left shift in `t` wraps, by the bounds `B`. -/
def Q.ok (B : Bnds) : Q → Nat → Bool
  | .reg _, _ | .gpr _, _ | .ld _, _ | .mb _, _ | .zero, _ => true
  | .lane0 a, k => if k = 0 then a.ok B 0 else true
  | .bc a, _ => a.ok B 0
  | .add a b, k => a.bnd B k + b.bnd B k < 2 ^ 64 && a.ok B k && b.ok B k
  | .and a b, k | .or a b, k => a.ok B k && b.ok B k
  | .shl a n, k => a.bnd B k * 2 ^ n < 2 ^ 64 && a.ok B k
  | .shr a _, k => a.ok B k
  | .unpl a b, k => if k % 2 = 0 then a.ok B k else b.ok B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.ok B (k + 1) else b.ok B k
  | .shuf a b sel, k => if k / 2 < 2 then a.ok B (shufIdx sel k) else b.ok B (shufIdx sel k)
  | .mad h c a b, k =>
    c.bnd B k + madB h (a.bnd B k) (b.bnd B k) < 2 ^ 64 && c.ok B k && a.ok B k && b.ok B k

/-- The registers `s₀` starts from are within `B`. -/
structure EnvOK (s₀ : State) (B : Bnds) : Prop where
  v : ∀ r k, k < 8 → (qz s₀ r k).toNat ≤ B.v r
  g : ∀ g, (s₀.gpr g).toNat ≤ B.g g
  mb : ∀ d : Nat, (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofInt 64 (d : Int)) 64).toNat ≤ B.mb d

theorem mad52_nat (h : Bool) (c a b : BitVec 64) :
    (mad52 h c a b).toNat = (c.toNat + madN h a.toNat b.toNat) % 2 ^ 64 := by
  rw [mad52_toNat]; cases h <;> rfl

theorem nat_ok {s₀ : State} {B : Bnds} (hE : EnvOK s₀ B) :
    ∀ (t : Q) {k : Nat}, k < 8 → t.ok B k = true →
      (t.eval s₀ k).toNat = t.nat (envOf s₀) k ∧ (t.eval s₀ k).toNat ≤ t.bnd B k := by
  intro t
  induction t with
  | reg r =>
    intro k hk _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.v (xr r) k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | gpr g =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.g g, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | lane0 a ih =>
    intro k _ ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ih (by decide) ho
    · simp
  | bc a ih =>
    intro k _ ho
    exact ih (by decide) ho
  | ld i =>
    intro k _ _
    refine ⟨?_, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩
    simp only [Q.eval, Q.nat, envOf, Avx512.envOf, Nat.mul_add]
  | mb d =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.mb d, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩⟩
  | zero =>
    intro k _ _
    exact ⟨rfl, Nat.le_refl _⟩
  | add a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba⟩ := iha hk oa
    obtain ⟨eb, bb⟩ := ihb hk ob
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_add]
    rw [← ea, ← eb]
    have := BitVec.isLt (a.eval s₀ k + b.eval s₀ k)
    rw [BitVec.toNat_add] at this
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this⟩
  | and a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_and]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_min.2 ⟨Nat.le_trans Nat.and_le_left ba, Nat.le_trans Nat.and_le_right bb⟩⟩
  | or a b iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba⟩ := iha hk ho.1
    obtain ⟨eb, bb⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ||| b.eval s₀ k)
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_or] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, orB_ge ba bb this⟩
  | shl a n ih =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨ea, ba⟩ := ih hk ho.2
    have := BitVec.isLt (a.eval s₀ k <<< n)
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this ⊢
    rw [← ea]
    have hm := Nat.mul_le_mul_right (2 ^ n) ba
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega) this⟩
  | shr a n ih =>
    intro k hk ho
    obtain ⟨ea, ba⟩ := ih hk ho
    simp only [Q.eval, Q.nat, Q.bnd, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [← ea]
    exact ⟨rfl, Nat.div_le_div_right ba⟩
  | unpl a b iha ihb =>
    intro k hk ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha hk ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb (by omega) ho
  | unph a b iha ihb =>
    intro k hk ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha (by omega) ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb hk ho
  | shuf a b sel iha ihb =>
    intro k _ ho
    simp only [Q.eval, Q.nat, Q.bnd, Q.ok] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact iha (shufIdx_lt _ _) ho
    · rename_i h; rw [ite_eq_right h] at ho; exact ihb (shufIdx_lt _ _) ho
  | mad h c a b ihc iha ihb =>
    intro k hk ho
    simp only [Q.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨⟨hs, oc⟩, oa⟩, ob⟩ := ho
    obtain ⟨ec, bc⟩ := ihc hk oc
    obtain ⟨ea, ba⟩ := iha hk oa
    obtain ⟨eb, bb⟩ := ihb hk ob
    have hm := madN_le (h := h) ba bb
    simp only [Q.eval, Q.nat, Q.bnd, mad52_nat]
    rw [← ec, ← ea, ← eb]
    have hlt : (c.eval s₀ k).toNat + madN h (a.eval s₀ k).toNat (b.eval s₀ k).toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt]
    exact ⟨rfl, capW_ge (by omega) hlt⟩

theorem natw_ok (s₀ : State) : ∀ (t : Q) (k : Nat), (t.eval s₀ k).toNat = t.natw (envOf s₀) k := by
  intro t
  induction t with
  | reg r => intro k; rfl
  | gpr g => intro k; rfl
  | lane0 a ih =>
    intro k
    simp only [Q.eval, Q.natw]
    split
    · exact ih 0
    · rfl
  | bc a ih => intro k; exact ih 0
  | ld i => intro k; simp only [Q.eval, Q.natw, envOf, Avx512.envOf, Nat.mul_add]
  | mb d => intro k; rfl
  | zero => intro k; rfl
  | add a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_add, iha, ihb]
  | and a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_and, iha, ihb]
  | or a b iha ihb => intro k; simp only [Q.eval, Q.natw, BitVec.toNat_or, iha, ihb]
  | shl a n ih =>
    intro k; simp only [Q.eval, Q.natw, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ih]
  | shr a n ih =>
    intro k; simp only [Q.eval, Q.natw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ih]
  | unpl a b iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha k
    · exact ihb _
  | unph a b iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha _
    · exact ihb k
  | shuf a b sel iha ihb =>
    intro k; simp only [Q.eval, Q.natw]; split
    · exact iha _
    · exact ihb _
  | mad h c a b ihc iha ihb => intro k; simp only [Q.eval, Q.natw, mad52_nat, ihc, iha, ihb]

theorem SRel.nat {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {B : Bnds} (hE : EnvOK s₀ B) {r : XReg}
    {k : Nat} (hk : k < 8) (ho : (σ.reg (xi r)).ok B k = true) :
    (qz s r k).toNat = (σ.reg (xi r)).nat (envOf s₀) k ∧ (qz s r k).toNat ≤ (σ.reg (xi r)).bnd B k := by
  rw [h.reg r k hk]; exact nat_ok hE _ hk ho

theorem SRel.natw {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) (r : XReg) {k : Nat} (hk : k < 8) :
    (qz s r k).toNat = (σ.reg (xi r)).natw (envOf s₀) k := by
  rw [h.reg r k hk]; exact natw_ok s₀ _ k

end VG.Proof.Poly1305.X86_64.Ifma
