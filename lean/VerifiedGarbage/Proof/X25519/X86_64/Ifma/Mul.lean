module

public import VerifiedGarbage.Impl.X25519.X86_64.Ifma
public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Sym
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Bound

/-! ### `X25519.X86_64.Ifma.Bound`, which this module and modules that import it used -/

section

/-!
# X25519 on x86-64 with AVX512_IFMA: terms as numbers

The limbs the ladder computes stay below `2⁶⁴`, and its differences never go
negative, so its additions, subtractions, multiply-adds and shifts never wrap.
`T.bnd` and `T.lb` bound each term from above and below, from bounds on the
registers and memory a block starts from; `T.ok` checks that nothing wraps
under those bounds (and that every blend picks whole quadwords); and `T.nat`
is its value as a number, with the reductions modulo `2⁶⁴` left out. `nat_ok`
proves that a term is `T.nat` and within its bounds where the kernel evaluates
`T.ok` of concrete terms to `true`, so the number a block computes is `nat` of
its term, which unfolds to the arithmetic of the ladder by definition.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi qw pick2 sel4 sel4_lt capW capW_ge orB orB_ge)

/-- Bounds on what a block starts from: the quadwords of each vector register
(`v`), each general-purpose register (`g`), and each quadword of the 32
bytes at each offset of the working space, from above (`m`) and below
(`ml`). -/
structure Bnds where
  v : Nat → Nat
  g : Reg → Nat
  m : Nat → Nat
  ml : Nat → Nat
  /-- The quadwords of `ymm (16 + r)`. -/
  h : Nat → Nat

/-- The values a block starts from, as numbers. -/
structure Env where
  v : Nat → Nat → Nat
  g : Reg → Nat
  m : Nat → Nat → Nat
  h : Nat → Nat → Nat

def envOf (s₀ : State) : Env :=
  ⟨fun r k => (qw s₀ (xr r) k).toNat, fun g => (s₀.gpr g).toNat,
    fun d k => (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64).toNat,
    fun r k => (qwH s₀ (hr r) k).toNat⟩

/-- Whether `vpblendd`'s selector takes quadword `k` from its second source
(`some true`), its first (`some false`), or doublewords of both (`none`). -/
def selQ (sel k : Nat) : Option Bool :=
  match sel.testBit (2 * k), sel.testBit (2 * k + 1) with
  | true, true => some true
  | false, false => some false
  | _, _ => none

/-- The bound on the low 52 bits of a product. -/
def loB (a b : Nat) : Nat := min (2 ^ 52 - 1) (min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1))
/-- The bound on the high 52 bits of a product. -/
def hiB (a b : Nat) : Nat := min a (2 ^ 52 - 1) * min b (2 ^ 52 - 1) / 2 ^ 52

def T.bnd (B : Bnds) : T → Nat → Nat
  | .reg r, _ => min (B.v r) (2 ^ 64 - 1)
  | .gpr g, _ => min (B.g g) (2 ^ 64 - 1)
  | .zero, _ => 0
  | .lane0 a, k => if k = 0 then a.bnd B 0 else 0
  | .bc a, _ => a.bnd B 0
  | .ld d, _ => min (B.m d) (2 ^ 64 - 1)
  | .add a b, k => capW (a.bnd B k + b.bnd B k)
  | .sub a _, k => a.bnd B k
  | .and a b, k => min (a.bnd B k) (b.bnd B k)
  | .xor _ _, _ => 2 ^ 64 - 1
  | .or a b, k => orB (a.bnd B k) (b.bnd B k)
  | .shl a n, k => capW (a.bnd B k * 2 ^ n)
  | .shr a n, k => a.bnd B k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.bnd B k else b.bnd B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.bnd B (k + 1) else b.bnd B k
  | .perm a o, k => a.bnd B (sel4 o k)
  | .blend a b sel, k => match selQ sel k with
    | some true => b.bnd B k
    | some false => a.bnd B k
    | none => 2 ^ 64 - 1
  | .mad false c a b, k => capW (c.bnd B k + loB (a.bnd B k) (b.bnd B k))
  | .mad true c a b, k => capW (c.bnd B k + hiB (a.bnd B k) (b.bnd B k))
  | .p2 a b hi, k => if k < 2 then a.bnd B (if hi then k + 2 else k) else b.bnd B (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.bnd B k else 0
  | .hreg r, _ => min (B.h r) (2 ^ 64 - 1)
  | .pd _ _, _ => 2 ^ 64 - 1

/-- A lower bound. -/
def T.lb (B : Bnds) : T → Nat → Nat
  | .ld d, _ => B.ml d
  | .add a b, k => a.lb B k + b.lb B k
  | .sub a b, k => a.lb B k - b.bnd B k
  | .perm a o, k => a.lb B (sel4 o k)
  | .blend a b sel, k => match selQ sel k with
    | some true => b.lb B k
    | some false => a.lb B k
    | none => 0
  | .mad _ c _ _, k => c.lb B k
  | .bc a, _ => a.lb B 0
  | _, _ => 0

/-- The value of a term as a number, with no reductions modulo `2⁶⁴`: what
the code computes where `T.ok` holds. -/
def T.nat (E : Env) : T → Nat → Nat
  | .reg r, k => E.v r k
  | .gpr g, _ => E.g g
  | .zero, _ => 0
  | .lane0 a, k => if k = 0 then a.nat E 0 else 0
  | .bc a, _ => a.nat E 0
  | .ld d, k => E.m d k
  | .add a b, k => a.nat E k + b.nat E k
  | .sub a b, k => a.nat E k - b.nat E k
  | .and a b, k => a.nat E k &&& b.nat E k
  | .xor a b, k => a.nat E k ^^^ b.nat E k
  | .or a b, k => a.nat E k ||| b.nat E k
  | .shl a n, k => a.nat E k * 2 ^ n
  | .shr a n, k => a.nat E k / 2 ^ n
  | .unpl a b, k => if k % 2 = 0 then a.nat E k else b.nat E (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.nat E (k + 1) else b.nat E k
  | .perm a o, k => a.nat E (sel4 o k)
  | .blend a b sel, k => match selQ sel k with
    | some true => b.nat E k
    | _ => a.nat E k
  | .mad false c a b, k => c.nat E k + a.nat E k % 2 ^ 52 * (b.nat E k % 2 ^ 52) % 2 ^ 52
  | .mad true c a b, k => c.nat E k + a.nat E k % 2 ^ 52 * (b.nat E k % 2 ^ 52) / 2 ^ 52
  | .p2 a b hi, k => if k < 2 then a.nat E (if hi then k + 2 else k) else b.nat E (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.nat E k else 0
  | .hreg r, k => E.h r k
  | .pd _ _, _ => 0

/-- Nothing in `t` wraps, by the bounds `B`, and every blend picks whole
quadwords. -/
def T.ok (B : Bnds) : T → Nat → Bool
  | .reg _, _ | .gpr _, _ | .ld _, _ | .zero, _ | .hreg _, _ => true
  | .lane0 a, k => if k = 0 then a.ok B 0 else true
  | .bc a, _ => a.ok B 0
  | .add a b, k => a.bnd B k + b.bnd B k < 2 ^ 64 && a.ok B k && b.ok B k
  | .sub a b, k => b.bnd B k ≤ a.lb B k && a.ok B k && b.ok B k
  | .and a b, k | .xor a b, k | .or a b, k => a.ok B k && b.ok B k
  | .shl a n, k => a.bnd B k * 2 ^ n < 2 ^ 64 && a.ok B k
  | .shr a _, k => a.ok B k
  | .unpl a b, k => if k % 2 = 0 then a.ok B k else b.ok B (k - 1)
  | .unph a b, k => if k % 2 = 0 then a.ok B (k + 1) else b.ok B k
  | .perm a o, k => a.ok B (sel4 o k)
  | .blend a b sel, k => (selQ sel k).isSome && a.ok B k && b.ok B k
  | .mad false c a b, k => c.bnd B k + loB (a.bnd B k) (b.bnd B k) < 2 ^ 64 && c.ok B k && a.ok B k && b.ok B k
  | .mad true c a b, k => c.bnd B k + hiB (a.bnd B k) (b.bnd B k) < 2 ^ 64 && c.ok B k && a.ok B k && b.ok B k
  | .p2 a b hi, k => if k < 2 then a.ok B (if hi then k + 2 else k) else b.ok B (if hi then k else k - 2)
  | .low a, k => if k < 2 then a.ok B k else true
  | .pd _ _, _ => false

/-- What a block starts from is within `B`. -/
structure EnvOK (s₀ : State) (B : Bnds) : Prop where
  v : ∀ r k, k < 4 → (qw s₀ (xr r) k).toNat ≤ B.v r
  g : ∀ g, (s₀.gpr g).toNat ≤ B.g g
  m : ∀ d k, k < 4 → (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64).toNat ≤ B.m d
  ml : ∀ d k, k < 4 → B.ml d ≤ (s₀.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (d + 8 * k)) 64).toNat
  h : ∀ r k, k < 4 → (qwH s₀ (hr r) k).toNat ≤ B.h r

theorem pick2_tt (a b : BitVec 64) : pick2 a b true true = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pick2, ite_true, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 32
  · simp [h]
  · simp only [h, decide_false, ite_false, decide_eq_true (show j - 32 < 32 by omega_arith), Bool.true_and]
    exact congrArg _ (by omega_arith)

theorem pick2_ff (a b : BitVec 64) : pick2 a b false false = a := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [pick2, Bool.false_eq_true, ite_false, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h : j < 32
  · simp [h]
  · simp only [h, decide_false, ite_false, decide_eq_true (show j - 32 < 32 by omega_arith), Bool.true_and]
    exact congrArg _ (by omega_arith)

theorem pick2_sel (a b : BitVec 64) (sel k : Nat) (hs : (selQ sel k).isSome = true) :
    pick2 a b (sel.testBit (2 * k)) (sel.testBit (2 * k + 1)) = if selQ sel k = some true then b else a := by
  unfold selQ at hs ⊢
  split at hs <;> simp only [Option.isSome_some, Option.isSome_none, reduceCtorEq] at hs
  · rename_i h1 h2
    rw [h1, h2, ite_eq_left rfl, pick2_tt]
  · rename_i h1 h2
    rw [h1, h2, ite_eq_right (by simp), pick2_ff]

theorem loB_ge {x y a b : Nat} (hx : x ≤ a) (hy : y ≤ b) :
    x % 2 ^ 52 * (y % 2 ^ 52) % 2 ^ 52 ≤ loB a b := by
  unfold loB
  have h1 : x % 2 ^ 52 ≤ min a (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hx,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have h2 : y % 2 ^ 52 ≤ min b (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hy,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  exact Nat.le_min.2 ⟨Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide)),
    Nat.le_trans (Nat.mod_le _ _) (Nat.mul_le_mul h1 h2)⟩

theorem hiB_ge {x y a b : Nat} (hx : x ≤ a) (hy : y ≤ b) :
    x % 2 ^ 52 * (y % 2 ^ 52) / 2 ^ 52 ≤ hiB a b := by
  unfold hiB
  have h1 : x % 2 ^ 52 ≤ min a (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hx,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  have h2 : y % 2 ^ 52 ≤ min b (2 ^ 52 - 1) := Nat.le_min.2 ⟨Nat.le_trans (Nat.mod_le _ _) hy,
    Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  exact Nat.div_le_div_right (Nat.mul_le_mul h1 h2)

theorem nat_ok {s₀ : State} {B : Bnds} (hE : EnvOK s₀ B) :
    ∀ (t : T) {k : Nat}, k < 4 → t.ok B k = true →
      (t.eval s₀ k).toNat = t.nat (envOf s₀) k ∧ (t.eval s₀ k).toNat ≤ t.bnd B k ∧
        t.lb B k ≤ (t.eval s₀ k).toNat := by
  intro t
  induction t with
  | reg r =>
    intro k hk _
    exact ⟨by simp only [T.eval, T.nat, envOf], Nat.le_min.2 ⟨hE.v r k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩,
      Nat.zero_le _⟩
  | gpr g =>
    intro k _ _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.g g, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩, Nat.zero_le _⟩
  | hreg r =>
    intro k hk _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.h r k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩, Nat.zero_le _⟩
  | zero => intro k _ _; exact ⟨rfl, by simp [T.eval, T.bnd], Nat.zero_le _⟩
  | lane0 a ih =>
    intro k _ ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ⟨(ih (by decide) ho).1, (ih (by decide) ho).2.1, Nat.zero_le _⟩
    · simp
  | bc a ih =>
    intro k _ ho
    exact ih (by decide) ho
  | ld d =>
    intro k hk _
    exact ⟨rfl, Nat.le_min.2 ⟨hE.m d k hk, Nat.le_sub_one_of_lt (BitVec.isLt _)⟩, hE.ml d k hk⟩
  | add a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba, la⟩ := iha hk oa
    obtain ⟨eb, bb, lb⟩ := ihb hk ob
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_add]
    rw [← ea, ← eb]
    have := BitVec.isLt (a.eval s₀ k + b.eval s₀ k)
    rw [BitVec.toNat_add] at this
    refine ⟨Nat.mod_eq_of_lt (by omega_arith), capW_ge (by rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith) this, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith
  | sub a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba, la⟩ := iha hk oa
    obtain ⟨eb, bb, lb⟩ := ihb hk ob
    have hle : (b.eval s₀ k).toNat ≤ (a.eval s₀ k).toNat := by omega_arith
    simp only [T.eval, T.nat, T.bnd, T.lb]
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.2 hle), ← ea, ← eb]
    exact ⟨rfl, by omega_arith, by omega_arith⟩
  | and a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba, _⟩ := iha hk ho.1
    obtain ⟨eb, bb, _⟩ := ihb hk ho.2
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_and]
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_min.2 ⟨Nat.le_trans Nat.and_le_left ba, Nat.le_trans Nat.and_le_right bb⟩,
      Nat.zero_le _⟩
  | xor a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba, _⟩ := iha hk ho.1
    obtain ⟨eb, bb, _⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ^^^ b.eval s₀ k)
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_xor] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, Nat.le_sub_one_of_lt this, Nat.zero_le _⟩
  | or a b iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨ea, ba, _⟩ := iha hk ho.1
    obtain ⟨eb, bb, _⟩ := ihb hk ho.2
    have := BitVec.isLt (a.eval s₀ k ||| b.eval s₀ k)
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_or] at this ⊢
    rw [← ea, ← eb]
    exact ⟨rfl, orB_ge ba bb this, Nat.zero_le _⟩
  | shl a n ih =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
    obtain ⟨ea, ba, _⟩ := ih hk ho.2
    have := BitVec.isLt (a.eval s₀ k <<< n)
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at this ⊢
    rw [← ea]
    have hm := Nat.mul_le_mul_right (2 ^ n) ba
    exact ⟨Nat.mod_eq_of_lt (by omega), capW_ge (by rw [Nat.mod_eq_of_lt (by omega)]; omega_using [hm]) this,
      Nat.zero_le _⟩
  | shr a n ih =>
    intro k hk ho
    obtain ⟨ea, ba, _⟩ := ih hk ho
    simp only [T.eval, T.nat, T.bnd, T.lb, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [← ea]
    exact ⟨rfl, Nat.div_le_div_right ba, Nat.zero_le _⟩
  | unpl a b iha ihb =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ⟨(iha hk ho).1, (iha hk ho).2.1, Nat.zero_le _⟩
    · rename_i h; rw [ite_eq_right h] at ho
      exact ⟨(ihb (by omega_arith) ho).1, (ihb (by omega_arith) ho).2.1, Nat.zero_le _⟩
  | unph a b iha ihb =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho
      exact ⟨(iha (by omega_arith) ho).1, (iha (by omega_arith) ho).2.1, Nat.zero_le _⟩
    · rename_i h; rw [ite_eq_right h] at ho; exact ⟨(ihb hk ho).1, (ihb hk ho).2.1, Nat.zero_le _⟩
  | perm a o ih =>
    intro k _ ho
    exact ih (sel4_lt _ _) ho
  | blend a b sel iha ihb =>
    intro k hk ho
    simp only [T.ok, Bool.and_eq_true] at ho
    obtain ⟨⟨hs, oa⟩, ob⟩ := ho
    obtain ⟨ea, ba, la⟩ := iha hk oa
    obtain ⟨eb, bb, lb⟩ := ihb hk ob
    simp only [T.eval, T.nat, T.bnd, T.lb]
    rw [pick2_sel _ _ _ _ hs]
    rcases hq : selQ sel k with _ | c
    · rw [hq] at hs; cases hs
    · cases c
      · exact ⟨ea, ba, la⟩
      · simp only [ite_true]; exact ⟨eb, bb, lb⟩
  | mad h c a b ihc iha ihb =>
    intro k hk ho
    have ha := BitVec.isLt (a.eval s₀ k)
    have hb := BitVec.isLt (b.eval s₀ k)
    cases h
    · simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
      obtain ⟨⟨⟨hs, oc⟩, oa⟩, ob⟩ := ho
      obtain ⟨ec, bc, lc⟩ := ihc hk oc
      obtain ⟨ea, ba, _⟩ := iha hk oa
      obtain ⟨eb, bb, _⟩ := ihb hk ob
      have hl := loB_ge ba bb
      simp only [T.eval, T.nat, T.bnd, T.lb]
      rw [mad52_toNat]
      simp only [Bool.false_eq_true, ite_false]
      rw [← ec, ← ea, ← eb, Nat.mod_eq_of_lt (by omega_arith)]
      exact ⟨rfl, capW_ge (by omega_arith) (by omega_arith), by omega_arith⟩
    · simp only [T.ok, Bool.and_eq_true, decide_eq_true_eq] at ho
      obtain ⟨⟨⟨hs, oc⟩, oa⟩, ob⟩ := ho
      obtain ⟨ec, bc, lc⟩ := ihc hk oc
      obtain ⟨ea, ba, _⟩ := iha hk oa
      obtain ⟨eb, bb, _⟩ := ihb hk ob
      have hl := hiB_ge ba bb (x := (a.eval s₀ k).toNat) (y := (b.eval s₀ k).toNat)
      simp only [T.eval, T.nat, T.bnd, T.lb]
      rw [mad52_toNat]
      simp only [ite_true]
      rw [← ec, ← ea, ← eb, Nat.mod_eq_of_lt (by omega_arith)]
      exact ⟨rfl, capW_ge (by omega_arith) (by omega_arith), by omega_arith⟩
  | p2 a b hi iha ihb =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho
      exact ⟨(iha (by split <;> omega_arith) ho).1, (iha (by split <;> omega_arith) ho).2.1, Nat.zero_le _⟩
    · rename_i h; rw [ite_eq_right h] at ho
      exact ⟨(ihb (by split <;> omega_arith) ho).1, (ihb (by split <;> omega_arith) ho).2.1, Nat.zero_le _⟩
  | low a ih =>
    intro k hk ho
    simp only [T.eval, T.nat, T.bnd, T.ok, T.lb] at ho ⊢
    split
    · rename_i h; rw [ite_eq_left h] at ho; exact ⟨(ih hk ho).1, (ih hk ho).2.1, Nat.zero_le _⟩
    · simp
  | pd i a _ _ =>
    intro k _ ho
    simp only [T.ok, Bool.false_eq_true] at ho

theorem SRel.nat {σ : Sym} {s₀ s : State} (h : SRel σ s₀ s) {B : Bnds} (hE : EnvOK s₀ B) {r : XReg}
    {k : Nat} (hk : k < 4) (ho : (σ.reg (xi r)).ok B k = true) :
    (qw s r k).toNat = (σ.reg (xi r)).nat (envOf s₀) k ∧ (qw s r k).toNat ≤ (σ.reg (xi r)).bnd B k := by
  rw [h.reg r k hk]; exact ⟨(nat_ok hE _ hk ho).1, (nat_ok hE _ hk ho).2.1⟩

end VG.Proof.X25519.X86_64.Ifma

end

end

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi qw)

/-- The low halves of the products `a_i b_j` with `i + j = c`, summed as the
code does. -/
def accLo (a b : Nat → Nat) (c : Nat) : Nat :=
  (List.range 5).foldl (fun acc i =>
    if i ≤ c ∧ c - i < 5 then acc + a i % 2 ^ 52 * (b (c - i) % 2 ^ 52) % 2 ^ 52 else acc) 0

/-- The high halves of the products `a_i b_j` with `i + j + 1 = c`. -/
def accHi (a b : Nat → Nat) (c : Nat) : Nat :=
  (List.range 5).foldl (fun acc i =>
    if i + 1 ≤ c ∧ c - (i + 1) < 5 then acc + a i % 2 ^ 52 * (b (c - (i + 1)) % 2 ^ 52) / 2 ^ 52
    else acc) 0

/-- Limb `k` of `mul4`: column `k` plus 19 times column `k + 5`. -/
def mulNat (a b : Nat → Nat) (k : Nat) : Nat :=
  accLo a b k + accHi a b k * 2 ^ 1 + (accLo a b (k + 5) + accHi a b (k + 5) * 2 ^ 1) +
    (accLo a b (k + 5) + accHi a b (k + 5) * 2 ^ 1) * 2 ^ 1 +
    (accLo a b (k + 5) + accHi a b (k + 5) * 2 ^ 1) * 2 ^ 4

def mulS (a : Nat) (h : (Sym.init.run (mul4 a)).isSome := by decide +kernel) : Sym :=
  (Sym.init.run (mul4 a)).get h

def mulB (a : Nat) : Bnds :=
  ⟨fun r => if 5 ≤ r ∧ r < 10 then 2 ^ 52 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if a ≤ d ∧ d < a + 160 ∧ d % 32 = 0 then 2 ^ 52 - 1 else 2 ^ 64 - 1, fun _ => 0,
    fun _ => 2 ^ 64 - 1⟩

theorem mulS_eq (a : Nat) (h : (Sym.init.run (mul4 a)).isSome) :
    Sym.init.run (mul4 a) = some (mulS a h) := (Option.some_get _).symm

def mulL : Sym := mulS OPL

theorem mulL_nat (E : Env) (l : Nat) : ∀ k < 5, (mulL.reg k).nat E l =
    mulNat (fun i => E.m (OPL + 32 * i) l) (fun j => E.v (5 + j) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mulL_ok : ∀ k < 5, ∀ l < 4, (mulL.reg k).ok (mulB OPL) l = true ∧
    (mulL.reg k).bnd (mulB OPL) l < 2 ^ 61 := by decide +kernel

theorem mulL_keep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → mulL.reg r = .reg r := by decide +kernel
theorem mulL_st : mulL.st = [] := by decide +kernel

def mulV : Sym := mulS OPV

theorem mulV_nat (E : Env) (l : Nat) : ∀ k < 5, (mulV.reg k).nat E l =
    mulNat (fun i => E.m (OPV + 32 * i) l) (fun j => E.v (5 + j) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mulV_ok : ∀ k < 5, ∀ l < 4, (mulV.reg k).ok (mulB OPV) l = true ∧
    (mulV.reg k).bnd (mulB OPV) l < 2 ^ 61 := by decide +kernel

theorem mulV_keep : ∀ r < 16, 5 ≤ r → r < 10 ∨ r = 15 → mulV.reg r = .reg r := by decide +kernel
theorem mulV_st : mulV.st = [] := by decide +kernel

/-! ## The ladder's products (`mulG`) -/

/-- The low halves of the products `a_i b_j` with `i + j = c`, summed onto
`acc` in `mulG`'s order: `a_0`'s last. -/
def gLoN (a b : Nat → Nat) (c acc : Nat) : Nat :=
  [1, 2, 3, 4, 0].foldl (fun acc i =>
    if i ≤ c ∧ c - i < 5 then acc + a i % 2 ^ 52 * (b (c - i) % 2 ^ 52) % 2 ^ 52 else acc) acc

/-- The high halves of the products `a_i b_j` with `i + j + 1 = c`, likewise. -/
def gHiN (a b : Nat → Nat) (c : Nat) : Nat :=
  [1, 2, 3, 4, 0].foldl (fun acc i =>
    if i + 1 ≤ c ∧ c - (i + 1) < 5 then acc + a i % 2 ^ 52 * (b (c - (i + 1)) % 2 ^ 52) / 2 ^ 52
    else acc) 0

/-- Column `c + 5` of `mulG`: its low halves and twice its high halves. -/
def gColH (a b : Nat → Nat) (k : Nat) : Nat := gLoN a b (k + 5) 0 + (gHiN a b (k + 5) + gHiN a b (k + 5))

/-- Limb `k` of `mulG`, as the code sums it: column `k`, from `p`, plus 19
times column `k + 5`. -/
def mulNatG (p : Nat) (a b : Nat → Nat) (k : Nat) : Nat :=
  gLoN a b k p + (gHiN a b k + gHiN a b k) + gColH a b k + (gColH a b k + gColH a b k) + gColH a b k * 2 ^ 4

def mulGS (pre : Bool) (h : (Sym.init.run (mulG pre)).isSome := by decide +kernel) : Sym :=
  (Sym.init.run (mulG pre)).get h

theorem mulGS_eq (pre : Bool) (h : (Sym.init.run (mulG pre)).isSome) :
    Sym.init.run (mulG pre) = some (mulGS pre h) := (Option.some_get _).symm

/-- The product with nothing added. -/
def mulG0 : Sym := mulGS false
/-- The product added to lanes 0 and 1 of what `ymm0–ymm4` held. -/
def mulG1 : Sym := mulGS true

theorem mulG0_eq : Sym.init.run (mulG false) = some mulG0 := mulGS_eq false _
theorem mulG1_eq : Sym.init.run (mulG true) = some mulG1 := mulGS_eq true _

/-- The bounds a product starts from: limbs below `2⁵²` in `ymm5–ymm14`, and
below `2⁶¹` in `ymm0–ymm4`. -/
def mulGB : Bnds :=
  ⟨fun r => if 5 ≤ r ∧ r < 15 then 2 ^ 52 - 1 else if r < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun _ => 2 ^ 64 - 1, fun _ => 0, fun _ => 2 ^ 64 - 1⟩

theorem mulG0_nat (E : Env) (l : Nat) : ∀ k < 5, (mulG0.reg k).nat E l =
    mulNatG 0 (fun i => E.v (10 + i) l) (fun j => E.v (5 + j) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem mulG1_nat (E : Env) : ∀ l < 4, ∀ k < 5, (mulG1.reg k).nat E l =
    mulNatG (if l < 2 then E.v k l else 0) (fun i => E.v (10 + i) l) (fun j => E.v (5 + j) l) k := by
  intro l hl k hk
  rcases (by omega_using [hk] : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega_using [hl] : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The bounds of a product's operands alone. -/
def mulG0B : Bnds :=
  ⟨fun r => if 5 ≤ r ∧ r < 15 then 2 ^ 52 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun _ => 2 ^ 64 - 1, fun _ => 0, fun _ => 2 ^ 64 - 1⟩

theorem mulG0_ok : ∀ k < 5, ∀ l < 4, (mulG0.reg k).ok mulG0B l = true ∧
    (mulG0.reg k).bnd mulG0B l < 2 ^ 61 := by decide +kernel

theorem mulG1_ok : ∀ k < 5, ∀ l < 4, (mulG1.reg k).ok mulGB l = true ∧
    (mulG1.reg k).bnd mulGB l < 2 ^ 62 := by decide +kernel

theorem mulG0_keep : ∀ r < 16, 5 ≤ r → mulG0.reg r = .reg r := by decide +kernel
theorem mulG1_keep : ∀ r < 15, 5 ≤ r → mulG1.reg r = .reg r := by decide +kernel
theorem mulG0_st : mulG0.st = [] := by decide +kernel
theorem mulG1_st : mulG1.st = [] := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma
