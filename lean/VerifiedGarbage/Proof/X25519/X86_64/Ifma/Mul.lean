module

public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Bound
public import VerifiedGarbage.Impl.X25519.X86_64.Ifma

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
