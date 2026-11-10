module

public import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Arith
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem

/-!
# X25519 on x86-64 with AVX512_IFMA: carries

`carry r` leaves each limb's low 51 bits plus the bits from 51 up of the limb
below (of the top limb, times 19, for the lowest): the same number modulo `p`
(`carryNat_mod`), in limbs below `2⁵²` if they were below `2⁶³`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519

/-- The limbs `carry` leaves, with the mask `m` and the constant `k19`. -/
def carryNat (m k19 : Nat) (x : Nat → Nat) : Nat → Nat
  | 0 => (x 0 &&& m) + x 4 / 2 ^ 51 % 2 ^ 52 * (k19 % 2 ^ 52) % 2 ^ 52
  | 1 => (x 1 &&& m) + x 0 / 2 ^ 51
  | 2 => (x 2 &&& m) + x 1 / 2 ^ 51
  | 3 => (x 3 &&& m) + x 2 / 2 ^ 51
  | _ => (x 4 &&& m) + x 3 / 2 ^ 51

theorem carryNat_mod (x : Nat → Nat) (h4 : x 4 < 2 ^ 63) :
    lv (carryNat (2 ^ 51 - 1) 19 x) % P = lv x % P := by
  have e : lv (carryNat (2 ^ 51 - 1) 19 x) + 2 ^ 255 * (x 4 / 2 ^ 51) = lv x + 19 * (x 4 / 2 ^ 51) := by
    simp only [lv, carryNat, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have := fold255 (lv (carryNat (2 ^ 51 - 1) 19 x)) (x 4 / 2 ^ 51)
  rw [e] at this
  simp only [P] at this ⊢
  omega

/-- `carry r` run from its start. -/
def carryS (r : Nat → Nat) (h : (Sym.init.run (carry r)).isSome := by decide +kernel) : Sym :=
  (Sym.init.run (carry r)).get h

theorem carryS_eq (r : Nat → Nat) (h : (Sym.init.run (carry r)).isSome) :
    Sym.init.run (carry r) = some (carryS r h) := (Option.some_get _).symm

def carryI : Sym := carryS id
def carryF : Sym := carryS (5 + ·)

theorem carryI_nat (E : Env) (l : Nat) : ∀ k < 5,
    (carryI.reg k).nat E l = carryNat (E.m KM l) (E.m K19 l) (fun i => E.v i l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem carryF_nat (E : Env) (l : Nat) : ∀ k < 5,
    (carryF.reg (5 + k)).nat E l = carryNat (E.m KM l) (E.m K19 l) (fun i => E.v (5 + i) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

/-- The bounds `carry r` needs: limbs below `2⁶³`, and the constants. -/
def carryB (r : Nat → Nat) : Bnds :=
  ⟨fun i => if i = r 0 ∨ i = r 1 ∨ i = r 2 ∨ i = r 3 ∨ i = r 4 then 2 ^ 63 - 1 else 2 ^ 64 - 1,
    fun _ => 2 ^ 64 - 1, fun d => if d = KM then 2 ^ 51 - 1 else if d = K19 then 19 else 2 ^ 64 - 1,
    fun _ => 0, fun _ => 2 ^ 64 - 1⟩

theorem carryI_ok : ∀ k < 5, ∀ l < 4, (carryI.reg k).ok (carryB id) l = true ∧
    (carryI.reg k).bnd (carryB id) l < 2 ^ 52 := by decide +kernel

theorem carryF_ok : ∀ k < 5, ∀ l < 4, (carryF.reg (5 + k)).ok (carryB (5 + ·)) l = true ∧
    (carryF.reg (5 + k)).bnd (carryB (5 + ·)) l < 2 ^ 52 := by decide +kernel

theorem carryI_keep : ∀ r < 16, ¬ (r < 5 ∨ (10 ≤ r ∧ r < 13)) → carryI.reg r = .reg r := by
  decide +kernel

theorem carryF_keep : ∀ r < 16, ¬ ((5 ≤ r ∧ r < 13)) → carryF.reg r = .reg r := by
  decide +kernel

theorem carryI_st : carryI.st = [] := by decide +kernel
theorem carryF_st : carryF.st = [] := by decide +kernel

/-! ## The carries of stages 2 and 3 (`carryT`) -/

/-- Stage 2's carry, of its first operand in `ymm10–ymm14`. -/
def carryU : Sym := (Sym.init.run (carryT (10 + ·) 15 5 6)).get (by decide +kernel)
/-- Stage 3's carry, of stage 2's product in `ymm0–ymm4`. -/
def carryR : Sym := (Sym.init.run (carryT id 15 5 6)).get (by decide +kernel)

theorem carryU_eq : Sym.init.run (carryT (10 + ·) 15 5 6) = some carryU := (Option.some_get _).symm
theorem carryR_eq : Sym.init.run (carryT id 15 5 6) = some carryR := (Option.some_get _).symm

theorem carryU_nat (E : Env) (l : Nat) : ∀ k < 5,
    (carryU.reg (10 + k)).nat E l = carryNat (E.m KM l) (E.m K19 l) (fun i => E.v (10 + i) l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem carryR_nat (E : Env) (l : Nat) : ∀ k < 5,
    (carryR.reg k).nat E l = carryNat (E.m KM l) (E.m K19 l) (fun i => E.v i l) k
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem carryU_ok : ∀ k < 5, ∀ l < 4, (carryU.reg (10 + k)).ok (carryB (10 + ·)) l = true ∧
    (carryU.reg (10 + k)).bnd (carryB (10 + ·)) l < 2 ^ 52 := by decide +kernel

theorem carryR_ok : ∀ k < 5, ∀ l < 4, (carryR.reg k).ok (carryB id) l = true ∧
    (carryR.reg k).bnd (carryB id) l < 2 ^ 52 := by decide +kernel

theorem carryU_keep : ∀ r < 16, ¬ ((5 ≤ r ∧ r < 7) ∨ 10 ≤ r) → carryU.reg r = .reg r := by decide +kernel
theorem carryR_keep : ∀ r < 16, ¬ (r < 7 ∨ r = 15) → carryR.reg r = .reg r := by decide +kernel

theorem carryU_st : carryU.st = [] := by decide +kernel
theorem carryR_st : carryR.st = [] := by decide +kernel

end VG.Proof.X25519.X86_64.Ifma
