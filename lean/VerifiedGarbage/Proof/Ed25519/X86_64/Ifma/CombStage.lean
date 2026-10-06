import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Setup
import VerifiedGarbage.Impl.Ed25519.X86_64.CombIfma

/-!
# Ed25519's comb with AVX512_IFMA: the blocks, run symbolically

The vector blocks of `Ifma.combMultiply` but X25519's products and carries and
the doublings' blocks, run symbolically (`Proof/X25519/X86_64/Ifma/Sym.lean`):
each output limb, lane by lane, as a number (`rfl`), and its bounds
(`decide`).
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Ifma
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord lanes)
open VG.Proof.X25519.X86_64.Ifma (Sym T Env Bnds symOf limbNat)

/-! ## The entry's limbs -/

def eloadS : Sym := symOf eload

/-- Word `k` of row `l` of the entry: `y - x`, `y + x` (each with `rax` or'd into its first
word), `2dt`, and the words of `2` at `K2`. -/
def erow (E : Env) (l k : Nat) : Nat :=
  match l with
  | 0 => E.v 11 k ||| (if k = 0 then E.g .rax else 0)
  | 1 => E.v 12 k ||| (if k = 0 then E.g .rax else 0)
  | 2 => E.v 13 k
  | _ => E.m K2 k

theorem eloadS_regs (E : Env) : ∀ j < 5, ∀ l < 4, (eloadS.reg (5 + j)).nat E l =
    limbNat (erow E l) (E.m KM l) j := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

def eloadB : Bnds :=
  ⟨fun _ => 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1, fun d => if d = KM then 2 ^ 51 - 1 else 2 ^ 64 - 1,
    fun _ => 0⟩

theorem eloadS_ok : ∀ j < 5, ∀ l < 4, (eloadS.reg (5 + j)).ok eloadB l = true ∧
    (eloadS.reg (5 + j)).bnd eloadB l < 2 ^ 52 := by
  decide +kernel

theorem eloadS_keep : ∀ r < 5, eloadS.reg r = .reg r := by decide +kernel
theorem eloadS_st : eloadS.st = [] := by decide +kernel

/-! ## The negation -/

def vnegS : Sym := symOf vneg

theorem vnegS_regs : ∀ j < 5, vnegS.reg (5 + j) = .xor (.reg (5 + j))
    (.and (.xor (.blend (.perm (.reg (5 + j)) (ord 1 0 2 3).toNat) (.sub (.ld (kb j)) (.reg (5 + j)))
      (lanes false false true false).toNat) (.reg (5 + j))) (.bc (.lane0 (.gpr .rcx)))) := by
  decide +kernel

theorem vnegS_keep : ∀ r < 5, vnegS.reg r = .reg r := by decide +kernel
theorem vnegS_st : vnegS.st = [] := by decide +kernel

/-! ## An addition's first operands -/

def vaddAS : Sym := symOf vaddA

/-- `(Y - X, Y + X, T, Z)`, limb `j`, from `(X, Y, Z, T)`. -/
def aNat (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 1 + (E.m (kb j) 0 - E.v j 0)
  | 1 => E.v j 1 + E.v j 0
  | 2 => E.v j 3 + 0
  | _ => E.v j 2 + 0

theorem vaddAS_nat (E : Env) : ∀ j < 5, ∀ l < 4, (vaddAS.reg j).nat E l = aNat E j l := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> rfl

/-- Bounds: the point's limbs below `2⁶¹`, and the bias. -/
def addB : Bnds :=
  ⟨fun i => if i < 5 then 2 ^ 61 - 1 else 2 ^ 64 - 1, fun _ => 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 2 ^ 64 - 1,
    fun d => if d = KB0 then 2 ^ 62 - 38912 else if d = KB1 then 2 ^ 62 - 2048 else 0⟩

theorem vaddAS_ok : ∀ j < 5, ∀ l < 4, (vaddAS.reg j).ok addB l = true ∧
    (vaddAS.reg j).bnd addB l < 2 ^ 63 := by
  decide +kernel

theorem vaddAS_keep : ∀ r < 16, 5 ≤ r → r < 10 ∨ 14 ≤ r → vaddAS.reg r = .reg r := by decide +kernel
theorem vaddAS_st : vaddAS.st = [] := by decide +kernel

def vstAS : Sym := symOf vstA

theorem vstAS_st : vstAS.st = [(OPL + 128, .reg 4), (OPL + 96, .reg 3), (OPL + 64, .reg 2),
    (OPL + 32, .reg 1), (OPL, .reg 0)] := by decide +kernel
theorem vstAS_keep : ∀ r < 16, vstAS.reg r = .reg r := by decide +kernel

/-! ## An addition's second operands -/

def vaddBS : Sym := symOf vaddB

/-- `(E, G, F, H) = (B - A, D + C, D - C, B + A)`, limb `j`, from `(A, B, C, D)`. -/
def wNat (E : Env) (j : Nat) : Nat → Nat
  | 0 => E.v j 1 + (E.m (kb j) 0 - E.v j 0)
  | 1 => E.v j 3 + E.v j 2
  | 2 => E.v j 3 + (E.m (kb j) 2 - E.v j 2)
  | _ => E.v j 1 + E.v j 0

/-- `(E, G, F, E)`. -/
def bOp1 (E : Env) (j : Nat) : Nat → Nat
  | 0 => wNat E j 0
  | 1 => wNat E j 1
  | 2 => wNat E j 2
  | _ => wNat E j 0

/-- `(F, H, G, H)`. -/
def bOp2 (E : Env) (j : Nat) : Nat → Nat
  | 0 => wNat E j 2
  | 1 => wNat E j 3
  | 2 => wNat E j 1
  | _ => wNat E j 3

theorem vaddBS_nat (E : Env) : ∀ j < 5, ∀ l < 4,
    (vaddBS.reg j).nat E l = bOp1 E j l ∧ (vaddBS.reg (5 + j)).nat E l = bOp2 E j l := by
  intro j hj l hl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;>
    rcases VG.X86_64.cases4 hl with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem vaddBS_ok : ∀ j < 5, ∀ l < 4, (vaddBS.reg j).ok addB l = true ∧
    (vaddBS.reg j).bnd addB l < 2 ^ 63 ∧ (vaddBS.reg (5 + j)).ok addB l = true ∧
    (vaddBS.reg (5 + j)).bnd addB l < 2 ^ 63 := by
  decide +kernel

theorem vaddBS_keep : ∀ r < 16, 14 ≤ r → vaddBS.reg r = .reg r := by decide +kernel
theorem vaddBS_st : vaddBS.st = [] := by decide +kernel

end VG.Proof.Ed25519.X86_64.Ifma
