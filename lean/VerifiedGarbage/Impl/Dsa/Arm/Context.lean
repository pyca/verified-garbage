module

public import VerifiedGarbage.Impl.Mont.Arm.Context
public import VerifiedGarbage.Impl.Dsa.HelperLayout

/-! # Shared Montgomery context setup for ARMv7 DSA

Setup leaves the result slot unused. Save r4–r10 and lr in its first 32
bytes (extending into the product slot for the smallest widths), so nested
calls preserve the arithmetic helpers' register saves in the header.
The caller keeps its workspace in r4 across the call; r11 stays untouched.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Context
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic

def regs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .lr]

def slots (n : Nat) : List (Reg × Nat) := regs.zipIdx.map fun (r, i) => (r, resS n + 4 * i)

def save (n : Nat) : List Instr :=
  .mov .r12 (.reg .r0) :: (slots n).map fun (r, o) => .str r .r12 o

def restore (n : Nat) : List Instr := (slots n).map fun (r, o) => .ldr r .r12 o

/-- Addition, subtraction and byte reduction do not use Montgomery R² or one.
Only establish the inverse required by the shared arithmetic invariant. -/
def light (n : Nat) : Prog isa := .block (setupInverse (modS n))

def body (n : Nat) : Prog isa :=
  .seq (.block (save n)) (.seq (contextSetup n) (.block (restore n)))

def scratch (n : Nat) : List (Nat × Nat) :=
  [(resS n, 32), (0, 4), (oneS n, 8 * n), (rrS n, 8 * n),
    (tmpS n, 8 * n), (accS n, 4 * (8 * n + 2))]

def layout (n : Nat) : Impl.Dsa.MontContext.Layout where
  n := n
  modulus := modS n
  inverse := invO
  one := oneS n
  rSquared := rrS n
  scratch := scratch n
  size := contextBytes n

def name (n : Nat) : String := s!"vg_dsa_context_{(layout n).n}"

def head (n : Nat) : List Instr :=
  [.mov .r4 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 (BitVec.ofNat 16 (contextBytes n / 8))]

def call (n : Nat) : Prog isa :=
  .seq (.block (head n)) (.seq (.call (name n) (body n)) (.block [.mov .r12 (.reg .r4)]))

end VG.Impl.Dsa.Arm.Context
