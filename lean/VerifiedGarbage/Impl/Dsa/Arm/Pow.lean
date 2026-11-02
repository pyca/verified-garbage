module

public import VerifiedGarbage.Impl.Dsa.Arm.Context

/-! # DSA's exponentiation as a function on 32-bit ARM

`vg_dsa_pow_{n}_{e}` (`Proof/Dsa/ModPowContract.lean`) sets up the context of the
modulus in slot 0 of the working space and raises the base in slot 8 to the
exponent of `e` words in slot 11, into slot 9 (`contextSetup`,
`exponentiate`). The working space is in `r0`, which it keeps in `r12`; it
saves `r4`–`r11` and `lr` in the header, past `m'` and the mask, and
restores them on return.

A caller (`call`) keeps its working space's base, in `r12`, in `r11` across
the call, which leaves unknown values in `r12` and `lr` (`Arm.call`).
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Pow
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic

/-- The registers the function saves. -/
def savedRegs : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- Each saved register and its offset in the header, past `m'` and the mask. -/
def slots : List (Reg × Nat) := savedRegs.zipIdx.map fun (r, i) => (r, 8 + 4 * i)

def save : List Instr := .mov .r12 (.reg .r0) :: slots.map fun (r, o) => .str r .r12 o

def restore : List Instr := slots.map fun (r, o) => .ldr r .r12 o

def body (n e : Nat) : Prog isa :=
  .seq (.block save) (.seq (Context.call n) (.seq (exponentiate n e) (.block restore)))

/-- The function's own bytes: the header's first 64, and every slot but the
modulus's. -/
def scratch (n : Nat) : List (Nat × Nat) := [(0, 64), (slot n 1, contextBytes n - slot n 1)]

def layout (n e : Nat) : Impl.Dsa.ModPow.Layout where
  n := n
  e := e
  modulus := modS n
  base := baseS n
  exponent := expS n
  result := resS n
  scratch := scratch n
  size := contextBytes n

def name (n e : Nat) : String := s!"vg_dsa_pow_{(layout n e).n}_{(layout n e).e}"

/-- A call: the working space `r12` and its length, then `r12` back from `r11`. -/
def call (n e : Nat) : Prog isa :=
  .seq (.block [.mov .r11 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 (BitVec.ofNat 16 (contextBytes n / 8))])
    (.seq (.call (name n e) (body n e)) (.block [.mov .r12 (.reg .r11)]))

end VG.Impl.Dsa.Arm.Pow
