module

public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Spec.Dsa.ModPow

/-! # Shared DSA modular exponentiation on IA-32

The caller loads the modulus, base and exponent into the existing Montgomery
workspace. Each width has one callable setup-and-exponentiation body.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Pow
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def slots : List (Reg × Nat) := [(.ebx, 8), (.esi, 12), (.ebp, 16), (.edi, 20)]

def save : List Instr :=
  [.mov .eax (.mem (at_ .esp 4))] ++
    slots.map (fun (r, d) => .store (at_ .eax d) r) ++ [.mov .edi (.reg .eax)]

def restore : List Instr := slots.map fun (r, d) => .mov r (.mem (sc d))

def core (n e : Nat) : Prog isa := .seq (contextSetup n) (exponentiate n e)

def body (n e : Nat) : Prog isa :=
  .seq (.block save) (.seq (core n e) (.block restore))

def scratch (n : Nat) : List (Nat × Nat) := [(0, 64), (slot n 1, contextBytes n - slot n 1)]

def layout (n e : Nat) : Spec.Dsa.ModPow.Layout where
  n := n
  e := e
  modulus := slot n 0
  base := slot n 5
  exponent := slot n 8
  result := slot n 6
  scratch := scratch n
  size := contextBytes n

def name (n e : Nat) : String := (Spec.Dsa.ModPow.powApi (layout n e)).name

/-- Pass the workspace and its length using cdecl's two stack arguments. -/
def call (n e : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 (contextBytes n / 8)))])
    (.frame (.push [.eax, .edi]) (.call (name n e) (body n e)) (.pop .eax 2))

end VG.Impl.Dsa.X86.Pow
